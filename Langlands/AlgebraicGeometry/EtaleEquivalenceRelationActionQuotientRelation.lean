import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationSchemeQuotientMap
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionMorphism

/-! # Quotient relations of actions of étale equivalence relations

Let `A` be an action of an étale equivalence relation `H` on `π : P ⟶ H.U`. The relation `H`
also acts diagonally on the scheme `P ×_{H.U} P` of pairs of points over the same point of
`H.U`. Given scheme quotients `Q` of the action relation of `A` and `Q₂` of the action relation
of the pair action, the two projections descend to morphisms `s, t : Q₂.M ⟶ Q.M`. When `π` is
étale they form an étale equivalence relation on `Q.M`, the quotient relation of `A`.

The file also records when the quotient relation is affine, separated, quasi-compact and of
finite type.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

/-- If arrows are determined by their endpoints, an arrow with prescribed endpoints exists as
soon as it exists after precomposition with an effective epimorphism. -/
lemma exists_of_exists_local {R U T T₁ : Scheme.{u}} {t s : R ⟶ U}
    (hom_ext : ∀ ⦃W : Scheme.{u}⦄ ⦃a b : W ⟶ R⦄, a ≫ t = b ≫ t → a ≫ s = b ≫ s → a = b)
    (e : T₁ ⟶ T) [EffectiveEpi e] (x y : T ⟶ U) (ρ : T₁ ⟶ R) (ht : ρ ≫ t = e ≫ x)
    (hs : ρ ≫ s = e ≫ y) : ∃ r : T ⟶ R, r ≫ t = x ∧ r ≫ s = y := by
  have hd : ∀ {W : Scheme.{u}} (g₁ g₂ : W ⟶ T₁), g₁ ≫ e = g₂ ≫ e → g₁ ≫ ρ = g₂ ≫ ρ := by
    intro W g₁ g₂ h
    apply hom_ext
    · rw [Category.assoc, Category.assoc, ht, reassoc_of% h]
    · rw [Category.assoc, Category.assoc, hs, reassoc_of% h]
  refine ⟨EffectiveEpi.desc e ρ hd, ?_, ?_⟩
  · rw [← cancel_epi e, ← Category.assoc, EffectiveEpi.fac, ht]
  · rw [← cancel_epi e, ← Category.assoc, EffectiveEpi.fac, hs]

/-- A morphism of étale equivalence relations given by isomorphisms commuting with both
projections is cartesian. -/
lemma isCartesianHom_of_isIso {E F : EtaleEquivalenceRelation.{u}} (α : E.U ⟶ F.U)
    (β : E.R ⟶ F.R) [IsIso α] [IsIso β] (ht : β ≫ F.t = E.t ≫ α) (hs : β ≫ F.s = E.s ≫ α) :
    IsCartesianHom E F α β :=
  ⟨ht, IsPullback.of_horiz_isIso ⟨hs⟩⟩

namespace Action

section Pair

variable {H : EtaleEquivalenceRelation.{u}} {P : Scheme.{u}} {π : P ⟶ H.U}

lemma pairFst_condition :
    pullback.fst H.s (pullback.fst π π ≫ π) ≫ H.s =
      (pullback.snd H.s (pullback.fst π π ≫ π) ≫ pullback.fst π π) ≫ π := by
  rw [Category.assoc]
  exact pullback.condition

lemma pairSnd_condition :
    pullback.fst H.s (pullback.fst π π ≫ π) ≫ H.s =
      (pullback.snd H.s (pullback.fst π π ≫ π) ≫ pullback.snd π π) ≫ π := by
  rw [Category.assoc, ← pullback.condition (f := π) (g := π)]
  exact pullback.condition

variable (A : Action H π)

/-- The diagonal action map on pairs of points of `P` over the same point of `H.U`. -/
noncomputable def pairMap : pullback H.s (pullback.fst π π ≫ π) ⟶ pullback π π :=
  pullback.lift
    (A.act (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst π π) pairFst_condition)
    (A.act (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd π π) pairSnd_condition)
    (by rw [act_over, act_over])

@[reassoc (attr := simp)]
lemma pairMap_fst : A.pairMap ≫ pullback.fst π π =
    A.act (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst π π) pairFst_condition :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pairMap_snd : A.pairMap ≫ pullback.snd π π =
    A.act (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd π π) pairSnd_condition :=
  pullback.lift_snd _ _ _

lemma lift_pairMap_fst {T : Scheme.{u}} (r : T ⟶ H.R) (v : T ⟶ pullback π π)
    (h : r ≫ H.s = v ≫ pullback.fst π π ≫ π) :
    pullback.lift r v h ≫ A.pairMap ≫ pullback.fst π π =
      A.act r (v ≫ pullback.fst π π) (by rw [Category.assoc]; exact h) := by
  rw [pairMap_fst, act_precomp]
  exact A.act_congr (pullback.lift_fst _ _ _) (by rw [pullback.lift_snd_assoc]) _ _

lemma lift_pairMap_snd {T : Scheme.{u}} (r : T ⟶ H.R) (v : T ⟶ pullback π π)
    (h : r ≫ H.s = v ≫ pullback.fst π π ≫ π) :
    pullback.lift r v h ≫ A.pairMap ≫ pullback.snd π π =
      A.act r (v ≫ pullback.snd π π)
        (by rw [Category.assoc, ← pullback.condition (f := π) (g := π)]; exact h) := by
  rw [pairMap_snd, act_precomp]
  exact A.act_congr (pullback.lift_fst _ _ _) (by rw [pullback.lift_snd_assoc]) _ _

/-- The diagonal action of `H` on pairs of points of `P` over the same point of `H.U`. -/
noncomputable def pairAction : Action H (pullback.fst π π ≫ π) := by
  refine ⟨A.pairMap, ?_, ?_, ?_⟩
  · rw [← Category.assoc, pairMap_fst, act_over]
  · apply pullback.hom_ext
    · rw [Category.assoc, lift_pairMap_fst]
      refine (A.act_congr (by rw [Category.assoc]) (Category.id_comp _) _ ?_).trans
        ((A.act_unit _).trans (Category.id_comp _).symm)
      simp
    · rw [Category.assoc, lift_pairMap_snd]
      refine (A.act_congr (by rw [Category.assoc, pullback.condition_assoc (f := π) (g := π)])
        (Category.id_comp _) _ ?_).trans ((A.act_unit _).trans (Category.id_comp _).symm)
      simp
  · intro T r q v hrq hqv
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [lift_pairMap_fst, lift_pairMap_fst]
      refine (A.act_congr rfl (by rw [Category.assoc, lift_pairMap_fst]) _ ?_).trans
        (A.act_assoc r q _ hrq _)
      rw [act_over]
      exact hrq
    · simp only [Category.assoc]
      rw [lift_pairMap_snd, lift_pairMap_snd]
      refine (A.act_congr rfl (by rw [Category.assoc, lift_pairMap_snd]) _ ?_).trans
        (A.act_assoc r q _ hrq _)
      rw [act_over]
      exact hrq

@[simp]
lemma pairAction_map : A.pairAction.map = A.pairMap := rfl

/-- The first projection is equivariant from the pair action to the action. -/
lemma isEquivariant_pairFst :
    IsEquivariant (isCartesianHom_id H) (pullback.fst π π ≫ π) π (pullback.fst π π)
      (Category.comp_id _) A.pairAction A := by
  change A.pairMap ≫ _ = _
  rw [pairMap_fst]
  dsimp only [act]
  congr 1

/-- The second projection is equivariant from the pair action to the action. -/
lemma isEquivariant_pairSnd :
    IsEquivariant (isCartesianHom_id H) (pullback.fst π π ≫ π) π (pullback.snd π π)
      (by rw [Category.comp_id, pullback.condition]) A.pairAction A := by
  change A.pairMap ≫ _ = _
  rw [pairMap_snd]
  dsimp only [act]
  congr 1

/-- The diagonal is equivariant from the action to the pair action. -/
lemma isEquivariant_diagonal :
    IsEquivariant (isCartesianHom_id H) π (pullback.fst π π ≫ π) (pullback.diagonal π)
      (by simp) A A.pairAction := by
  change A.map ≫ _ = _ ≫ A.pairMap
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id, Category.assoc, pairMap_fst,
      act_precomp]
    refine Eq.trans ?_ (A.act_congr (by simp) (by simp) pullback.condition _)
    simp only [act, pullback.lift_fst_snd, Category.id_comp]
  · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, Category.assoc, pairMap_snd,
      act_precomp]
    refine Eq.trans ?_ (A.act_congr (by simp) (by simp) pullback.condition _)
    simp only [act, pullback.lift_fst_snd, Category.id_comp]

/-- The exchange of the two factors of `P ×_{H.U} P`. -/
noncomputable def pairSwap : pullback π π ⟶ pullback π π :=
  pullback.lift (pullback.snd π π) (pullback.fst π π) pullback.condition.symm

@[reassoc (attr := simp)]
lemma pairSwap_fst : pairSwap ≫ pullback.fst π π = pullback.snd π π :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pairSwap_snd : pairSwap ≫ pullback.snd π π = pullback.fst π π :=
  pullback.lift_snd _ _ _

/-- The exchange of factors is equivariant for the pair action. -/
lemma isEquivariant_pairSwap :
    IsEquivariant (isCartesianHom_id H) (pullback.fst π π ≫ π) (pullback.fst π π ≫ π) pairSwap
      (by rw [Category.comp_id, pairSwap_fst_assoc, pullback.condition]) A.pairAction
      A.pairAction := by
  change A.pairMap ≫ _ = _ ≫ A.pairMap
  apply pullback.hom_ext
  · rw [Category.assoc, pairSwap_fst, pairMap_snd, Category.assoc, pairMap_fst, act_precomp]
    exact A.act_congr (by simp) (by simp) _ _
  · rw [Category.assoc, pairSwap_snd, pairMap_fst, Category.assoc, pairMap_snd, act_precomp]
    exact A.act_congr (by simp) (by simp) _ _

lemma isCartesianHom_pairFst :
    IsCartesianHom A.pairAction.relation A.relation (pullback.fst π π)
      (arrowMap (isCartesianHom_id H) _ π (pullback.fst π π) (Category.comp_id _)) :=
  isCartesianHom_of_isEquivariant _ _ _ _ _ _ _ A.isEquivariant_pairFst

lemma isCartesianHom_pairSnd :
    IsCartesianHom A.pairAction.relation A.relation (pullback.snd π π)
      (arrowMap (isCartesianHom_id H) _ π (pullback.snd π π)
        (by rw [Category.comp_id, pullback.condition])) :=
  isCartesianHom_of_isEquivariant _ _ _ _ _ _ _ A.isEquivariant_pairSnd

lemma isCartesianHom_diagonal :
    IsCartesianHom A.relation A.pairAction.relation (pullback.diagonal π)
      (arrowMap (isCartesianHom_id H) π _ (pullback.diagonal π) (by simp)) :=
  isCartesianHom_of_isEquivariant _ _ _ _ _ _ _ A.isEquivariant_diagonal

lemma isCartesianHom_pairSwap :
    IsCartesianHom A.pairAction.relation A.pairAction.relation pairSwap
      (arrowMap (isCartesianHom_id H) _ _ pairSwap
        (by rw [Category.comp_id, pairSwap_fst_assoc, pullback.condition])) :=
  isCartesianHom_of_isEquivariant _ _ _ _ _ _ _ A.isEquivariant_pairSwap

/-- The action is free: two points with the same image in a quotient of the action relation
and the same image in `H.U` are equal. -/
lemma eq_of_comp_q_eq (Q : A.relation.SchemeQuotient) {T : Scheme.{u}} {b₁ b₂ : T ⟶ P}
    (hq : b₁ ≫ Q.q = b₂ ≫ Q.q) (hπ : b₁ ≫ π = b₂ ≫ π) : b₁ = b₂ := by
  obtain ⟨ρ, hρt, hρs⟩ : ∃ ρ, ρ ≫ A.relation.t = b₁ ∧ ρ ≫ A.relation.s = b₂ :=
    ⟨_, Q.isPullback.lift_fst _ _ hq, Q.isPullback.lift_snd _ _ hq⟩
  change ρ ≫ A.map = b₁ at hρt
  change ρ ≫ pullback.snd H.s π = b₂ at hρs
  have hunit : ρ ≫ pullback.fst H.s π = b₂ ≫ π ≫ H.unit := by
    apply H.hom_ext
    · rw [Category.assoc, ← A.over, ← Category.assoc, hρt, Category.assoc, Category.assoc,
        unit_t, Category.comp_id, hπ]
    · rw [Category.assoc, pullback.condition, ← Category.assoc, hρs, Category.assoc,
        Category.assoc, unit_s, Category.comp_id]
  rw [← hρt, ← A.act_arrow ρ]
  exact (A.act_congr hunit hρs _ _).trans (A.act_unit b₂)

end Pair

section QuotientRelation

variable {H : EtaleEquivalenceRelation.{u}} {P : Scheme.{u}} {π : P ⟶ H.U} (A : Action H π)
  (Q : A.relation.SchemeQuotient) (Q₂ : A.pairAction.relation.SchemeQuotient)

/-- The source map of the quotient relation, induced by the first projection. -/
noncomputable def quotientS : Q₂.M ⟶ Q.M :=
  SchemeQuotient.map A.isCartesianHom_pairFst Q₂ Q

/-- The target map of the quotient relation, induced by the second projection. -/
noncomputable def quotientT : Q₂.M ⟶ Q.M :=
  SchemeQuotient.map A.isCartesianHom_pairSnd Q₂ Q

@[reassoc (attr := simp)]
lemma q_quotientS : Q₂.q ≫ A.quotientS Q Q₂ = pullback.fst π π ≫ Q.q :=
  SchemeQuotient.q_map _ _ _

@[reassoc (attr := simp)]
lemma q_quotientT : Q₂.q ≫ A.quotientT Q Q₂ = pullback.snd π π ≫ Q.q :=
  SchemeQuotient.q_map _ _ _

lemma isPullback_quotientS :
    IsPullback (pullback.fst π π) Q₂.q Q.q (A.quotientS Q Q₂) :=
  SchemeQuotient.isPullback_map A.isCartesianHom_pairFst Q₂ Q

lemma isPullback_quotientT :
    IsPullback (pullback.snd π π) Q₂.q Q.q (A.quotientT Q Q₂) :=
  SchemeQuotient.isPullback_map A.isCartesianHom_pairSnd Q₂ Q

/-- Points of the quotient of pairs are determined by their two images in the quotient. -/
lemma quotient_hom_ext {T : Scheme.{u}} {x y : T ⟶ Q₂.M}
    (ht : x ≫ A.quotientT Q Q₂ = y ≫ A.quotientT Q Q₂)
    (hs : x ≫ A.quotientS Q Q₂ = y ≫ A.quotientS Q Q₂) : x = y := by
  let e : pullback x Q₂.q ⟶ T := pullback.fst x Q₂.q
  let x' : pullback x Q₂.q ⟶ pullback π π := pullback.snd x Q₂.q
  have hx' : x' ≫ Q₂.q = e ≫ x := pullback.condition.symm
  have he : Epi e := by
    dsimp only [e]
    infer_instance
  clear_value e x'
  have hy : (x' ≫ pullback.fst π π) ≫ Q.q = (e ≫ y) ≫ A.quotientS Q Q₂ := by
    simp only [Category.assoc]
    rw [← q_quotientS, reassoc_of% hx', hs]
  let y' := (A.isPullback_quotientS Q Q₂).lift _ _ hy
  have hy'₁ : y' ≫ pullback.fst π π = x' ≫ pullback.fst π π :=
    (A.isPullback_quotientS Q Q₂).lift_fst _ _ _
  have hy'₂ : y' ≫ Q₂.q = e ≫ y := (A.isPullback_quotientS Q Q₂).lift_snd _ _ _
  clear_value y'
  have hxy : x' = y' := by
    apply pullback.hom_ext
    · exact hy'₁.symm
    · apply A.eq_of_comp_q_eq Q
      · simp only [Category.assoc]
        rw [← q_quotientT, reassoc_of% hx', reassoc_of% hy'₂, ht]
      · simp only [Category.assoc]
        rw [← pullback.condition (f := π) (g := π), reassoc_of% hy'₁]
  have : e ≫ x = e ≫ y := by rw [← hx', ← hy'₂, hxy]
  exact (cancel_epi e).1 this

/-- The diagonal of the quotient. -/
noncomputable def quotientDiagonal : Q.M ⟶ Q₂.M :=
  SchemeQuotient.map A.isCartesianHom_diagonal Q Q₂

@[reassoc (attr := simp)]
lemma quotientDiagonal_s : A.quotientDiagonal Q Q₂ ≫ A.quotientS Q Q₂ = 𝟙 Q.M := by
  apply Q.hom_ext
  rw [quotientDiagonal, SchemeQuotient.q_map_assoc, q_quotientS, pullback.diagonal_fst_assoc,
    Category.comp_id]

@[reassoc (attr := simp)]
lemma quotientDiagonal_t : A.quotientDiagonal Q Q₂ ≫ A.quotientT Q Q₂ = 𝟙 Q.M := by
  apply Q.hom_ext
  rw [quotientDiagonal, SchemeQuotient.q_map_assoc, q_quotientT, pullback.diagonal_snd_assoc,
    Category.comp_id]

/-- The exchange of the two factors on the quotient of pairs. -/
noncomputable def quotientSwap : Q₂.M ⟶ Q₂.M :=
  SchemeQuotient.map A.isCartesianHom_pairSwap Q₂ Q₂

@[reassoc (attr := simp)]
lemma quotientSwap_s : A.quotientSwap Q₂ ≫ A.quotientS Q Q₂ = A.quotientT Q Q₂ := by
  apply Q₂.hom_ext
  rw [quotientSwap, SchemeQuotient.q_map_assoc, q_quotientS, pairSwap_fst_assoc, q_quotientT]

@[reassoc (attr := simp)]
lemma quotientSwap_t : A.quotientSwap Q₂ ≫ A.quotientT Q Q₂ = A.quotientS Q Q₂ := by
  apply Q₂.hom_ext
  rw [quotientSwap, SchemeQuotient.q_map_assoc, q_quotientT, pairSwap_snd_assoc, q_quotientS]

/-- Transitivity of the quotient relation. -/
lemma quotient_trans {T : Scheme.{u}} (r r' : T ⟶ Q₂.M)
    (h : r ≫ A.quotientS Q Q₂ = r' ≫ A.quotientT Q Q₂) :
    ∃ r'' : T ⟶ Q₂.M, r'' ≫ A.quotientT Q Q₂ = r ≫ A.quotientT Q Q₂ ∧
      r'' ≫ A.quotientS Q Q₂ = r' ≫ A.quotientS Q Q₂ := by
  let e : pullback r Q₂.q ⟶ T := pullback.fst r Q₂.q
  let x' : pullback r Q₂.q ⟶ pullback π π := pullback.snd r Q₂.q
  have hx' : x' ≫ Q₂.q = e ≫ r := pullback.condition.symm
  have he : EffectiveEpi e := by
    dsimp only [e]
    infer_instance
  clear_value e x'
  have hy : (x' ≫ pullback.fst π π) ≫ Q.q = (e ≫ r') ≫ A.quotientT Q Q₂ := by
    simp only [Category.assoc]
    rw [← q_quotientS, reassoc_of% hx', h]
  let y' := (A.isPullback_quotientT Q Q₂).lift _ _ hy
  have hy'₁ : y' ≫ pullback.snd π π = x' ≫ pullback.fst π π :=
    (A.isPullback_quotientT Q Q₂).lift_fst _ _ _
  have hy'₂ : y' ≫ Q₂.q = e ≫ r' := (A.isPullback_quotientT Q Q₂).lift_snd _ _ _
  clear_value y'
  let z : pullback r Q₂.q ⟶ pullback π π :=
    pullback.lift (y' ≫ pullback.fst π π) (x' ≫ pullback.snd π π) (by
      simp only [Category.assoc]
      calc y' ≫ pullback.fst π π ≫ π = y' ≫ pullback.snd π π ≫ π :=
            congrArg (y' ≫ ·) pullback.condition
        _ = x' ≫ pullback.fst π π ≫ π := by rw [reassoc_of% hy'₁]
        _ = x' ≫ pullback.snd π π ≫ π := congrArg (x' ≫ ·) pullback.condition)
  apply exists_of_exists_local (fun W a b => A.quotient_hom_ext Q Q₂) e _ _ (z ≫ Q₂.q)
  · rw [Category.assoc, q_quotientT, pullback.lift_snd_assoc, Category.assoc, ← q_quotientT,
      reassoc_of% hx']
  · rw [Category.assoc, q_quotientS, pullback.lift_fst_assoc, Category.assoc, ← q_quotientS,
      reassoc_of% hy'₂]

/-- The quotient relation of an action with étale structure map: the relation on the quotient
of the action relation whose arrows are the classes of pairs of points over the same point. -/
noncomputable def quotientRelation [Etale π] : EtaleEquivalenceRelation.{u} where
  U := Q.M
  R := Q₂.M
  t := A.quotientT Q Q₂
  s := A.quotientS Q Q₂
  mono_lift := by
    constructor
    intro T x y h
    apply A.quotient_hom_ext Q Q₂
    · simpa using congrArg (· ≫ prod.fst) h
    · simpa using congrArg (· ≫ prod.snd) h
  refl := by
    intro T a
    exact ⟨a ≫ A.quotientDiagonal Q Q₂, by simp, by simp⟩
  symm := by
    intro T r
    exact ⟨r ≫ A.quotientSwap Q₂, by simp, by simp⟩
  trans := by
    intro T r r' h
    exact A.quotient_trans Q Q₂ r r' h
  etale_t := by
    have : IsZariskiLocalAtTarget @Etale.{u} := HasRingHomProperty.instIsZariskiLocalAtTarget _
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale)
      (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) (A.isPullback_quotientT Q Q₂)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ (inferInstanceAs (Etale (pullback.snd π π)))
  etale_s := by
    have : IsZariskiLocalAtTarget @Etale.{u} := HasRingHomProperty.instIsZariskiLocalAtTarget _
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale)
      (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) (A.isPullback_quotientS Q Q₂)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ (inferInstanceAs (Etale (pullback.fst π π)))

section

variable [Etale π]

@[simp]
lemma quotientRelation_s : (A.quotientRelation Q Q₂).s = A.quotientS Q Q₂ := rfl

@[simp]
lemma quotientRelation_t : (A.quotientRelation Q Q₂).t = A.quotientT Q Q₂ := rfl

end

/-- Characterization of the source map of the quotient relation. -/
lemma quotientS_eq {s' : Q₂.M ⟶ Q.M} (h : Q₂.q ≫ s' = pullback.fst π π ≫ Q.q) :
    A.quotientS Q Q₂ = s' :=
  Q₂.hom_ext (by rw [q_quotientS, h])

/-- Characterization of the target map of the quotient relation. -/
lemma quotientT_eq {t' : Q₂.M ⟶ Q.M} (h : Q₂.q ≫ t' = pullback.snd π π ≫ Q.q) :
    A.quotientT Q Q₂ = t' :=
  Q₂.hom_ext (by rw [q_quotientT, h])

section Finiteness

/-- The quotient map of pairs is affine if the quotient map of points is. -/
lemma isAffineHom_q₂ [IsAffineHom Q.q] : IsAffineHom Q₂.q :=
  SchemeQuotient.isAffineHom_q A.isCartesianHom_pairFst Q₂ Q

lemma isAffineHom_quotientS [IsAffineHom π] [IsAffineHom Q.q] :
    IsAffineHom (A.quotientS Q Q₂) :=
  have : IsAffineHom (pullback.fst π π) := MorphismProperty.pullback_fst _ _ ‹_›
  SchemeQuotient.isAffineHom_map A.isCartesianHom_pairFst Q₂ Q

lemma isAffineHom_quotientT [IsAffineHom π] [IsAffineHom Q.q] :
    IsAffineHom (A.quotientT Q Q₂) :=
  have : IsAffineHom (pullback.snd π π) := MorphismProperty.pullback_snd _ _ ‹_›
  SchemeQuotient.isAffineHom_map A.isCartesianHom_pairSnd Q₂ Q

variable [Etale π]

lemma isSeparated_quotientRelation_s [IsAffineHom π] [IsAffineHom Q.q] :
    IsSeparated (A.quotientRelation Q Q₂).s :=
  have := A.isAffineHom_quotientS Q Q₂
  inferInstanceAs (IsSeparated (A.quotientS Q Q₂))

lemma compactSpace_quotientRelation_U [CompactSpace P] :
    CompactSpace (A.quotientRelation Q Q₂).U :=
  have : CompactSpace A.relation.U := inferInstanceAs (CompactSpace P)
  SchemeQuotient.compactSpace Q

lemma locallyOfFiniteType_quotientRelation_U [LocallyOfFiniteType (terminal.from P)] :
    LocallyOfFiniteType (terminal.from (A.quotientRelation Q Q₂).U) :=
  have : LocallyOfFiniteType (terminal.from A.relation.U) :=
    inferInstanceAs (LocallyOfFiniteType (terminal.from P))
  SchemeQuotient.locallyOfFiniteType_terminal Q

lemma compactSpace_quotientRelation_R [CompactSpace P] [QuasiCompact π] :
    CompactSpace (A.quotientRelation Q Q₂).R :=
  have : CompactSpace A.pairAction.relation.U :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst π π)
  SchemeQuotient.compactSpace Q₂

lemma quasiSeparatedSpace_quotientRelation_R [IsAffineHom Q.q]
    [QuasiSeparatedSpace (pullback π π : Scheme.{u})] :
    QuasiSeparatedSpace (A.quotientRelation Q Q₂).R :=
  have := A.isAffineHom_q₂ Q Q₂
  have : QuasiSeparatedSpace A.pairAction.relation.U :=
    inferInstanceAs (QuasiSeparatedSpace (pullback π π : Scheme.{u}))
  SchemeQuotient.quasiSeparatedSpace Q₂

end Finiteness

end QuotientRelation

end Action

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
