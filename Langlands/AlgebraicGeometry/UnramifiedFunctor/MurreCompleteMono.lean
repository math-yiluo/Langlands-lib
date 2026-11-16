import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteChart
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteSeparated
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCharts

/-! # The closed-fibre charts are monomorphisms

For Step 2a of Murre's induction (Bourbaki exp. 294): `ξ_y : Spec B_y → F` is a monomorphism.
Two points of `Spec B_y` with the same image in `F` are compared in `Spec B_y ×_S Spec B_y`; over
the closed point the stalks of the `Y k` separate them, and elsewhere a discrete valuation ring
specializing to the closed fibre and condition (F6) do. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace CompleteLocal

open Charts

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

section Generic

/-- (F1b) gives injectivity of restriction along flat surjective quasi-compact morphisms. -/
lemma map_injective_of_flat (hF : FaithfullyFlatSheaf F) {T₁ T₂ : Over (Spec R)} (z : T₁ ⟶ T₂)
    [Flat z.left] [Surjective z.left] [QuasiCompact z.left] :
    Function.Injective (F.map z.op) := fun _ _ hab ↦
  (hF z inferInstance inferInstance inferInstance).isSeparatedFor.ext fun _ _ hg ↦ by
    cases hg
    exact hab

variable (U : Over (Spec R)) (ξ : F.obj (op U))

/-- The two elements of `F(T)` given by `β : T ⟶ U ×_S U` followed by the projections agree. -/
def AgreeAlong {T : Over (Spec R)} (β : T.left ⟶ pullback U.hom U.hom)
    (hβ : β ≫ pullback.fst U.hom U.hom ≫ U.hom = T.hom) : Prop :=
  F.map (Over.homMk (β ≫ pullback.fst U.hom U.hom) (by rw [Category.assoc]; exact hβ) :
      T ⟶ U).op ξ =
    F.map (Over.homMk (β ≫ pullback.snd U.hom U.hom)
      (by rw [Category.assoc, ← pullback.condition]; exact hβ) : T ⟶ U).op ξ

variable {U ξ}

lemma agreeAlong_congr {T : Over (Spec R)} {β β' : T.left ⟶ pullback U.hom U.hom} (h : β = β')
    (hβ : β ≫ pullback.fst U.hom U.hom ≫ U.hom = T.hom)
    (hβ' : β' ≫ pullback.fst U.hom U.hom ≫ U.hom = T.hom) :
    AgreeAlong U ξ β hβ ↔ AgreeAlong U ξ β' hβ' := by
  subst h; rfl

lemma agreeAlong_comp {T T' : Over (Spec R)} {β : T.left ⟶ pullback U.hom U.hom}
    {hβ : β ≫ pullback.fst U.hom U.hom ≫ U.hom = T.hom} (h : AgreeAlong U ξ β hβ)
    (γ : T' ⟶ T) :
    AgreeAlong U ξ (γ.left ≫ β) (by rw [Category.assoc, hβ]; exact Over.w γ) := by
  have e₁ : (Over.homMk (γ.left ≫ β ≫ pullback.fst U.hom U.hom) (by
      rw [Category.assoc, Category.assoc, hβ]; exact Over.w γ) : T' ⟶ U) =
        γ ≫ Over.homMk (β ≫ pullback.fst U.hom U.hom) (by rw [Category.assoc]; exact hβ) := by
    ext1; simp
  have e₂ : (Over.homMk (γ.left ≫ β ≫ pullback.snd U.hom U.hom) (by
      rw [Category.assoc, Category.assoc, ← pullback.condition, hβ]; exact Over.w γ) :
        T' ⟶ U) = γ ≫ Over.homMk (β ≫ pullback.snd U.hom U.hom)
          (by rw [Category.assoc, ← pullback.condition]; exact hβ) := by
    ext1; simp
  unfold AgreeAlong at h ⊢
  simp only [Category.assoc] at e₁ e₂ ⊢
  rw [e₁, e₂]
  simp only [op_comp, Functor.map_comp_apply]
  rw [h]

lemma agreeAlong_of_comp (hF : FaithfullyFlatSheaf F) {T T' : Over (Spec R)}
    {β : T.left ⟶ pullback U.hom U.hom} (hβ : β ≫ pullback.fst U.hom U.hom ≫ U.hom = T.hom)
    (γ : T' ⟶ T) [Flat γ.left] [Surjective γ.left] [QuasiCompact γ.left]
    (h : AgreeAlong U ξ (γ.left ≫ β) (by rw [Category.assoc, hβ]; exact Over.w γ)) :
    AgreeAlong U ξ β hβ := by
  apply map_injective_of_flat hF γ
  have e₁ : (Over.homMk (γ.left ≫ β ≫ pullback.fst U.hom U.hom) (by
      rw [Category.assoc, Category.assoc, hβ]; exact Over.w γ) : T' ⟶ U) =
        γ ≫ Over.homMk (β ≫ pullback.fst U.hom U.hom) (by rw [Category.assoc]; exact hβ) := by
    ext1; simp
  have e₂ : (Over.homMk (γ.left ≫ β ≫ pullback.snd U.hom U.hom) (by
      rw [Category.assoc, Category.assoc, ← pullback.condition, hβ]; exact Over.w γ) :
        T' ⟶ U) = γ ≫ Over.homMk (β ≫ pullback.snd U.hom U.hom)
          (by rw [Category.assoc, ← pullback.condition]; exact hβ) := by
    ext1; simp
  unfold AgreeAlong at h
  simp only [Category.assoc] at e₁ e₂ h
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, ← e₁, ← e₂]
  exact h

variable (U ξ)

/-- Agreement at a point `a` of `U ×_S U`: along `Spec κ(a) ⟶ U ×_S U`. -/
def AgreeAtPt (a : ↥(pullback U.hom U.hom)) : Prop :=
  AgreeAlong U ξ (T := Over.mk ((pullback U.hom U.hom).fromSpecResidueField a ≫
    pullback.fst U.hom U.hom ≫ U.hom)) ((pullback U.hom U.hom).fromSpecResidueField a) rfl

variable {U ξ}

lemma agreeAlong_of_agreeAt {L : Type u} [Field L] (f : Spec (CommRingCat.of L) ⟶ Spec R)
    (β : Spec (CommRingCat.of L) ⟶ pullback U.hom U.hom)
    (hβ : β ≫ pullback.fst U.hom U.hom ≫ U.hom = f) (h : AgreeAtPt U ξ (β (closedPoint L))) :
    AgreeAlong U ξ (T := Over.mk f) β hβ := by
  have e := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField L _ β
  let γ : Over.mk f ⟶ Over.mk ((pullback U.hom U.hom).fromSpecResidueField (β (closedPoint L)) ≫
      pullback.fst U.hom U.hom ≫ U.hom) :=
    Over.homMk (Spec.map ((pullback U.hom U.hom).descResidueField
      (Scheme.stalkClosedPointTo β))) (by
        change _ ≫ _ ≫ _ ≫ _ = f
        rw [← Category.assoc, e, hβ])
  have := agreeAlong_comp h γ
  exact (agreeAlong_congr e _ _).1 this

lemma agreeAt_of_agreeAlong (hF : FaithfullyFlatSheaf F) {L : Type u} [Field L]
    (f : Spec (CommRingCat.of L) ⟶ Spec R) (β : Spec (CommRingCat.of L) ⟶ pullback U.hom U.hom)
    (hβ : β ≫ pullback.fst U.hom U.hom ≫ U.hom = f) (h : AgreeAlong U ξ (T := Over.mk f) β hβ) :
    AgreeAtPt U ξ (β (closedPoint L)) := by
  have e := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField L _ β
  let γ : Over.mk f ⟶ Over.mk ((pullback U.hom U.hom).fromSpecResidueField (β (closedPoint L)) ≫
      pullback.fst U.hom U.hom ≫ U.hom) :=
    Over.homMk (Spec.map ((pullback U.hom U.hom).descResidueField
      (Scheme.stalkClosedPointTo β))) (by
        change _ ≫ _ ≫ _ ≫ _ = f
        rw [← Category.assoc, e, hβ])
  have : Flat γ.left := flat_specMap_of_isField (Field.toIsField _) _
  have : Surjective γ.left :=
    surjective_specMap_of_isField (Field.toIsField _) (Field.toIsField L) _
  have : QuasiCompact γ.left := inferInstanceAs (QuasiCompact (Spec.map _))
  apply agreeAlong_of_comp hF rfl γ
  exact (agreeAlong_congr e.symm _ _).1 h

end Generic

section Chart

variable [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
  {Y : ℕ → Scheme.{u}} {q : ∀ k, Y k ⟶ Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (k + 1)))}
  (e : ∀ k, (baseChange (maximalIdealPowQuotientMap R k) F).RepresentableBy (Over.mk (q k)))
  [hfu : ∀ k, FormallyUnramified (q k)] [hlft : ∀ k, LocallyOfFiniteType (q k)]
  (hF3 : AdicLimits F) (y : Y 0)

/-- The chart `Spec B_y` as an object over `Spec R`. -/
abbrev chartU : Over (Spec R) := ovR R (ChartRing e y)

/-- `Spec B_y ×_S Spec B_y`. -/
abbrev chartP : Scheme.{u} := pullback (chartU e y).hom (chartU e y).hom

/-- The first projection of `chartP`. -/
abbrev chartFst : chartP e y ⟶ (chartU e y).left := pullback.fst _ _

/-- The second projection of `chartP`. -/
abbrev chartSnd : chartP e y ⟶ (chartU e y).left := pullback.snd _ _

include hfu hlft in
/-- Two `S`-morphisms from the spectrum of a field lying over the closed point to `Spec B_y`
with the same image in `F` are equal. -/
lemma chart_eq_of_closed {L : CommRingCat.{u}} (hL : IsField L) (f : Spec L ⟶ Spec R)
    (hf : ∀ x, f x = closedPoint R) (g₁ g₂ : Over.mk f ⟶ ovR R (ChartRing e y))
    (h : F.map g₁.op (chartElem e hF3 y) = F.map g₂.op (chartElem e hF3 y)) : g₁ = g₂ := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  let : Algebra R L := φ.hom.toAlgebra
  have := hL.isDomain
  have hA : ∀ r ∈ maximalIdeal R ^ (0 + 1), algebraMap R L r = 0 := by
    intro r hr
    rw [zero_add, pow_one] at hr
    let x : Spec L := ⟨⊥, inferInstance⟩
    have hx := congrArg PrimeSpectrum.asIdeal (hf x)
    change Ideal.comap φ.hom ⊥ = maximalIdeal R at hx
    rw [← hx, Ideal.mem_comap, Ideal.mem_bot] at hr
    exact hr
  obtain ⟨ψ₁, rfl⟩ := exists_homR (T' := L) g₁
  obtain ⟨ψ₂, rfl⟩ := exists_homR (T' := L) g₂
  rw [chart_inj_level e hF3 y 0 hA h]

include hfu hlft in
/-- A point of `Spec B_y ×_S Spec B_y` over the closed point, at which the two pullbacks of
`ξ_y` agree, lies on the diagonal. -/
lemma chart_mem_range_of_closed (a : ↥(chartP e y)) (ha : AgreeAtPt (chartU e y) (chartElem e hF3 y) a)
    (hs : (chartFst e y ≫ (chartU e y).hom) a = closedPoint R) :
    a ∈ Set.range (pullback.diagonal (chartU e y).hom) := by
  have hg := chart_eq_of_closed e hF3 y (Field.toIsField _)
    (Scheme.fromSpecResidueField (chartP e y) a ≫ (chartFst e y) ≫ (chartU e y).hom)
    (fun x ↦ (congrArg (fun p ↦ (chartFst e y ≫ (chartU e y).hom) p)
      (Scheme.fromSpecResidueField_apply (X := chartP e y) a x)).trans hs)
    (Over.homMk (Scheme.fromSpecResidueField (chartP e y) a ≫ chartFst e y) (by rw [Category.assoc]; rfl))
    (Over.homMk (Scheme.fromSpecResidueField (chartP e y) a ≫ chartSnd e y)
      (by rw [Category.assoc, ← pullback.condition]; rfl))
    (by unfold AgreeAtPt AgreeAlong at ha; exact ha)
  have hk := congrArg CommaMorphism.left hg
  have := lift_mem_range_diagonal (chartU e y).hom (chartFst e y) (chartSnd e y) pullback.condition _ hk (closedPoint _)
  rw [pullback.lift_fst_snd] at this
  change Scheme.fromSpecResidueField (chartP e y) a (closedPoint _) ∈ _ at this
  have h1 : Scheme.fromSpecResidueField (chartP e y) a
      (closedPoint ((chartP e y).residueField a)) = a := Scheme.fromSpecResidueField_apply _ _
  exact h1 ▸ this

instance : IsAffine (chartU e y).left := inferInstanceAs (IsAffine (Spec _))

instance : FormallyUnramified (chartU e y).hom := formallyUnramified_ovR _

instance : LocallyOfFiniteType (chartU e y).hom := locallyOfFiniteType_ovR _

instance : IsAffine (chartP e y) := inferInstanceAs (IsAffine (pullback _ _))

include hfu hlft in
lemma chartU_isFinite : IsFinite (chartU e y).hom := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing e y))))
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.2 inferInstance

include hfu hlft in
/-- Every point of `Spec B_y ×_S Spec B_y` at which the two pullbacks of `ξ_y` agree lies on
the diagonal. Away from the closed fibre, a discrete valuation ring specializes the point to the
closed fibre, and (F6) carries the agreement along it. -/
lemma chart_mem_range (hF6 : ValuativeSeparation F) (a : ↥(chartP e y))
    (ha : AgreeAtPt (chartU e y) (chartElem e hF3 y) a) :
    a ∈ Set.range (pullback.diagonal (chartU e y).hom) := by
  by_cases hs : (chartFst e y ≫ (chartU e y).hom) a = closedPoint R
  · exact chart_mem_range_of_closed e hF3 y a ha hs
  have : IsFinite (chartU e y).hom := chartU_isFinite e y
  have : IsLocallyNoetherian (chartP e y) :=
    LocallyOfFiniteType.isLocallyNoetherian (chartFst e y ≫ (chartU e y).hom)
  have : IsNoetherianRing Γ(chartP e y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  obtain ⟨b, hb, hbc⟩ := (isClosed_closure (s := ({a} : Set (chartP e y)))).exists_closed_singleton
    ⟨a, subset_closure rfl⟩
  have hab : a ⤳ b := specializes_iff_mem_closure.2 hb
  have hbs : (chartFst e y ≫ (chartU e y).hom) b = closedPoint R := by
    have hc : IsClosed {(chartFst e y ≫ (chartU e y).hom) b} := by
      have := (chartFst e y ≫ (chartU e y).hom).isClosedMap _ hbc
      rwa [Set.image_singleton] at this
    have hmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).1 hc
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)
  have hne : a ≠ b := fun h ↦ hs (h ▸ hbs)
  obtain ⟨V, _, _, _, n, hnc, hng⟩ := exists_dvr_spec hab hne
  -- agreement over `V`, by (F6)
  have hagr : AgreeAlong (chartU e y) (chartElem e hF3 y)
      (T := Over.mk (n ≫ chartFst e y ≫ (chartU e y).hom)) n rfl := by
    unfold AgreeAlong
    apply hF6 V (n ≫ chartFst e y ≫ (chartU e y).hom)
    have ha' : AgreeAtPt (chartU e y) (chartElem e hF3 y)
        ((Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ n)
          (closedPoint (FractionRing V))) := by rw [hng]; exact ha
    have h := agreeAlong_of_agreeAt
      (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ n ≫ chartFst e y ≫
        (chartU e y).hom)
      (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ n)
      (Category.assoc _ _ _) ha'
    unfold AgreeAlong at h
    rw [← map_comp_op_apply, ← map_comp_op_apply]
    convert h using 4 <;> (ext1; simp [algebraOverBase])
  -- restriction to the closed point of `V`
  let γ : Over.mk (Spec.map (CommRingCat.ofHom (residue V)) ≫ n ≫ chartFst e y ≫
      (chartU e y).hom) ⟶ Over.mk (n ≫ chartFst e y ≫ (chartU e y).hom) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (residue V))) rfl
  have hres := agreeAlong_comp hagr γ
  unfold AgreeAlong at hres
  have : IsLocalHom (CommRingCat.ofHom (residue V)).hom := inferInstanceAs (IsLocalHom (residue V))
  have hcl : (Spec.map (CommRingCat.ofHom (residue V))) (closedPoint (ResidueField V)) =
      closedPoint V := Spec_closedPoint
  have hg := chart_eq_of_closed e hF3 y (L := CommRingCat.of (ResidueField V))
    (Field.toIsField _) _ (fun x ↦ by
      have hx : x = closedPoint (ResidueField V) := Subsingleton.elim _ _
      subst hx
      change (chartFst e y ≫ (chartU e y).hom) (n ((Spec.map (CommRingCat.ofHom (residue V)))
        (closedPoint (ResidueField V)))) = _
      rw [hcl, hnc, hbs]) _ _ hres
  have hk := congrArg CommaMorphism.left hg
  simp only [Over.homMk_left, Category.assoc] at hk
  have hn : n ≫ chartFst e y = n ≫ chartSnd e y :=
    eq_of_isLocalRing (chartU e y).hom (n ≫ chartFst e y) (n ≫ chartSnd e y)
      (by simp only [Category.assoc, pullback.condition])
      (Spec.map (CommRingCat.ofHom (residue V))) hk (closedPoint _) hcl
  have := lift_mem_range_diagonal (chartU e y).hom (chartFst e y) (chartSnd e y)
    pullback.condition n hn
    ((Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) (closedPoint _))
  rw [pullback.lift_fst_snd] at this
  have h1 : n ((Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))))
      (closedPoint (FractionRing V))) = a := hng
  change n _ ∈ _ at this
  exact h1 ▸ this

include hfu hlft in
/-- `ξ_y : Spec B_y → F` is a monomorphism. -/
theorem chartElem_isMonoElement (hF : FaithfullyFlatSheaf F) (hF6 : ValuativeSeparation F) :
    IsMonoElement F (chartElem e hF3 y) := by
  intro T h₁ h₂ h
  have w : h₁.left ≫ (chartU e y).hom = h₂.left ≫ (chartU e y).hom := by
    rw [Over.w h₁, Over.w h₂]
  ext1
  apply eq_of_forall_mem_range_diagonal (chartU e y).hom h₁.left h₂.left w
  intro z
  have hT : AgreeAlong (chartU e y) (chartElem e hF3 y) (T := T)
      (pullback.lift h₁.left h₂.left w) (by rw [pullback.lift_fst_assoc]; exact Over.w h₁) := by
    unfold AgreeAlong
    have e₁ : (Over.homMk (pullback.lift h₁.left h₂.left w ≫ pullback.fst _ _)
        (by rw [pullback.lift_fst]; exact Over.w h₁) : T ⟶ chartU e y) = h₁ :=
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)
    have e₂ : (Over.homMk (pullback.lift h₁.left h₂.left w ≫ pullback.snd _ _)
        (by rw [pullback.lift_snd]; exact Over.w h₂) : T ⟶ chartU e y) = h₂ :=
      Over.OverMorphism.ext (pullback.lift_snd _ _ _)
    rw [e₁, e₂]
    exact h
  let γ : Over.mk (T.left.fromSpecResidueField z ≫ T.hom) ⟶ T :=
    Over.homMk (T.left.fromSpecResidueField z) rfl
  have h2 := agreeAlong_comp hT γ
  have h3 := agreeAt_of_agreeAlong hF (L := T.left.residueField z) _ _ _ h2
  have hpt : (γ.left ≫ pullback.lift h₁.left h₂.left w) (closedPoint (T.left.residueField z)) =
      pullback.lift h₁.left h₂.left w z := by
    change pullback.lift h₁.left h₂.left w (T.left.fromSpecResidueField z (closedPoint _)) = _
    exact congrArg (fun p ↦ pullback.lift h₁.left h₂.left w p)
      (Scheme.fromSpecResidueField_apply _ _)
  rw [hpt] at h3
  exact chart_mem_range e hF3 y hF6 _ h3

end Chart

end CompleteLocal

end Langlands.AlgebraicGeometry.UnramifiedFunctor
