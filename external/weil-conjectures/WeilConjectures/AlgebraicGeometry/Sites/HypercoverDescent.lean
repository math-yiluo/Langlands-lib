/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleHypercover
public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSectionsLimitModule
public import WeilConjectures.AlgebraicTopology.SemiSimplicialObject.Coskeleton

/-!
# Descent of truncated étale hypercovers to a finite stage

Let `X = lim Dᵢ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps, and let `U` be a qcqs hypercover of `X` (a semi-simplicial object of the small
étale site of `X` with quasi-compact quasi-separated terms). We show that the truncation of `U`
in degrees `≤ N` descends to some stage `Dₖ`:

- `AlgebraicGeometry.TruncatedDescent`: an `N`-truncated semi-simplicial object `T` of the small
  étale site of `Dₖ` with quasi-compact quasi-separated terms, together with identifications
  `U_n ≅ T_n ×_{Dₖ} X` (`n ≤ N`) compatible with the face maps;
- `AlgebraicGeometry.exists_truncatedDescent`: such data exists at some stage;
- `AlgebraicGeometry.TruncatedDescent.baseChange`: the data can be moved to any later stage;
- `AlgebraicGeometry.TruncatedDescent.exists_isHypercover`: at every late enough stage, the
  coskeletal extension of `T` (`CategoryTheory.SemiSimplicialObject.Truncated.cosk`), which
  continues `T` above degree `N` by the matching objects, is a qcqs hypercover;
- `AlgebraicGeometry.TruncatedDescent.toCosk`: the morphism of semi-simplicial objects from `U`
  to the base change to `X` of the coskeletal extension of `T`, which is the given identification
  in degrees `≤ N`.

Morphisms between truncated hypercovers descend as well
(`AlgebraicGeometry.TruncatedDescent.exists_homDescent`).

The main inputs are the descent of quasi-compact quasi-separated étale schemes, of morphisms, of
equalities of morphisms and of surjectivity to a finite stage
(`AlgebraicGeometry.etale_finite_data_descent_of_isLimit`), and the fact that matching objects are
finite limits, so that their formation commutes with base change and preserves quasi-compactness
and quasi-separatedness.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme.Etale

variable {X : Scheme.{u}}

/-- Base change of étale schemes along `f : X ⟶ Y`, as a functor between small étale sites. -/
noncomputable abbrev baseChangeFunctor {Y : Scheme.{u}} (f : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @Etale ⊤ f

/-- Base change of étale schemes preserves finite limits. -/
instance preservesFiniteLimits_pullback {Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ f : Y.Etale ⥤ X.Etale) :=
  inferInstance

instance preservesFiniteLimits_baseChangeFunctor {Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (baseChangeFunctor f) :=
  preservesFiniteLimits_pullback f

/-- The terminal object `X` of the small étale site of `X`. -/
noncomputable def isTerminal (X : Scheme.{u}) :
    IsTerminal (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X) : X.Etale) :=
  MorphismProperty.Over.mkIdTerminal _ X

/-- The isomorphism of underlying schemes induced by an isomorphism of étale `X`-schemes. -/
noncomputable def leftIso {A B : X.Etale} (e : A ≅ B) : A.left ≅ B.left :=
  (MorphismProperty.Over.forget @Etale ⊤ X ⋙ Over.forget X).mapIso e

@[simp]
lemma leftIso_hom {A B : X.Etale} (e : A ≅ B) : (leftIso e).hom = e.hom.left := rfl

@[simp]
lemma leftIso_inv {A B : X.Etale} (e : A ≅ B) : (leftIso e).inv = e.inv.left := rfl

@[reassoc (attr := simp)]
lemma inv_hom_id_left {A B : X.Etale} (e : A ≅ B) : e.inv.left ≫ e.hom.left = 𝟙 _ := by
  rw [← MorphismProperty.Comma.comp_left, e.inv_hom_id]
  rfl

@[reassoc (attr := simp)]
lemma hom_inv_id_left {A B : X.Etale} (e : A ≅ B) : e.hom.left ≫ e.inv.left = 𝟙 _ := by
  rw [← MorphismProperty.Comma.comp_left, e.hom_inv_id]
  rfl

/-- The morphism of étale schemes to a base change induced by a pullback square is an
isomorphism. -/
lemma isIso_homToPullback_of_isPullback {Y : Scheme.{u}} {t : X ⟶ Y} {V : X.Etale} {W : Y.Etale}
    {φ : V.left ⟶ W.left} (hφ : IsPullback φ V.hom W.hom t) :
    IsIso (Etale.homToPullback t φ hφ.w) := by
  have : IsIso (Etale.homToPullback t φ hφ.w).left := by
    have : (Etale.homToPullback t φ hφ.w).left = hφ.isoPullback.hom := by
      apply pullback.hom_ext <;> simp
    rw [this]
    infer_instance
  have : IsIso ((Over.forget X).map
      ((Scheme.Etale.forget X).map (Etale.homToPullback t φ hφ.w))) := this
  have : IsIso ((Scheme.Etale.forget X).map (Etale.homToPullback t φ hφ.w)) :=
    isIso_of_reflects_iso _ (Over.forget X)
  exact (Scheme.Etale.forgetFullyFaithful X).isIso_of_isIso_map _

/-- Surjectivity of the underlying morphism of schemes is invariant under isomorphisms of
arrows. -/
lemma surjective_left_iff_of_comm {A B A' B' : X.Etale} (e : A ⟶ B) (e' : A' ⟶ B')
    (i : A ≅ A') (j : B ≅ B') (h : e ≫ j.hom = i.hom ≫ e') :
    Surjective e.left ↔ Surjective e'.left :=
  MorphismProperty.arrow_mk_iso_iff @Surjective
    (Arrow.isoMk (leftIso i) (leftIso j) (by
      simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, leftIso_hom]
      rw [← MorphismProperty.Comma.comp_left, ← h, MorphismProperty.Comma.comp_left]))

lemma isTerminal_from_left (V : X.Etale) : ((isTerminal X).from V).left = V.hom := by
  have := MorphismProperty.Over.w ((isTerminal X).from V)
  erw [Category.comp_id] at this
  exact this

/-- A semi-simplicial object of the small étale site is a hypercover if and only if its
`0`-simplices cover `X` and all its matching maps are surjective. -/
lemma isHypercover_iff_surjective (V : SemiSimplicialObject X.Etale) :
    V.IsHypercover X.smallEtaleTopology ↔
      Surjective (V.obj 0).hom ∧ ∀ n, Surjective (V.toMatching n).left := by
  rw [SemiSimplicialObject.isHypercover_iff _ V (isTerminal X)]
  simp only [ofArrows_mem_smallEtaleTopology_iff, Set.iUnion_const, Set.range_eq_univ,
    ← surjective_iff]
  rw [isTerminal_from_left]

/-- The quasi-compact quasi-separated étale `X`-schemes. -/
def qcqs (X : Scheme.{u}) : ObjectProperty X.Etale :=
  fun V ↦ CompactSpace V.left ∧ QuasiSeparatedSpace V.left

instance : (qcqs X).IsClosedUnderIsomorphisms where
  of_iso {A B} e h := by
    obtain ⟨_, _⟩ := h
    exact ⟨QuasiCompact.compactSpace_of_compactSpace (leftIso e).inv,
      quasiSeparatedSpace_of_quasiSeparated (leftIso e).inv⟩

instance [CompactSpace X] [QuasiSeparatedSpace X] :
    (qcqs X).IsClosedUnderLimitsOfShape (Discrete PEmpty.{1}) where
  limitsOfShape_le := by
    rintro Y ⟨p⟩
    have hY : IsTerminal Y :=
      (IsLimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isLimit
    refine (qcqs X).prop_of_iso ((isTerminal X).uniqueUpToIso hY) ?_
    exact ⟨inferInstanceAs (CompactSpace X), inferInstanceAs (QuasiSeparatedSpace X)⟩

instance [QuasiSeparatedSpace X] : (qcqs X).IsClosedUnderLimitsOfShape WalkingCospan where
  limitsOfShape_le := by
    rintro Y ⟨p⟩
    let F := MorphismProperty.Over.forget @Etale ⊤ X ⋙ Over.forget X
    let e : Y.left ≅ pullback (p.diag.map WalkingCospan.Hom.inl).left
        (p.diag.map WalkingCospan.Hom.inr).left :=
      (isLimitOfPreserves F p.isLimit).conePointUniqueUpToIso (limit.isLimit _) ≪≫
        HasLimit.isoOfNatIso (diagramIsoCospan (p.diag ⋙ F))
    obtain ⟨_, _⟩ := p.prop_diag_obj WalkingCospan.left
    obtain ⟨_, _⟩ := p.prop_diag_obj WalkingCospan.right
    obtain ⟨_, _⟩ := p.prop_diag_obj WalkingCospan.one
    have : QuasiCompact (p.diag.map WalkingCospan.Hom.inl).left :=
      quasiCompact_of_compactSpace _
    exact ⟨QuasiCompact.compactSpace_of_compactSpace e.hom,
      @quasiSeparatedSpace_of_quasiSeparated _ _ (e.hom ≫ pullback.fst _ _) _ inferInstance⟩

instance [CompactSpace X] [QuasiSeparatedSpace X] (J : Type) [SmallCategory J] [FinCategory J] :
    (qcqs X).IsClosedUnderLimitsOfShape J := by
  have := hasFiniteLimits_of_hasTerminal_and_pullbacks (C := (qcqs X).FullSubcategory)
  have : PreservesFiniteLimits (qcqs X).ι :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
  exact (qcqs X).isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι _

/-- Base change of quasi-compact quasi-separated étale schemes to a quasi-compact quasi-separated
scheme. -/
lemma qcqs_baseChange {Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace Y]
    [QuasiSeparatedSpace X] {A : Y.Etale} (hA : qcqs Y A) :
    qcqs X ((baseChangeFunctor f).obj A) := by
  obtain ⟨_, _⟩ := hA
  have : CompactSpace ((𝟭 Scheme).obj A.left) := inferInstanceAs (CompactSpace A.left)
  have : QuasiSeparatedSpace ((𝟭 Scheme).obj A.left) := inferInstanceAs (QuasiSeparatedSpace A.left)
  have : QuasiSeparatedSpace ((Functor.fromPUnit Y).obj A.right) :=
    inferInstanceAs (QuasiSeparatedSpace Y)
  have : QuasiCompact A.hom := quasiCompact_of_compactSpace _
  exact ⟨inferInstanceAs (CompactSpace ↥(pullback A.hom f)),
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd A.hom f)⟩

/-- Matching objects of quasi-compact quasi-separated étale schemes over a quasi-compact
quasi-separated scheme are quasi-compact and quasi-separated. -/
lemma qcqs_matching [CompactSpace X] [QuasiSeparatedSpace X] (V : SemiSimplicialObject X.Etale)
    (n : ℕ) (hV : ∀ k, k ≤ n → qcqs X (V.obj k)) : qcqs X (V.matching n) := by
  cases n with
  | zero => exact (qcqs X).prop_pi _ fun _ ↦ hV 0 le_rfl
  | succ m =>
    refine (qcqs X).prop_limit _ fun j ↦ ?_
    cases j
    · exact (qcqs X).prop_pi _ fun _ ↦ hV (m + 1) le_rfl
    · exact (qcqs X).prop_pi _ fun _ ↦ hV m (by omega)

end Scheme.Etale

section Stage

variable {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  (hc : IsLimit c)

/-- (Implementation) The structure morphisms `Dⱼ ⟶ Dₖ` of the stages over a stage `k`. -/
@[simps]
def overStageπ (k : I) : Over.forget k ⋙ D ⟶ (Functor.const (Over k)).obj (D.obj k) where
  app j := D.map j.hom
  naturality j j' f := by simp [← D.map_comp]

include hc in
/-- (Implementation) The limit is also the limit of the stages over a stage `k`. -/
noncomputable def isLimitOverStage (k : I) : IsLimit (c.whisker (Over.forget k)) :=
  (Functor.Initial.isLimitWhiskerEquiv (Over.forget k) c).symm hc

omit [IsCofiltered I] in
/-- A pullback square from the limit to a stage `k` induces a pullback square from the limit to
any later stage `k'`. -/
lemma isPullback_lift_of_isPullback {k k' : I} (g : k' ⟶ k) {Y : (D.obj k).Etale}
    {V : c.pt.Etale} {m : V.left ⟶ Y.left} (hm : IsPullback m V.hom Y.hom (c.π.app k)) :
    IsPullback (pullback.lift m (V.hom ≫ c.π.app k')
        (by rw [hm.w, Category.assoc, c.w g]) : V.left ⟶ pullback Y.hom (D.map g))
      V.hom (pullback.snd Y.hom (D.map g)) (c.π.app k') := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst, c.w g]
  exact hm

variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

omit [∀ i, CompactSpace (D.obj i)] in
include hc in
/-- The limit is quasi-separated. -/
lemma quasiSeparatedSpace_pt : QuasiSeparatedSpace c.pt := by
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  have := isAffineHom_π_app D c hc i
  exact quasiSeparatedSpace_of_quasiSeparated (c.π.app i)

include hc in
/-- **Quasi-compact quasi-separated étale schemes descend** to a stage. -/
lemma exists_isPullback_etale (V : c.pt.Etale) [CompactSpace V.left]
    [QuasiSeparatedSpace V.left] :
    ∃ (k : I) (Y : (D.obj k).Etale) (_ : CompactSpace Y.left) (_ : QuasiSeparatedSpace Y.left)
      (m : V.left ⟶ Y.left), IsPullback m V.hom Y.hom (c.π.app k) := by
  have := quasiSeparatedSpace_pt hc
  have : CompactSpace ((𝟭 Scheme).obj V.left) := inferInstanceAs (CompactSpace V.left)
  have : QuasiSeparatedSpace ((𝟭 Scheme).obj V.left) := inferInstanceAs (QuasiSeparatedSpace V.left)
  have : QuasiSeparatedSpace ((Functor.fromPUnit c.pt).obj V.right) := quasiSeparatedSpace_pt hc
  have : QuasiCompact V.hom := quasiCompact_of_compactSpace _
  obtain ⟨k, Y, p, hp, h₁, h₂, m, H⟩ := exists_etale_isPullback_of_isLimit D c hc V.hom
  exact ⟨k, MorphismProperty.Over.mk ⊤ p hp, h₁, h₂, m, H⟩

omit [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
/-- **Morphisms descend** to a stage: a morphism over `X ⟶ Dₖ` from the base change `V` of a
quasi-compact quasi-separated étale `Dₖ`-scheme `A` to an étale `Dₖ`-scheme `B` comes from a
morphism `A ×_{Dₖ} Dₖ' ⟶ B ×_{Dₖ} Dₖ'` at every late enough stage. -/
lemma exists_hom_descent_stage {k : I} {A B : (D.obj k).Etale} [CompactSpace A.left]
    [QuasiSeparatedSpace A.left] {V : c.pt.Etale} {mA : V.left ⟶ A.left}
    (hA : IsPullback mA V.hom A.hom (c.π.app k)) (φ : V.left ⟶ B.left)
    (hφ : φ ≫ B.hom = V.hom ≫ c.π.app k) :
    ∃ (k' : I) (g : k' ⟶ k), ∀ (k'' : I) (g' : k'' ⟶ k') (h : k'' ⟶ k), g' ≫ g = h →
      ∃ ψ : (MorphismProperty.Over.pullback @Etale ⊤ (D.map h)).obj A ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ (D.map h)).obj B,
        pullback.lift mA (V.hom ≫ c.π.app k'') (by rw [hA.w, Category.assoc, c.w]) ≫
          ψ.left ≫ pullback.fst _ _ = φ := by
  have : CompactSpace ((𝟭 Scheme).obj A.left) := inferInstanceAs (CompactSpace A.left)
  have : QuasiSeparatedSpace ((𝟭 Scheme).obj A.left) := inferInstanceAs (QuasiSeparatedSpace A.left)
  have : ∀ {i j : Over k} (f : i ⟶ j), IsAffineHom ((Over.forget k ⋙ D).map f) :=
    fun f ↦ inferInstanceAs (IsAffineHom (D.map f.left))
  obtain ⟨k', f, ψ, hψ, hψφ⟩ := exists_hom_descent_of_isLimit (Over.forget k ⋙ D)
    (c.whisker (Over.forget k)) (isLimitOverStage hc k) (overStageπ k) (k := Over.mk (𝟙 k))
    A.hom B.hom (hA.isoPullback.inv ≫ φ) (by
      simp [hφ, IsPullback.isoPullback_inv_snd_assoc])
  refine ⟨k'.left, f.left, fun k'' g' _ hg ↦ ?_⟩
  subst hg
  have hfk : f.left = k'.hom := by simpa using Over.w f
  let ψ' : pullback A.hom (D.map (g' ≫ f.left)) ⟶ B.left :=
    pullback.map A.hom (D.map (g' ≫ f.left)) A.hom (D.map f.left) (𝟙 _) (D.map g') (𝟙 _)
      (by simp) (by simp) ≫ ψ
  have hψ' : ψ' ≫ B.hom = pullback.snd _ _ ≫ D.map (g' ≫ f.left) := by
    have : ψ ≫ B.hom = pullback.snd _ _ ≫ D.map f.left := by
      simpa [← hfk] using hψ
    simp [ψ', this]
  refine ⟨Etale.homToPullback (D.map (g' ≫ f.left)) ψ' hψ', ?_⟩
  rw [Etale.homToPullback_left_fst]
  have e : pullback.lift mA (V.hom ≫ c.π.app k'') (by rw [hA.w, Category.assoc, c.w]) ≫
      pullback.map A.hom (D.map (g' ≫ f.left)) A.hom (D.map f.left) (𝟙 _) (D.map g') (𝟙 _)
        (by simp) (by simp) =
      hA.isoPullback.hom ≫ pullback.map A.hom (c.π.app k) A.hom (D.map f.left) (𝟙 _)
        (c.π.app k'.left) (𝟙 _) (by simp) (by simp [c.w]) := by
    apply pullback.hom_ext <;> simp [c.w]
  calc _ = hA.isoPullback.hom ≫ (pullback.map A.hom (c.π.app k) A.hom (D.map f.left) (𝟙 _)
        (c.π.app k'.left) (𝟙 _) (by simp) (by simp [c.w]) ≫ ψ) := by
          simp only [ψ', ← Category.assoc, e]
    _ = hA.isoPullback.hom ≫ (hA.isoPullback.inv ≫ φ) := congrArg _ hψφ
    _ = φ := by rw [Iso.hom_inv_id_assoc]

omit [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
/-- **Equalities of morphisms descend** to a stage. -/
lemma exists_eq_descent_stage {k : I} {A B : (D.obj k).Etale} [CompactSpace A.left]
    {V : c.pt.Etale} {mA : V.left ⟶ A.left} (hA : IsPullback mA V.hom A.hom (c.π.app k))
    (a b : A ⟶ B) (h : mA ≫ a.left = mA ≫ b.left) :
    ∃ (k' : I) (g : k' ⟶ k), ∀ (k'' : I) (g' : k'' ⟶ k'),
      (MorphismProperty.Over.pullback @Etale ⊤ (D.map (g' ≫ g))).map a =
        (MorphismProperty.Over.pullback @Etale ⊤ (D.map (g' ≫ g))).map b := by
  have : CompactSpace ((𝟭 Scheme).obj A.left) := inferInstanceAs (CompactSpace A.left)
  have : ∀ {i j : Over k} (f : i ⟶ j), IsAffineHom ((Over.forget k ⋙ D).map f) :=
    fun f ↦ inferInstanceAs (IsAffineHom (D.map f.left))
  obtain ⟨k', f, hf⟩ := exists_eq_descent_of_isLimit (Over.forget k ⋙ D)
    (c.whisker (Over.forget k)) (isLimitOverStage hc k) (overStageπ k) (k := Over.mk (𝟙 k))
    A.hom B.hom a.left b.left (by simp [MorphismProperty.Over.w a])
    (by simp [MorphismProperty.Over.w b]) (by
      change pullback.fst A.hom (c.π.app k) ≫ a.left = pullback.fst A.hom (c.π.app k) ≫ b.left
      rw [← hA.isoPullback_inv_fst, Category.assoc, Category.assoc, h])
  refine ⟨k'.left, f.left, fun k'' g' ↦ ?_⟩
  apply Etale.hom_ext_pullback
  simp only [Etale.overPullback_map_left, pullback.lift_fst]
  simpa using congrArg (pullback.map A.hom (D.map (g' ≫ f.left)) A.hom (D.map f.left) (𝟙 _)
    (D.map g') (𝟙 _) (by simp) (by simp) ≫ ·) hf

omit [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
/-- **Surjectivity descends** to a stage: if the base change to the limit of a morphism of étale
`Dₖ`-schemes with quasi-compact target is surjective, so are its base changes to all late enough
stages. -/
lemma exists_surjective_descent_stage {k : I} {A B : (D.obj k).Etale} [CompactSpace B.left]
    (e : A ⟶ B)
    (h : Surjective ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app k)).map e).left) :
    ∃ (k' : I) (g : k' ⟶ k), ∀ (k'' : I) (g' : k'' ⟶ k'),
      Surjective ((MorphismProperty.Over.pullback @Etale ⊤ (D.map (g' ≫ g))).map e).left := by
  have : CompactSpace ((𝟭 Scheme).obj B.left) := inferInstanceAs (CompactSpace B.left)
  obtain ⟨k', f, hf⟩ := exists_forall_mem_range_of_isLimit D c hc B.hom (ι := PUnit.{u + 1})
    (fun _ ↦ e.left) (fun x ↦ by
      obtain ⟨y, rfl⟩ := h.surj x
      refine ⟨PUnit.unit, pullback.fst A.hom (c.π.app k) y, ?_⟩
      have hcomm : ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app k)).map e).left ≫
          pullback.fst B.hom (c.π.app k) = pullback.fst A.hom (c.π.app k) ≫ e.left := by simp
      exact (congrArg (fun φ ↦ φ.base y) hcomm).symm)
  refine ⟨k', f, fun k'' g' ↦ ⟨fun x ↦ ?_⟩⟩
  obtain ⟨-, a, ha⟩ := hf k'' g' x
  -- the base change of `e` is the base change of `e.left` along `B ×_{Dₖ} Dₖ'' ⟶ B`
  have H : IsPullback (pullback.fst A.hom (D.map (g' ≫ f)))
      ((MorphismProperty.Over.pullback @Etale ⊤ (D.map (g' ≫ f))).map e).left e.left
      (pullback.fst B.hom (D.map (g' ≫ f))) := by
    refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback B.hom (D.map (g' ≫ f)))
    simpa [MorphismProperty.Over.w e] using IsPullback.of_hasPullback A.hom (D.map (g' ≫ f))
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := e.left)
    (g := pullback.fst B.hom (D.map (g' ≫ f))) a x ha
  refine ⟨H.isoPullback.inv z, ?_⟩
  exact (congrArg (fun φ ↦ φ.base z) H.isoPullback_inv_snd).trans hz

end Stage

section Matching

variable {Y : Scheme.{u}}

open SemiSimplicialObject

/-- Surjectivity of the matching maps is invariant under morphisms which are isomorphisms in
low degrees. -/
lemma surjective_toMatching_iff_of_isIso {A B : SemiSimplicialObject Y.Etale} (f : A ⟶ B)
    (n : ℕ) (hf : ∀ k, k ≤ n + 1 → IsIso (f.app k)) :
    Surjective (A.toMatching n).left ↔ Surjective (B.toMatching n).left := by
  have := hf (n + 1) le_rfl
  have := isIso_matchingMap f n fun k hk ↦ hf k (by omega)
  exact Scheme.Etale.surjective_left_iff_of_comm _ _ (asIso (f.app (n + 1)))
    (asIso (matchingMap f n)) (toMatching_matchingMap f n)

/-- The matching maps of the base change of a semi-simplicial object are the base changes of its
matching maps. -/
lemma surjective_baseChange_toMatching_iff {Z : Scheme.{u}} (g : Z ⟶ Y)
    (V : SemiSimplicialObject Y.Etale) (n : ℕ) :
    Surjective ((MorphismProperty.Over.pullback @Etale ⊤ g).map (V.toMatching n)).left ↔
      Surjective ((V.baseChange g).toMatching n).left := by
  have : IsIso (V.mapMatchingComparison
      (MorphismProperty.Over.pullback @Etale ⊤ g : Y.Etale ⥤ Z.Etale) n) := inferInstance
  exact Scheme.Etale.surjective_left_iff_of_comm _ _ (Iso.refl _)
    (asIso (V.mapMatchingComparison
      (MorphismProperty.Over.pullback @Etale ⊤ g : Y.Etale ⥤ Z.Etale) n)) (by simp)

/-- A matching map which is an isomorphism is surjective. -/
lemma surjective_toMatching_of_hasUniqueLifts {V : SemiSimplicialObject Y.Etale} {n : ℕ}
    (h : V.HasUniqueLifts n) : Surjective (V.toMatching n).left := by
  have := h.isIso_toMatching
  infer_instance


/-- Unique lifts are preserved by base change. -/
lemma _root_.CategoryTheory.SemiSimplicialObject.HasUniqueLifts.baseChange
    {V : SemiSimplicialObject Y.Etale} {n : ℕ} (h : V.HasUniqueLifts n) {Z : Scheme.{u}}
    (g : Z ⟶ Y) : (V.baseChange g).HasUniqueLifts n :=
  h.map (MorphismProperty.Over.pullback @Etale ⊤ g : Y.Etale ⥤ Z.Etale)

/-- **Coskeletal replacement** of a hypercover: the coskeletal extension `V'` of the truncation of
a hypercover `V` in degrees `≤ N` is a hypercover with lifts above degree `N`, and the canonical
morphism `V ⟶ V'` is an isomorphism in degrees `≤ N`. -/
theorem exists_coskeletal_replacement (V : SemiSimplicialObject Y.Etale)
    (hV : V.IsHypercover Y.smallEtaleTopology) (N : ℕ) :
    ∃ (V' : SemiSimplicialObject Y.Etale) (u : V ⟶ V'), V'.IsHypercover Y.smallEtaleTopology ∧
      (∀ n, n ≤ N → IsIso (u.app n)) ∧ ∀ n, N ≤ n → V'.HasUniqueLifts n := by
  let T := V.truncate N
  let u : V ⟶ T.cosk := extendHom N (fun n h ↦ T.cosk_hasLifts n h)
    (fun n h ↦ (T.coskIso n h).inv) (fun n h i ↦ by
      rw [T.cosk_δ n h, Iso.inv_hom_id_assoc]
      rfl)
  have hu (n : ℕ) (h : n ≤ N) : IsIso (u.app n) := by
    rw [extendHom_app _ _ _ _ n h]
    infer_instance
  refine ⟨T.cosk, u, ?_, hu, fun n h ↦ T.cosk_hasUniqueLifts n h⟩
  rw [Scheme.Etale.isHypercover_iff_surjective] at hV ⊢
  refine ⟨?_, fun n ↦ ?_⟩
  · have := hu 0 (Nat.zero_le _)
    have e : (Scheme.Etale.leftIso (asIso (u.app 0))).inv ≫ (V.obj 0).hom = (T.cosk.obj 0).hom :=
      MorphismProperty.Over.w (asIso (u.app 0)).inv
    have := hV.1
    rw [← e]
    infer_instance
  · by_cases hn : n < N
    · rw [← surjective_toMatching_iff_of_isIso u n (fun j hj ↦ hu j (by omega))]
      exact hV.2 n
    · exact surjective_toMatching_of_hasUniqueLifts (T.cosk_hasUniqueLifts n (by omega))
end Matching

namespace Etale

section BaseChange

open SemiSimplicialObject

variable {Y Z : Scheme.{u}} (g : Y ⟶ Z) {V : SemiSimplicialObject Z.Etale}
  {U : SemiSimplicialObject Y.Etale} (φ : U ⟶ V.baseChange g)

/-- The projection `U_n ⟶ V_n` underlying a morphism `φ : U ⟶ V ×_Z Y` of semi-simplicial étale
schemes. -/
noncomputable def baseChangeProj (n : ℕ) : (U.obj n).left ⟶ (V.obj n).left :=
  (φ.app n).left ≫ pullback.fst (V.obj n).hom g

lemma baseChangeProj_eq (n : ℕ) :
    baseChangeProj g φ n = (φ.app n).left ≫ pullback.fst (V.obj n).hom g := rfl

omit φ in
@[simp]
lemma baseChangeProj_id (n : ℕ) :
    baseChangeProj g (𝟙 (V.baseChange g)) n = pullback.fst (V.obj n).hom g :=
  Category.id_comp _

include φ in
lemma baseChangeProj_w (n : ℕ) :
    baseChangeProj g φ n ≫ (V.obj n).hom = (U.obj n).hom ≫ g := by
  rw [baseChangeProj_eq, Category.assoc, pullback.condition, ← Category.assoc]
  congr 1
  exact MorphismProperty.Over.w (φ.app n)

@[reassoc]
lemma _root_.CategoryTheory.SemiSimplicialObject.baseChange_δ_left_fst (n : ℕ) (i : Fin (n + 2)) :
    ((V.baseChange g).δ n i).left ≫ pullback.fst (V.obj n).hom g =
      pullback.fst (V.obj (n + 1)).hom g ≫ (V.δ n i).left :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma _root_.CategoryTheory.SemiSimplicialObject.baseChange_δ_left_snd (n : ℕ) (i : Fin (n + 2)) :
    ((V.baseChange g).δ n i).left ≫ pullback.snd (V.obj n).hom g =
      pullback.snd (V.obj (n + 1)).hom g :=
  pullback.lift_snd _ _ _

@[reassoc]
lemma baseChangeProj_δ (n : ℕ) (i : Fin (n + 2)) :
    baseChangeProj g φ (n + 1) ≫ (V.δ n i).left = (U.δ n i).left ≫ baseChangeProj g φ n := by
  have h : (φ.app (n + 1) ≫ (V.baseChange g).δ n i).left ≫ pullback.fst (V.obj n).hom g =
      (U.δ n i ≫ φ.app n).left ≫ pullback.fst (V.obj n).hom g := by rw [φ.app_δ]
  rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left, Category.assoc,
    Category.assoc, baseChange_δ_left_fst] at h
  simpa only [baseChangeProj_eq, Category.assoc] using h

/-- A morphism `U ⟶ V ×_Z Y` from morphisms `U_n ⟶ V_n` over `g` commuting with the face
maps. -/
noncomputable def baseChangeMk (m : ∀ n, (U.obj n).left ⟶ (V.obj n).left)
    (hm : ∀ n, m n ≫ (V.obj n).hom = (U.obj n).hom ≫ g)
    (hδ : ∀ n i, m (n + 1) ≫ (V.δ n i).left = (U.δ n i).left ≫ m n) :
    U ⟶ V.baseChange g where
  app n := homToPullback g (m n) (hm n)
  app_δ n i := by
    apply hom_ext_pullback
    rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left, Category.assoc,
      Category.assoc, baseChange_δ_left_fst, homToPullback_left_fst_assoc,
      homToPullback_left_fst]
    exact hδ n i

omit φ in
@[simp]
lemma baseChangeProj_baseChangeMk (m : ∀ n, (U.obj n).left ⟶ (V.obj n).left)
    (hm : ∀ n, m n ≫ (V.obj n).hom = (U.obj n).hom ≫ g)
    (hδ : ∀ n i, m (n + 1) ≫ (V.δ n i).left = (U.δ n i).left ≫ m n) (n : ℕ) :
    baseChangeProj g (baseChangeMk g m hm hδ) n = m n :=
  homToPullback_left_fst _ _ _

/-- For a factorisation `g = g' ≫ h`, a morphism `U ⟶ V ×_Z Y` induces a morphism
`U ⟶ (V ×_Z Z') ×_{Z'} Y`. -/
noncomputable def baseChangeLift {Z' : Scheme.{u}} (g' : Y ⟶ Z') (h : Z' ⟶ Z)
    (hgh : g' ≫ h = g) : U ⟶ (V.baseChange h).baseChange g' :=
  baseChangeMk g' (fun n ↦ pullback.lift (baseChangeProj g φ n) ((U.obj n).hom ≫ g')
      (by rw [baseChangeProj_w, Category.assoc, hgh]))
    (fun n ↦ pullback.lift_snd _ _ _) (fun n i ↦ by
      apply pullback.hom_ext
      · rw [Category.assoc, baseChange_δ_left_fst, pullback.lift_fst_assoc, Category.assoc,
          pullback.lift_fst]
        exact baseChangeProj_δ g φ n i
      · rw [Category.assoc, baseChange_δ_left_snd, pullback.lift_snd, Category.assoc,
          pullback.lift_snd, ← Category.assoc, MorphismProperty.Over.w])

@[reassoc]
lemma baseChangeProj_baseChangeLift {Z' : Scheme.{u}} (g' : Y ⟶ Z') (h : Z' ⟶ Z)
    (hgh : g' ≫ h = g) (n : ℕ) :
    baseChangeProj g' (baseChangeLift g φ g' h hgh) n ≫ pullback.fst (V.obj n).hom h =
      baseChangeProj g φ n := by
  rw [baseChangeLift, baseChangeProj_baseChangeMk, pullback.lift_fst]

/-- For a factorisation `g' ≫ h`, a morphism `U ⟶ (V ×_Z Z') ×_{Z'} Y` induces a morphism
`U ⟶ V ×_Z Y`. -/
noncomputable def baseChangeTrans {Z' : Scheme.{u}} (g' : Y ⟶ Z') (h : Z' ⟶ Z)
    (ψ : U ⟶ (V.baseChange h).baseChange g') : U ⟶ V.baseChange (g' ≫ h) :=
  baseChangeMk (g' ≫ h) (fun n ↦ baseChangeProj g' ψ n ≫ pullback.fst _ _)
    (fun n ↦ by
      rw [Category.assoc, pullback.condition, ← Category.assoc,
        show baseChangeProj g' ψ n ≫ pullback.snd _ _ = _ from baseChangeProj_w g' ψ n,
        Category.assoc])
    (fun n i ↦ by rw [Category.assoc, ← baseChange_δ_left_fst h, baseChangeProj_δ_assoc])

lemma baseChangeProj_baseChangeTrans {Z' : Scheme.{u}} (g' : Y ⟶ Z') (h : Z' ⟶ Z)
    (ψ : U ⟶ (V.baseChange h).baseChange g') (n : ℕ) :
    baseChangeProj (g' ≫ h) (baseChangeTrans g' h ψ) n =
      baseChangeProj g' ψ n ≫ pullback.fst _ _ :=
  baseChangeProj_baseChangeMk _ _ _ _ n

/-- A morphism `U ⟶ V ×_Z Y` followed by the base change of a morphism `w : V ⟶ V'`. -/
noncomputable def baseChangeComp {V' : SemiSimplicialObject Z.Etale} (w : V ⟶ V') :
    U ⟶ V'.baseChange g :=
  baseChangeMk g (fun n ↦ baseChangeProj g φ n ≫ (w.app n).left)
    (fun n ↦ by rw [Category.assoc, MorphismProperty.Over.w, baseChangeProj_w])
    (fun n i ↦ by
      rw [Category.assoc, ← MorphismProperty.Comma.comp_left, w.app_δ,
        MorphismProperty.Comma.comp_left, baseChangeProj_δ_assoc])

lemma baseChangeProj_baseChangeComp {V' : SemiSimplicialObject Z.Etale} (w : V ⟶ V') (n : ℕ) :
    baseChangeProj g (baseChangeComp g φ w) n = baseChangeProj g φ n ≫ (w.app n).left :=
  baseChangeProj_baseChangeMk _ _ _ _ n

end BaseChange

end Etale

section Descent

variable {I : Type u} [SmallCategory I] {D : I ⥤ Scheme.{u}} {c : Cone D}

open SemiSimplicialObject

variable (c) in
/-- **Descent datum of a truncated étale hypercover**: for a semi-simplicial object `U` of the small
étale
site of the limit `X = lim Dᵢ`, an `N`-truncated semi-simplicial object `T` of the small étale
site of the stage `Dₖ`, with quasi-compact quasi-separated terms, together with pullback squares
`U_n ≅ T_n ×_{Dₖ} X` for `n ≤ N`, compatible with the face maps. -/
structure TruncatedDescent (U : SemiSimplicialObject c.pt.Etale) (N : ℕ) (k : I) where
  /-- The truncated semi-simplicial object at the stage `Dₖ`. -/
  T : Truncated (D.obj k).Etale N
  /-- The terms are quasi-compact and quasi-separated. -/
  qcqs (n : ℕ) (h : n ≤ N) : Scheme.Etale.qcqs _ (T.obj n h)
  /-- The projections `U_n ⟶ T_n`. -/
  m (n : ℕ) (h : n ≤ N) : (U.obj n).left ⟶ (T.obj n h).left
  /-- `U_n` is the base change of `T_n`. -/
  isPullback (n : ℕ) (h : n ≤ N) : IsPullback (m n h) (U.obj n).hom (T.obj n h).hom (c.π.app k)
  /-- Compatibility with the face maps. -/
  m_δ (n : ℕ) (h : n < N) (i : Fin (n + 2)) :
    m (n + 1) h ≫ (T.δ n h i).left = (U.δ n i).left ≫ m n h.le

namespace TruncatedDescent

variable {U : SemiSimplicialObject c.pt.Etale} {N : ℕ} {k : I} (d : TruncatedDescent c U N k)

variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- Moving a descent datum to a later stage, by base change. -/
noncomputable def baseChange {k' : I} (g : k' ⟶ k) : TruncatedDescent c U N k' where
  T := d.T.map (MorphismProperty.Over.pullback @Etale ⊤ (D.map g))
  qcqs n h := Scheme.Etale.qcqs_baseChange (D.map g) (d.qcqs n h)
  m n h := pullback.lift (d.m n h) ((U.obj n).hom ≫ c.π.app k')
    (by rw [(d.isPullback n h).w, Category.assoc, c.w g])
  isPullback n h := isPullback_lift_of_isPullback g (d.isPullback n h)
  m_δ n h i := by
    apply pullback.hom_ext
    · simp [d.m_δ n h i]
    · simp

/-- (Implementation) The components of `AlgebraicGeometry.TruncatedDescent.toCosk` in degrees
`≤ N`. -/
noncomputable def toCoskApp (n : ℕ) (h : n ≤ N) :
    U.obj n ⟶ (d.T.cosk.baseChange (c.π.app k)).obj n :=
  Etale.homToPullback (c.π.app k) (d.m n h ≫ (d.T.coskIso n h).inv.left) (by
    rw [Category.assoc, MorphismProperty.Over.w, (d.isPullback n h).w])

lemma isIso_toCoskApp (n : ℕ) (h : n ≤ N) : IsIso (d.toCoskApp n h) := by
  have H : IsPullback (d.m n h ≫ (d.T.coskIso n h).inv.left) (U.obj n).hom
      (d.T.cosk.obj n).hom (c.π.app k) := by
    refine IsPullback.of_iso (d.isPullback n h) (Iso.refl _)
      (Scheme.Etale.leftIso (d.T.coskIso n h).symm) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;>
      simp
  exact Scheme.Etale.isIso_homToPullback_of_isPullback H

/-- The morphism from `U` to the base change to the limit of the coskeletal extension of the
descended truncation. In degrees `≤ N` it is the isomorphism `U_n ≅ T_n ×_{Dₖ} X`
(`AlgebraicGeometry.TruncatedDescent.toCosk_app`). -/
noncomputable def toCosk : U ⟶ d.T.cosk.baseChange (c.π.app k) :=
  extendHom N (fun n h ↦ ((d.T.cosk_hasUniqueLifts n h).map
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app k) :
        (D.obj k).Etale ⥤ c.pt.Etale)).hasLifts)
    d.toCoskApp
    (fun n h i ↦ by
      apply Etale.hom_ext_pullback
      simp [toCoskApp, Truncated.cosk_δ _ n h, reassoc_of% (d.m_δ n h i)])

lemma toCosk_app (n : ℕ) (h : n ≤ N) : d.toCosk.app n = d.toCoskApp n h :=
  extendHom_app (U := U) (W := d.T.cosk.baseChange (c.π.app k)) _ _ _ _ n h

lemma isIso_toCosk_app (n : ℕ) (h : n ≤ N) : IsIso (d.toCosk.app n) := by
  rw [d.toCosk_app n h]
  exact d.isIso_toCoskApp n h

lemma toCosk_app_left_fst (n : ℕ) (h : n ≤ N) :
    (d.toCosk.app n).left ≫ pullback.fst _ _ = d.m n h ≫ (d.T.coskIso n h).inv.left := by
  rw [d.toCosk_app n h, toCoskApp, Etale.homToPullback_left_fst]

section Hypercover

variable [IsCofiltered I] [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

/-- **Descended truncated hypercovers are hypercovers at late stages**: if `U` is a hypercover of
`X`, then for every late
enough stage `Dₖ'`, the coskeletal extension of the base change to `Dₖ'` of the descended
truncation is a hypercover of `Dₖ'`. -/
theorem exists_isHypercover (hc : IsLimit c) (hU : U.IsHypercover c.pt.smallEtaleTopology) :
    ∃ (k₀ : I) (f₀ : k₀ ⟶ k), ∀ (k' : I) (g : k' ⟶ k₀),
      (d.baseChange (g ≫ f₀)).T.cosk.IsHypercover (D.obj k').smallEtaleTopology := by
  rw [Scheme.Etale.isHypercover_iff_surjective] at hU
  obtain ⟨hU₀, hU₁⟩ := hU
  let V := d.T.cosk
  have hVq (n : ℕ) (h : n ≤ N) : Scheme.Etale.qcqs _ (V.obj n) :=
    (Scheme.Etale.qcqs _).prop_of_iso (d.T.coskIso n h).symm (d.qcqs n h)
  -- the matching maps in degrees `< N` are surjective after base change to the limit, ...
  have hM (n : ℕ) (h : n < N) : Surjective
      ((Scheme.Etale.baseChangeFunctor (c.π.app k)).map (V.toMatching n)).left := by
    rw [surjective_baseChange_toMatching_iff, ← surjective_toMatching_iff_of_isIso d.toCosk n
      (fun j hj ↦ d.isIso_toCosk_app j (by omega))]
    exact hU₁ n
  -- ... hence at all late enough stages
  have key (n : Fin N) : ∃ (k' : I) (g : k' ⟶ k), ∀ (k'' : I) (g' : k'' ⟶ k'), Surjective
      ((Scheme.Etale.baseChangeFunctor (D.map (g' ≫ g))).map (V.toMatching n)).left := by
    obtain ⟨_, -⟩ := Scheme.Etale.qcqs_matching V n fun j hj ↦ hVq j (by omega)
    exact exists_surjective_descent_stage hc (V.toMatching n) (hM n n.2)
  choose kM gM hgM using key
  -- the `0`-simplices cover after base change to the limit, hence at all late enough stages
  have key₀ : ∃ (k' : I) (g : k' ⟶ k), ∀ (k'' : I) (g' : k'' ⟶ k'), Surjective
      ((Scheme.Etale.baseChangeFunctor (D.map (g' ≫ g))).map
        ((Scheme.Etale.isTerminal _).from (V.obj 0))).left := by
    have : CompactSpace (MorphismProperty.Over.mk ⊤ (𝟙 (D.obj k))
        (MorphismProperty.id_mem _ _) : (D.obj k).Etale).left :=
      inferInstanceAs (CompactSpace (D.obj k))
    refine exists_surjective_descent_stage hc _ ?_
    have := d.isIso_toCosk_app 0 (Nat.zero_le _)
    let ht := (Scheme.Etale.isTerminal (D.obj k)).isTerminalObj
      (Scheme.Etale.baseChangeFunctor (c.π.app k))
    rw [Scheme.Etale.surjective_left_iff_of_comm _ ((Scheme.Etale.isTerminal c.pt).from (U.obj 0))
      (asIso (d.toCosk.app 0)).symm (ht.uniqueUpToIso (Scheme.Etale.isTerminal _))
      ((Scheme.Etale.isTerminal _).hom_ext _ _), Scheme.Etale.isTerminal_from_left]
    exact hU₀
  obtain ⟨k₀, g₀, hg₀⟩ := key₀
  -- a common stage
  obtain ⟨K, h, b, hb⟩ := IsCofiltered.exists_comp_eq_of_finite (ι := Option (Fin N))
    (fun i ↦ i.elim k₀ kM) (fun i ↦ match i with | none => g₀ | some n => gM n)
  refine ⟨K, h, fun k' g ↦ ?_⟩
  let G := Scheme.Etale.baseChangeFunctor (D.map (g ≫ h))
  let ψ := d.T.coskMapHom G
  have hψ (n : ℕ) (hn : n ≤ N) : IsIso (ψ.app n) := d.T.isIso_coskMapHom_app G n hn
  change (d.T.map G).cosk.IsHypercover _
  rw [Scheme.Etale.isHypercover_iff_surjective]
  refine ⟨?_, fun n ↦ ?_⟩
  · have := hψ 0 (Nat.zero_le _)
    have H := hg₀ k' (g ≫ b none)
    rw [Category.assoc, hb none] at H
    let ht := (Scheme.Etale.isTerminal (D.obj k)).isTerminalObj G
    rw [← Scheme.Etale.isTerminal_from_left, Scheme.Etale.surjective_left_iff_of_comm _
      (G.map ((Scheme.Etale.isTerminal _).from (V.obj 0))) (asIso (ψ.app 0))
      ((Scheme.Etale.isTerminal _).uniqueUpToIso ht) (ht.hom_ext _ _)]
    exact H
  · by_cases hn : n < N
    · have H := hgM ⟨n, hn⟩ k' (g ≫ b (some ⟨n, hn⟩))
      rw [Category.assoc, hb (some ⟨n, hn⟩)] at H
      rw [surjective_toMatching_iff_of_isIso ψ n (fun j hj ↦ hψ j (by omega)),
        ← surjective_baseChange_toMatching_iff]
      exact H
    · exact surjective_toMatching_of_hasUniqueLifts ((d.T.map G).cosk_hasUniqueLifts n (by omega))

end Hypercover

end TruncatedDescent

section Existence

variable [IsCofiltered I] [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

/-- **Truncations of semi-simplicial qcqs étale schemes descend** to a stage: if all terms of `U`
are quasi-compact and
quasi-separated, its truncation in degrees `≤ N` is the base change of an `N`-truncated
semi-simplicial object of the small étale site of some stage `Dₖ`. The finitely many terms, face
maps and simplicial identities descend by `AlgebraicGeometry.exists_isPullback_etale`,
`AlgebraicGeometry.exists_hom_descent_stage` and `AlgebraicGeometry.exists_eq_descent_stage`. -/
theorem exists_truncatedDescent (hc : IsLimit c) (U : SemiSimplicialObject c.pt.Etale)
    (hU : ∀ n, Scheme.Etale.qcqs _ (U.obj n)) (N : ℕ) :
    ∃ k : I, Nonempty (TruncatedDescent c U N k) := by
  classical
  -- the terms descend
  have hobj (n : Fin (N + 1)) := by
    obtain ⟨_, _⟩ := hU n
    exact exists_isPullback_etale hc (U.obj n)
  choose j Y hY₁ hY₂ m₀ hm₀ using hobj
  obtain ⟨K₁, hK₁⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  let a (n : Fin (N + 1)) : K₁ ⟶ j n := (hK₁ (Finset.mem_image_of_mem _ (Finset.mem_univ n))).some
  let A (n : Fin (N + 1)) : (D.obj K₁).Etale :=
    (Scheme.Etale.baseChangeFunctor (D.map (a n))).obj (Y n)
  have hA (n : Fin (N + 1)) : Scheme.Etale.qcqs _ (A n) :=
    Scheme.Etale.qcqs_baseChange _ ⟨hY₁ n, hY₂ n⟩
  let m₁ (n : Fin (N + 1)) : (U.obj n).left ⟶ (A n).left :=
    pullback.lift (m₀ n) ((U.obj n).hom ≫ c.π.app K₁) (by rw [(hm₀ n).w, Category.assoc, c.w])
  have hm₁ (n : Fin (N + 1)) : IsPullback (m₁ n) (U.obj n).hom (A n).hom (c.π.app K₁) :=
    isPullback_lift_of_isPullback (a n) (hm₀ n)
  -- the face maps descend
  have hface (p : Σ n : Fin N, Fin (n + 2)) := by
    obtain ⟨_, _⟩ := hA p.1.succ
    exact exists_hom_descent_stage hc (hm₁ p.1.succ)
      ((U.δ p.1 p.2).left ≫ m₁ p.1.castSucc) (by
        rw [Category.assoc, (hm₁ _).w, ← Category.assoc]
        exact congrArg (· ≫ c.π.app K₁) (MorphismProperty.Over.w (U.δ p.1 p.2)))
  choose kF gF hF using hface
  obtain ⟨K₂, h₂, bF, hbF⟩ := IsCofiltered.exists_comp_eq_of_finite kF gF
  let B (n : Fin (N + 1)) : (D.obj K₂).Etale :=
    (Scheme.Etale.baseChangeFunctor (D.map h₂)).obj (A n)
  have hB (n : Fin (N + 1)) : Scheme.Etale.qcqs _ (B n) := Scheme.Etale.qcqs_baseChange _ (hA n)
  let m₂ (n : Fin (N + 1)) : (U.obj n).left ⟶ (B n).left :=
    pullback.lift (m₁ n) ((U.obj n).hom ≫ c.π.app K₂) (by rw [(hm₁ n).w, Category.assoc, c.w])
  have hm₂ (n : Fin (N + 1)) : IsPullback (m₂ n) (U.obj n).hom (B n).hom (c.π.app K₂) :=
    isPullback_lift_of_isPullback h₂ (hm₁ n)
  have hψ₀ (p : Σ n : Fin N, Fin (n + 2)) : ∃ ψ : B p.1.succ ⟶ B p.1.castSucc,
      m₂ p.1.succ ≫ ψ.left ≫ pullback.fst _ _ = (U.δ p.1 p.2).left ≫ m₁ p.1.castSucc := by
    exact hF p K₂ (bF p) h₂ (hbF p)
  choose ψ hψ using hψ₀
  have hψ' (p : Σ n : Fin N, Fin (n + 2)) :
      m₂ p.1.succ ≫ (ψ p).left = (U.δ p.1 p.2).left ≫ m₂ p.1.castSucc := by
    apply pullback.hom_ext
    · simpa [m₂] using hψ p
    · have h1 : (ψ p).left ≫ pullback.snd _ _ = pullback.snd _ _ := MorphismProperty.Over.w (ψ p)
      rw [Category.assoc, h1, Category.assoc]
      simp only [m₂, pullback.lift_snd]
      exact (congrArg (· ≫ c.π.app K₂) (MorphismProperty.Over.w (U.δ p.1 p.2))).symm.trans
        (Category.assoc _ _ _)
  -- reindex by natural numbers
  let B' (n : ℕ) (h : n ≤ N) : (D.obj K₂).Etale := B ⟨n, Nat.lt_succ_of_le h⟩
  let m₂' (n : ℕ) (h : n ≤ N) : (U.obj n).left ⟶ (B' n h).left := m₂ ⟨n, Nat.lt_succ_of_le h⟩
  let ψ' (n : ℕ) (h : n < N) (i : Fin (n + 2)) : B' (n + 1) h ⟶ B' n h.le := ψ ⟨⟨n, h⟩, i⟩
  have hψ'' (n : ℕ) (h : n < N) (i : Fin (n + 2)) :
      m₂' (n + 1) h ≫ (ψ' n h i).left = (U.δ n i).left ≫ m₂' n h.le :=
    hψ' ⟨⟨n, h⟩, i⟩
  -- the simplicial identities descend
  have hid (q : Σ n : Fin N, MatchingIndex n) : ∃ (k' : I) (g : k' ⟶ K₂),
      ∀ (k'' : I) (g' : k'' ⟶ k') (hq : q.1.1 + 1 < N),
        (Scheme.Etale.baseChangeFunctor (D.map (g' ≫ g))).map
            (ψ' (q.1 + 1) hq q.2.1.2.succ ≫ ψ' q.1 q.1.2 q.2.1.1) =
          (Scheme.Etale.baseChangeFunctor (D.map (g' ≫ g))).map
            (ψ' (q.1 + 1) hq q.2.1.1.castSucc ≫ ψ' q.1 q.1.2 q.2.1.2) := by
    by_cases hq : q.1.1 + 1 < N
    · obtain ⟨_, _⟩ := hB ⟨q.1 + 2, by omega⟩
      obtain ⟨k', g, H⟩ := exists_eq_descent_stage hc (hm₂ _)
        (ψ' (q.1 + 1) hq q.2.1.2.succ ≫ ψ' q.1 q.1.2 q.2.1.1)
        (ψ' (q.1 + 1) hq q.2.1.1.castSucc ≫ ψ' q.1 q.1.2 q.2.1.2) (by
          change m₂' (q.1 + 2) hq ≫ _ = m₂' (q.1 + 2) hq ≫ _
          rw [Etale.etale_comp_left, Etale.etale_comp_left, reassoc_of% (hψ'' _ hq _),
            reassoc_of% (hψ'' _ hq _), hψ'', hψ'', ← Etale.etale_comp_left_assoc,
            ← Etale.etale_comp_left_assoc, U.δ_comp_δ _ q.2.2])
      exact ⟨k', g, fun k'' g' _ ↦ H k'' g'⟩
    · exact ⟨K₂, 𝟙 _, fun _ _ hq' ↦ absurd hq' hq⟩
  choose kI gI hI using hid
  obtain ⟨K₃, h₃, bI, hbI⟩ := IsCofiltered.exists_comp_eq_of_finite kI gI
  refine ⟨K₃, ⟨{
    T := {
      obj n h := (Scheme.Etale.baseChangeFunctor (D.map h₃)).obj (B' n h)
      δ n h i := (Scheme.Etale.baseChangeFunctor (D.map h₃)).map (ψ' n h i)
      δ_comp_δ n hn i j hij := by
        have H := hI ⟨⟨n, by omega⟩, ⟨(i, j), hij⟩⟩ K₃ (bI _) hn
        rw [hbI] at H
        simpa only [Functor.map_comp] using H }
    qcqs n h := Scheme.Etale.qcqs_baseChange _ (hB _)
    m n h := pullback.lift (m₂' n h) ((U.obj n).hom ≫ c.π.app K₃)
      (by rw [(hm₂ _).w, Category.assoc, c.w])
    isPullback n h := isPullback_lift_of_isPullback h₃ (hm₂ _)
    m_δ n h i := by
      apply pullback.hom_ext
      · simpa using hψ'' n h i
      · simp }⟩⟩

end Existence

end Descent

section Hom

variable {I : Type u} [SmallCategory I] {D : I ⥤ Scheme.{u}} {c : Cone D}

open SemiSimplicialObject

namespace TruncatedDescent

variable {U : SemiSimplicialObject c.pt.Etale} {N : ℕ} {k : I} (d : TruncatedDescent c U N k)

/-- A *descent of a morphism* `f : U ⟶ W ×_{Dₖ} X` along a descent datum `d` of the truncation
of `U`: morphisms `T_n ⟶ W_n` of étale `Dₖ`-schemes, `n ≤ N`, whose base changes to the limit
`X` are the components of `f`. They are not required to commute with the face maps
(`AlgebraicGeometry.TruncatedDescent.Hom.IsCompatible`). -/
structure Hom (W : SemiSimplicialObject (D.obj k).Etale) (f : U ⟶ W.baseChange (c.π.app k)) where
  /-- The components. -/
  ψ (n : ℕ) (h : n ≤ N) : d.T.obj n h ⟶ W.obj n
  /-- The base change of `ψ` to the limit is `f`. -/
  m_ψ (n : ℕ) (h : n ≤ N) : d.m n h ≫ (ψ n h).left = Etale.baseChangeProj (c.π.app k) f n

variable {d} {W : SemiSimplicialObject (D.obj k).Etale} {f : U ⟶ W.baseChange (c.π.app k)}

/-- The components of a descended morphism commute with the face maps. -/
def Hom.IsCompatible (Ψ : d.Hom W f) : Prop :=
  ∀ (n : ℕ) (h : n < N) (i : Fin (n + 2)), Ψ.ψ (n + 1) h ≫ W.δ n i = d.T.δ n h i ≫ Ψ.ψ n h.le

variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
/-- Moving a descended morphism to a later stage, by base change. -/
noncomputable def Hom.baseChange (Ψ : d.Hom W f) {k' : I} (g : k' ⟶ k) :
    (d.baseChange g).Hom (W.baseChange (D.map g))
      (Etale.baseChangeLift (c.π.app k) f (c.π.app k') (D.map g) (c.w g)) where
  ψ n h := (MorphismProperty.Over.pullback @Etale ⊤ (D.map g)).map (Ψ.ψ n h)
  m_ψ n h := by
    apply pullback.hom_ext
    · rw [Category.assoc, Etale.baseChangeProj_baseChangeLift, ← Ψ.m_ψ n h]
      change pullback.lift _ _ _ ≫ pullback.lift _ _ _ ≫ pullback.fst _ _ = _
      rw [pullback.lift_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc, show Etale.baseChangeProj (c.π.app k') (Etale.baseChangeLift
          (c.π.app k) f (c.π.app k') (D.map g) (c.w g)) n ≫ pullback.snd _ _ = _ from
        Etale.baseChangeProj_w _ _ n]
      change pullback.lift _ _ _ ≫ pullback.lift _ _ _ ≫ pullback.snd _ _ = _
      rw [pullback.lift_snd, pullback.lift_snd]

variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
lemma Hom.IsCompatible.baseChange {Ψ : d.Hom W f} (hΨ : Ψ.IsCompatible) {k' : I} (g : k' ⟶ k) :
    (Ψ.baseChange g).IsCompatible := fun n h i ↦
  ((MorphismProperty.Over.pullback @Etale ⊤ (D.map g)).map_comp _ _).symm.trans
    ((congrArg _ (hΨ n h i)).trans
      ((MorphismProperty.Over.pullback @Etale ⊤ (D.map g)).map_comp _ _))

/-- A compatible descended morphism into a semi-simplicial object with lifts above degree `N`
extends to a morphism from the coskeletal extension of the descended truncation. -/
noncomputable def Hom.toCosk (Ψ : d.Hom W f) (hΨ : Ψ.IsCompatible)
    (hW : ∀ n, N ≤ n → W.HasLifts n) : d.T.cosk ⟶ W :=
  extendHom N hW (fun n h ↦ (d.T.coskIso n h).hom ≫ Ψ.ψ n h) (fun n h i ↦ by
    rw [d.T.cosk_δ n h, Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
      hΨ n h i])

lemma Hom.toCosk_app (Ψ : d.Hom W f) (hΨ : Ψ.IsCompatible) (hW : ∀ n, N ≤ n → W.HasLifts n)
    (n : ℕ) (h : n ≤ N) : (Ψ.toCosk hΨ hW).app n = (d.T.coskIso n h).hom ≫ Ψ.ψ n h :=
  extendHom_app _ _ _ _ n h

/-- In degrees `≤ N`, the base change of `Ψ.toCosk` to the limit, composed with the comparison
`U ⟶ (cosk T) ×_{Dₖ} X`, is `f`. -/
lemma Hom.baseChangeProj_toCosk (Ψ : d.Hom W f) (hΨ : Ψ.IsCompatible)
    (hW : ∀ n, N ≤ n → W.HasLifts n) (n : ℕ) (h : n ≤ N) :
    Etale.baseChangeProj (c.π.app k) d.toCosk n ≫ ((Ψ.toCosk hΨ hW).app n).left =
      Etale.baseChangeProj (c.π.app k) f n := by
  rw [Ψ.toCosk_app hΨ hW n h, MorphismProperty.Comma.comp_left, Etale.baseChangeProj_eq,
    ← Ψ.m_ψ n h]
  calc _ = ((d.toCosk.app n).left ≫ pullback.fst _ _) ≫ (d.T.coskIso n h).hom.left ≫
        (Ψ.ψ n h).left := by simp only [Category.assoc]
    _ = _ := by
      rw [d.toCosk_app_left_fst n h, Category.assoc, ← Category.assoc (d.T.coskIso n h).inv.left,
        Scheme.Etale.inv_hom_id_left, Category.id_comp]

variable [IsCofiltered I] [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

include d in
/-- **Morphisms descend along a descent datum**: at a late enough stage, every morphism
`f: U ⟶ W ×_{Dₖ} X` has a descent along the base change of `d`. -/
theorem exists_hom (hc : IsLimit c) (W : SemiSimplicialObject (D.obj k).Etale)
    (f : U ⟶ W.baseChange (c.π.app k)) :
    ∃ (k' : I) (g : k' ⟶ k), Nonempty ((d.baseChange g).Hom (W.baseChange (D.map g))
      (Etale.baseChangeLift (c.π.app k) f (c.π.app k') (D.map g) (c.w g))) := by
  classical
  have key (n : Fin (N + 1)) := by
    obtain ⟨_, _⟩ := d.qcqs n (Nat.lt_succ_iff.1 n.2)
    exact exists_hom_descent_stage hc (d.isPullback n (Nat.lt_succ_iff.1 n.2))
      (Etale.baseChangeProj (c.π.app k) f n) (Etale.baseChangeProj_w _ f n)
  choose kn gn hn using key
  obtain ⟨K, h, b, hb⟩ := IsCofiltered.exists_comp_eq_of_finite kn gn
  have key' (n : Fin (N + 1)) := hn n K (b n) h (hb n)
  choose ψ hψ using key'
  refine ⟨K, h, ⟨fun n hn ↦ ψ ⟨n, Nat.lt_succ_of_le hn⟩, fun n hn ↦ ?_⟩⟩
  apply pullback.hom_ext
  · rw [Category.assoc, Etale.baseChangeProj_baseChangeLift]
    exact hψ ⟨n, Nat.lt_succ_of_le hn⟩
  · rw [Category.assoc, show (ψ ⟨n, Nat.lt_succ_of_le hn⟩).left ≫ pullback.snd _ _ = _ from
      MorphismProperty.Over.w (ψ ⟨n, Nat.lt_succ_of_le hn⟩),
      show Etale.baseChangeProj (c.π.app K) (Etale.baseChangeLift (c.π.app k) f (c.π.app K)
        (D.map h) (c.w h)) n ≫ pullback.snd _ _ = _ from Etale.baseChangeProj_w _ _ n]
    exact pullback.lift_snd _ _ _

/-- **Compatibility with the face maps descends**: a descended morphism becomes compatible
with the face maps at a late enough stage. -/
theorem Hom.exists_isCompatible (hc : IsLimit c) (Ψ : d.Hom W f) :
    ∃ (k' : I) (g : k' ⟶ k), (Ψ.baseChange g).IsCompatible := by
  classical
  have key (p : Σ n : Fin N, Fin (n + 2)) := by
    obtain ⟨_, _⟩ := d.qcqs (p.1 + 1) p.1.2
    refine exists_eq_descent_stage hc (d.isPullback (p.1 + 1) p.1.2)
      (Ψ.ψ (p.1 + 1) p.1.2 ≫ W.δ p.1 p.2) (d.T.δ p.1 p.1.2 p.2 ≫ Ψ.ψ p.1 p.1.2.le) ?_
    rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left, ← Category.assoc,
      Ψ.m_ψ, ← Category.assoc, d.m_δ, Category.assoc, Ψ.m_ψ, Etale.baseChangeProj_δ]
  choose kI gI hI using key
  obtain ⟨K, h, b, hb⟩ := IsCofiltered.exists_comp_eq_of_finite kI gI
  refine ⟨K, h, fun n hn i ↦ ?_⟩
  have H := hI ⟨⟨n, hn⟩, i⟩ K (b _)
  rw [hb] at H
  exact ((MorphismProperty.Over.pullback @Etale ⊤ (D.map h)).map_comp _ _).symm.trans
    (H.trans ((MorphismProperty.Over.pullback @Etale ⊤ (D.map h)).map_comp _ _))

end TruncatedDescent

end Hom

end AlgebraicGeometry
