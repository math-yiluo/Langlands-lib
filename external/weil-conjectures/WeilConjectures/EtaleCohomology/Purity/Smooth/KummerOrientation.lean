/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerRelative
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionComp
public import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence

/-!
# The global orientation of the zero section of the affine line

For a rank-one datum whose Kummer class generates `R¹π_* Λ(1)` and a separated `k`-scheme `Y`
of finite type over an algebraically closed field `k`, the Kummer boundary `∂κ(t)` of the
coordinate of `𝔸¹_Y` is the fundamental class of the zero section `V(t) ≅ Y`: its adjoint
`Λ_{V(t)} ⟶ Rs^! (Λ(1)[2])` is an isomorphism.

The adjoint is pushed down to `Y` along `p : 𝔸¹_Y ⟶ Y`. There a class `γ` with supports on
`V(t)` becomes the morphism `Λ_Y ⟶ Rp_* Rs_! Rs^! (Λ(1)[2])` adjoint to `γ`, and the direct
image of the localization triangle of `(V(t), 𝔾_{m,Y})` identifies the latter target with
`R¹π_* Λ(1)`, concentrated in degree zero; under this identification the Kummer boundary is the
Kummer class, which generates.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The conjugate of a natural transformation of left adjoints, applied to the adjoint of a
morphism. -/
lemma Adjunction.homEquiv_comp_conjugateEquiv_app {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) {c : C}
    {d : D} (β : L₁.obj c ⟶ d) :
    adj₁.homEquiv c d β ≫ (conjugateEquiv adj₁ adj₂ α).app d =
      adj₂.homEquiv c d (α.app c ≫ β) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Category.assoc,
    (conjugateEquiv adj₁ adj₂ α).naturality β, ← Category.assoc, unit_conjugateEquiv,
    Category.assoc, ← R₂.map_comp]

/-- The transpose under a composite adjunction is the successive transpose. -/
private lemma Adjunction.homEquiv_comp_apply {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}
    (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) (X : C) (Y : E) (f : H.obj (F.obj X) ⟶ Y) :
    (adj₁.comp adj₂).homEquiv X Y f = adj₁.homEquiv X _ (adj₂.homEquiv _ Y f) := by
  rw [CategoryTheory.Adjunction.comp_homEquiv]
  rfl

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- For a closed immersion `i : Z ⟶ X` and `p : X ⟶ B` with `i ≫ p` invertible, the adjoint
`Λ_B ⟶ Rp_* Ri_! Λ_Z` of the restriction map `Λ_X ⟶ Ri_! Λ_Z` is an isomorphism: it is the unit
of the composite adjunction of `p` and of the compactification of `i`, whose left adjoint is
the derived pullback along the isomorphism `i ≫ p`. -/
theorem isIso_homEquiv_supportedRestrictionMap {B X Z : Scheme.{u}} (p : X ⟶ B) (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIso (i ≫ p)] :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).homEquiv _ _
      ((leftDerivedUpperStarConstantComplexIso Λ p).hom ≫ supportedRestrictionMap Λ i)) := by
  let c := HasCompactification.compactification i
  let F := rightDerivedLowerShriekToLowerStarComp (ModuleCat.{u + 1} Λ) i
  let adjC := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c.g).comp
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c.i)
  have hu : supportedRestrictionMap Λ i ≫ F.app (constantComplex Λ Z) =
      adjC.homEquiv _ _ (compactificationConstantComplexIso Λ i).hom := by
    have h := supportedTranspose_supportedRestrictionMap Λ i
    simp only [supportedTranspose, rightDerivedLowerShriekTranspose] at h
    rw [Iso.inv_comp_eq, Category.comp_id] at h
    rw [← h, Equiv.apply_symm_apply]
  let adj := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).comp adjC
  have he : IsIso (c.i ≫ c.g ≫ p) := by
    rw [← Category.assoc, ← c.comm]
    infer_instance
  let E : L((p)^*[ModuleCat.{u + 1} Λ]) ⋙ (L((c.g)^*[ModuleCat.{u + 1} Λ]) ⋙
      L((c.i)^*[ModuleCat.{u + 1} Λ])) ≅ L((c.i ≫ c.g ≫ p)^*[ModuleCat.{u + 1} Λ]) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (leftDerivedUpperStarComp _ c.g p).symm _ ≪≫
        (leftDerivedUpperStarComp _ c.i (c.g ≫ p)).symm
  have : (L((p)^*[ModuleCat.{u + 1} Λ]) ⋙ (L((c.g)^*[ModuleCat.{u + 1} Λ]) ⋙
      L((c.i)^*[ModuleCat.{u + 1} Λ]))).Full := Functor.Full.of_iso E.symm
  have : (L((p)^*[ModuleCat.{u + 1} Λ]) ⋙ (L((c.g)^*[ModuleCat.{u + 1} Λ]) ⋙
      L((c.i)^*[ModuleCat.{u + 1} Λ]))).Faithful := Functor.Faithful.of_iso E.symm
  have key : (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).homEquiv _ _
        ((leftDerivedUpperStarConstantComplexIso Λ p).hom ≫ supportedRestrictionMap Λ i) ≫
        (R((p)_*[ModuleCat.{u + 1} Λ])).map (F.app (constantComplex Λ Z)) =
      adj.homEquiv _ _ ((L((c.g)^*[ModuleCat.{u + 1} Λ]) ⋙
        L((c.i)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ p).hom ≫
          (compactificationConstantComplexIso Λ i).hom) := by
    rw [← Adjunction.homEquiv_naturality_right, Category.assoc, hu,
      ← Adjunction.homEquiv_naturality_left]
    simp only [adj, Adjunction.comp_homEquiv (derivedUpperStarLowerStarAdjunction _ p) adjC]
    rfl
  have : IsIso (adj.homEquiv _ _ ((L((c.g)^*[ModuleCat.{u + 1} Λ]) ⋙
      L((c.i)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ p).hom ≫
        (compactificationConstantComplexIso Λ i).hom)) := by
    rw [Adjunction.homEquiv_unit]
    infer_instance
  rw [← key] at this
  exact IsIso.of_isIso_comp_right _ ((R((p)_*[ModuleCat.{u + 1} Λ])).map
    (F.app (constantComplex Λ Z)))

/-- The derived pushforward along an isomorphism is an equivalence. -/
instance isEquivalence_rightDerivedLowerStar_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] :
    (R((e)_*[ModuleCat.{u + 1} Λ])).IsEquivalence :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
    e).isEquivalence_right_of_isEquivalence_left

/-- For a closed immersion `i : Z ⟶ X` and `p : X ⟶ B` with `i ≫ p` invertible, the adjoint
`Λ_Z ⟶ N` of a class `γ : Λ_X ⟶ Ri_! N` is an isomorphism if and only if the adjoint
`Λ_B ⟶ Rp_* Ri_! N` of `γ` under `Lp^* ⊣ Rp_*` is one. -/
theorem isIso_supportedTranspose_iff {B X Z : Scheme.{u}} (p : X ⟶ B) (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIso (i ≫ p)]
    {N : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj N) :
    IsIso (supportedTranspose Λ i γ) ↔
      IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).homEquiv _ _
        ((leftDerivedUpperStarConstantComplexIso Λ p).hom ≫ γ)) := by
  have h : (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).homEquiv _ _
      ((leftDerivedUpperStarConstantComplexIso Λ p).hom ≫ γ) =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).homEquiv _ _
        ((leftDerivedUpperStarConstantComplexIso Λ p).hom ≫ supportedRestrictionMap Λ i) ≫
        (R((p)_*[ModuleCat.{u + 1} Λ])).map
          ((R(i)_![ModuleCat.{u + 1} Λ]).map (supportedTranspose Λ i γ)) := by
    rw [← Adjunction.homEquiv_naturality_right, Category.assoc,
      supportedRestrictionMap_comp_map_supportedTranspose]
  have := isIso_homEquiv_supportedRestrictionMap Λ p i
  rw [h, isIso_comp_left_iff]
  let e : R(i)_![ModuleCat.{u + 1} Λ] ⋙ R((p)_*[ModuleCat.{u + 1} Λ]) ≅
      R((i ≫ p)_*[ModuleCat.{u + 1} Λ]) :=
    Functor.isoWhiskerRight (rightDerivedLowerShriekIsoRightDerivedLowerStar _ i) _ ≪≫
      rightDerivedLowerStarComp _ i p
  rw [show (R((p)_*[ModuleCat.{u + 1} Λ])).map
      ((R(i)_![ModuleCat.{u + 1} Λ]).map (supportedTranspose Λ i γ)) =
    (R(i)_![ModuleCat.{u + 1} Λ] ⋙ R((p)_*[ModuleCat.{u + 1} Λ])).map
      (supportedTranspose Λ i γ) from rfl, NatIso.isIso_map_iff e]
  exact (isIso_iff_of_reflects_iso _ _).symm

section Triangle

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  (T : Pretriangulated.Triangle (_root_.DerivedCategory C)) (hT : T ∈ distTriang _)
  (h₂ : ∀ m : ℤ, m ≠ 0 → IsZero ((_root_.DerivedCategory.homologyFunctor C m).obj T.obj₂))
  (h₃ : ∀ m : ℤ, m ≠ 0 → m ≠ 1 →
    IsZero ((_root_.DerivedCategory.homologyFunctor C m).obj T.obj₃))
  (hmor : IsIso ((_root_.DerivedCategory.homologyFunctor C 0).map T.mor₂))

include hT h₂ h₃ hmor in
/-- In a distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` with `B` concentrated in degree `0`, `C` in
degrees `0` and `1`, and `H⁰(B) ⟶ H⁰(C)` invertible, `A` is concentrated in degree `2`. -/
lemma isZero_homology_obj₁_of_ne_two (m : ℤ) (hm : m ≠ 2) :
    IsZero ((_root_.DerivedCategory.homologyFunctor C m).obj T.obj₁) := by
  open _root_.DerivedCategory.HomologySequence in
  by_cases h0 : m = 0
  · subst h0
    have hmono : Mono ((_root_.DerivedCategory.homologyFunctor C 0).map T.mor₁) :=
      (mono_homologyMap_mor₁_iff T hT (-1) 0 (by norm_num)).2
        ((h₃ (-1) (by norm_num) (by norm_num)).eq_of_src _ _)
    have hz : (_root_.DerivedCategory.homologyFunctor C 0).map T.mor₁ = 0 := by
      rw [← cancel_mono ((_root_.DerivedCategory.homologyFunctor C 0).map T.mor₂), zero_comp,
        ← Functor.map_comp, Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero]
    exact IsZero.of_mono_eq_zero _ hz
  by_cases h1 : m = 1
  · subst h1
    have hepi : Epi ((_root_.DerivedCategory.homologyFunctor C 0).map T.mor₂) := inferInstance
    have hδ : _root_.DerivedCategory.HomologySequence.δ T 0 1 = 0 :=
      (exact₃ T hT 0 1).epi_f_iff.1 hepi
    have hm1 : Mono ((_root_.DerivedCategory.homologyFunctor C 1).map T.mor₁) :=
      (mono_homologyMap_mor₁_iff T hT 0 1).2 hδ
    exact IsZero.of_mono_eq_zero ((_root_.DerivedCategory.homologyFunctor C 1).map T.mor₁)
      ((h₂ 1 one_ne_zero).eq_of_tgt _ _)
  · have hm1 : Mono ((_root_.DerivedCategory.homologyFunctor C m).map T.mor₁) :=
      (mono_homologyMap_mor₁_iff T hT (m - 1) m (by ring)).2
        ((h₃ (m - 1) (by omega) (by omega)).eq_of_src _ _)
    exact IsZero.of_mono_eq_zero ((_root_.DerivedCategory.homologyFunctor C m).map T.mor₁)
      ((h₂ m h0).eq_of_tgt _ _)

include hT h₂ in
/-- In a distinguished triangle `A ⟶ B ⟶ C ⟶ A[1]` with `B` concentrated in degree `0`, the
boundary `H¹(C) ⟶ H²(A)` is invertible. -/
lemma isIso_homologySequenceδ_one_two :
    IsIso (_root_.DerivedCategory.HomologySequence.δ T 1 2) := by
  open _root_.DerivedCategory.HomologySequence in
  have : Mono (δ T 1 2) :=
    (exact₃ T hT 1 2).mono_g ((h₂ 1 one_ne_zero).eq_of_src _ _)
  have : Epi (δ T 1 2) := (exact₁ T hT 1 2).epi_f ((h₂ 2 (by norm_num)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

omit [HasDerivedCategory C] in
/-- If the boundary `H¹(A) ⟶ H²(B)` attached to `f : A ⟶ B[1]` is invertible, so is
`H⁰(f[1]) : H⁰(A[1]) ⟶ H⁰(B[2])`. -/
lemma isIso_homology_zero_map_shift_of_isIso_shiftMap [HasDerivedCategory C]
    {A B : _root_.DerivedCategory C} (f : A ⟶ B⟦(1 : ℤ)⟧)
    (hf : IsIso ((_root_.DerivedCategory.homologyFunctor C 0).shiftMap f 1 2 (by norm_num))) :
    IsIso ((_root_.DerivedCategory.homologyFunctor C 0).map (f⟦(1 : ℤ)⟧')) := by
  have h1 : IsIso ((_root_.DerivedCategory.homologyFunctor C 1).map f) := by
    have : (_root_.DerivedCategory.homologyFunctor C 1).map f =
        (_root_.DerivedCategory.homologyFunctor C 0).shiftMap f 1 2 (by norm_num) ≫
          ((_root_.DerivedCategory.homologyFunctor C 0).shiftIso (1 : ℤ) 1 2
            (by norm_num)).inv.app B := by
      simp [Functor.shiftMap]
      rfl
    rw [this]
    infer_instance
  exact (NatIso.isIso_map_iff
    ((_root_.DerivedCategory.homologyFunctor C 0).shiftIso (1 : ℤ) 0 1 (by norm_num)) f).2 h1

end Triangle

section Orientation

variable [Finite Λ] [HasKummerClass Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]
  {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
  [QuasiCompact aY]

omit [Finite Λ] [HasKummerClass Λ] [IsAlgClosed k] [HasInvertibleExponent Λ (Spec (.of k))]
  [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] in
/-- For `π = j ≫ p`, the unit of `Lπ^* ⊣ Rπ_*` is the unit of `p` followed by `Rp_*` of the unit
of `j`, up to the composition isomorphisms. -/
lemma unit_comp_rightDerivedLowerStar_map_unit {X Y G : Scheme.{u}} (p : X ⟶ Y) (j : G ⟶ X)
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app M ≫
        (R((p)_*[ModuleCat.{u + 1} Λ])).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
            ((L((p)^*[ModuleCat.{u + 1} Λ])).obj M)) ≫
        (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} Λ) j p (j ≫ p) rfl).app _ =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (j ≫ p)).unit.app M ≫
        (R((j ≫ p)_*[ModuleCat.{u + 1} Λ])).map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) j p (j ≫ p) rfl).hom.app M) := by
  rw [← Category.assoc, ← Adjunction.comp_unit_app
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j) M]
  exact unit_conjugateEquiv _ _ _ M

set_option maxRecDepth 20000 in
-- the composites of derived functors between the derived categories of the two bases are large
include aY in
/-- The global orientation (`thm-pur-affine-line-orientation`) for a rank-one datum whose Kummer
class of the coordinate generates over every algebraically closed field, given the cohomology of
`𝔸¹_k` and `𝔾_{m,k}`: the adjoint `Λ_{V(t)} ⟶ Rs^!(Λ(1)[2])` of the Kummer boundary `∂κ(t)` is
an isomorphism. -/
theorem isIso_supportedClassMap_kummerBoundary_coord_of_cohomology
    (hKum : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [HasInvertibleExponent Λ (Spec (.of Ω))]
      (G' : Scheme.{u}) (j' : G' ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of Ω))) [IsOpenImmersion j']
      (hj' : Set.range j'.base =
        (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of Ω))).base)ᶜ)
      [HasInvertibleExponent Λ G'] (c : Λ),
      c • kummerClass Λ (AffineSpace.unitLineCoord j' hj') = 0 → c = 0)
    (hA : ∀ q : ℤ, q ≠ 0 → IsZero ((cohomology (ModuleCat.{u + 1} Λ)
      𝔸(ULift.{u} (Fin 1); Spec (.of k)) q).obj (constantComplex Λ _)))
    (eA : (cohomology (ModuleCat.{u + 1} Λ) 𝔸(ULift.{u} (Fin 1); Spec (.of k)) 0).obj
      (constantComplex Λ _) ≅ ModuleCat.of Λ Λ)
    {G₀ : Scheme.{u}} (j₀ : G₀ ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of k))) [IsOpenImmersion j₀]
    (hj₀ : Set.range j₀.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (.of k))).base)ᶜ)
    (hG : ∀ q : ℤ, q ≠ 0 → q ≠ 1 →
      IsZero ((cohomology (ModuleCat.{u + 1} Λ) G₀ q).obj (constantComplex Λ _)))
    (eG₀ : (cohomology (ModuleCat.{u + 1} Λ) G₀ 0).obj (constantComplex Λ _) ≅ ModuleCat.of Λ Λ)
    (eG₁ : (cohomology (ModuleCat.{u + 1} Λ) G₀ 1).obj (constantComplex Λ _) ≅ ModuleCat.of Λ Λ)
    [HasInvertibleExponent Λ Y] :
    IsIso (supportedClassMap Λ (𝔸(ULift.{u} (Fin 1); Y).zeroLocusSubschemeι
        {AffineSpace.coord Y (ULift.up 0)})
      (shiftSupportedClass Λ _ 2
        (kummerBoundary Λ (AffineSpace.coord Y (ULift.up 0))))) := by
  let X := 𝔸(ULift.{u} (Fin 1); Y)
  let t : Γ(X, ⊤) := AffineSpace.coord Y (ULift.up 0)
  let ι := X.zeroLocusSubschemeι {t}
  let p := X ↘ Y
  let eZ := AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) Y
    (s := {t}) Set.range_unique
  have : IsIso (ι ≫ p) := (inferInstance : IsIso eZ.inv)
  rw [supportedClassMap_eq_supportedTranspose, isIso_supportedTranspose_iff Λ p ι]
  let U := X.basicOpen t
  let jU := U.ι
  have hjU : Set.range jU.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ :=
    AffineSpace.range_basicOpen_ι_coord Y
  have hij : Set.range ι.base = (Set.range jU.base)ᶜ := range_zeroLocusSubschemeι_singleton t
  have : HasInvertibleExponent Λ U := .of_hom jU
  let L := tateObject Λ X 1
  let T := localizationTriangleLowerStar Λ p ι jU hij L
  have hT := localizationTriangleLowerStar_mem_distTriang Λ p ι jU hij L
  obtain ⟨LT, -, hLT, ⟨eTY⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject
    (Λ := Λ) Y 1
  have hQ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y (tateObject Λ Y 1) :=
    boundedConstructibleFiniteTor_tateObject Λ Y 1
  have hTz := (homology_props_of_iso_singleFunctor Λ eTY hLT).1
  let tX : (L((p)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ Y 1) ≅ L :=
    leftDerivedUpperStarTateObjectIso p 1
  -- `Rp_* Λ(1)` is concentrated in degree zero
  have h₂ : ∀ m : ℤ, m ≠ 0 →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ m).obj T.obj₂) := by
    obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerStar_affineLine_of_cohomology Λ aY hA eA hQ
    intro m hm
    exact (hTz m hm).of_iso ((_root_.DerivedCategory.homologyFunctor _ m).mapIso
      ((R((p)_*[ModuleCat.{u + 1} Λ])).mapIso tX.symm ≪≫ e))
  -- `Rπ_* Λ(1)` is concentrated in degrees zero and one
  have h₃ : ∀ m : ℤ, m ≠ 0 → m ≠ 1 →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ m).obj T.obj₃) := by
    obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerStar_multiplicativeGroup_of_cohomology Λ aY j₀
      hj₀ hG eG₀ eG₁ jU hjU hQ
    intro m h0 h1
    exact (isZero_homology_biprodShift Λ _ hTz m h0 h1).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ m).mapIso
        (localizationTriangleLowerStarObj₃Iso Λ p ι jU hij L ≪≫
          (R((jU ≫ p)_*[ModuleCat.{u + 1} Λ])).mapIso
            ((L((jU)^*[ModuleCat.{u + 1} Λ])).mapIso tX.symm ≪≫
              ((leftDerivedUpperStarComp _ jU p).app _).symm) ≪≫ e))
  have hmor : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map T.mor₂) := by
    let H := _root_.DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) 0
    let M := tateObject Λ Y 1
    have hp := isIso_unit_affineLine_of_cohomology Λ aY hA eA hQ eTY hLT
    have hjp := isIso_homology_zero_unit_multiplicativeGroup_of_cohomology Λ aY j₀ hj₀ hG eG₀
      eG₁ jU hjU hQ eTY hLT
    have hc : IsIso ((rightDerivedLowerStarCompHom (ModuleCat.{u + 1} Λ) jU p (jU ≫ p) rfl).app
        ((L((jU)^*[ModuleCat.{u + 1} Λ])).obj ((L((p)^*[ModuleCat.{u + 1} Λ])).obj M))) := by
      rw [← rightDerivedLowerStarComp_hom_comp_congr_hom]
      infer_instance
    have hu := congrArg H.map (unit_comp_rightDerivedLowerStar_map_unit Λ p jU M)
    simp only [Functor.map_comp] at hu
    have hb : IsIso (H.map ((R((p)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) jU).unit.app
          ((L((p)^*[ModuleCat.{u + 1} Λ])).obj M)))) := by
      let a := H.map ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app M)
      let b := H.map ((R((p)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) jU).unit.app
          ((L((p)^*[ModuleCat.{u + 1} Λ])).obj M)))
      let c := H.map ((rightDerivedLowerStarCompHom (ModuleCat.{u + 1} Λ) jU p (jU ≫ p) rfl).app
        ((L((jU)^*[ModuleCat.{u + 1} Λ])).obj ((L((p)^*[ModuleCat.{u + 1} Λ])).obj M)))
      have h3 : IsIso (a ≫ b ≫ c) := by
        simp only [a, b, c]
        rw [hu]
        infer_instance
      have : IsIso (b ≫ c) := IsIso.of_isIso_comp_left a (b ≫ c)
      exact IsIso.of_isIso_comp_right b c
    have hnat := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) jU).unit.naturality
      tX.hom
    have hm : T.mor₂ = (R((p)_*[ModuleCat.{u + 1} Λ])).map tX.inv ≫
        (R((p)_*[ModuleCat.{u + 1} Λ])).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) jU).unit.app
            ((L((p)^*[ModuleCat.{u + 1} Λ])).obj M)) ≫
        (R((p)_*[ModuleCat.{u + 1} Λ])).map ((L((jU)^*[ModuleCat.{u + 1} Λ]) ⋙
          R((jU)_*[ModuleCat.{u + 1} Λ])).map tX.hom) := by
      change (R((p)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) jU).unit.app L) = _
      rw [← Functor.map_comp, ← Functor.map_comp, ← hnat]
      simp
    rw [hm, Functor.map_comp, Functor.map_comp]
    infer_instance
  have h₁ := isZero_homology_obj₁_of_ne_two T hT h₂ h₃ hmor
  have hδ := isIso_homologySequenceδ_one_two T hT h₂
  -- the pieces of the Kummer boundary
  let θp := leftDerivedUpperStarConstantComplexIso Λ p
  let θj := leftDerivedUpperStarConstantComplexIso Λ jU
  let tU := leftDerivedUpperStarTateObjectIso (Λ := Λ) jU 1
  let κU := kummerClass Λ (X.basicOpenUnit t)
  let α := θj.hom ≫ κU ≫ tU.inv⟦(1 : ℤ)⟧'
  let w := supportedLocalizationBoundary Λ ι jU hij L
  let cs := ((R((jU)_*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app
    ((L((jU)^*[ModuleCat.{u + 1} Λ])).obj L)
  let sa := (shiftFunctorAdd' (_root_.DerivedCategory (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))) (1 : ℤ) 1 2 rfl).inv.app ((R(ι)_![ModuleCat.{u + 1} Λ]).obj
      ((R(ι)^![Λ]).obj L))
  let ss := ((R(ι)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 : ℤ)).inv.app _ ≫
    (R(ι)_![ModuleCat.{u + 1} Λ]).map (((R(ι)^![Λ]).commShiftIso 2).inv.app L)
  have hγ : shiftSupportedClass Λ ι 2 (kummerBoundary Λ t) =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) jU).homEquiv _ _ α ≫ cs ≫
        w⟦(1 : ℤ)⟧' ≫ sa ≫ ss := by
    simp only [shiftSupportedClass, kummerBoundary, α, cs, w, sa, ss, θj, κU, tU, L, jU, U, ι,
      Category.assoc]
  let Rp := R((p)_*[ModuleCat.{u + 1} Λ])
  let H := _root_.DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology
    (ModuleCat.{u + 1} Λ))
  let Ψ₁ := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).homEquiv _ _
    (θp.hom ≫ (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) jU).homEquiv _ _ α)
  have hΨ : (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).homEquiv _ _
      (θp.hom ≫ shiftSupportedClass Λ ι 2 (kummerBoundary Λ t)) =
      Ψ₁ ≫ Rp.map cs ≫ Rp.map (w⟦(1 : ℤ)⟧') ≫ Rp.map (sa ≫ ss) := by
    rw [hγ]
    simp only [Ψ₁, Rp, Adjunction.homEquiv_unit, Category.assoc, Functor.map_comp]
  -- `H⁰` of the adjoint of the Kummer class is invertible
  have hΨ₁ : IsIso ((H 0).map Ψ₁) := by
    have hunit : X.basicOpenUnit t = AffineSpace.unitLineCoord jU hjU := Units.ext rfl
    let Bι : (L((jU ≫ p)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ Y) ≅
        constantComplex Λ U :=
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) jU p (jU ≫ p) rfl).app _ ≪≫
        (L((jU)^*[ModuleCat.{u + 1} Λ])).mapIso θp ≪≫ θj
    have hgen := isIso_homology_zero_kummerClassAdjoint_of_cohomology Λ aY hKum j₀ hj₀ hG eG₀ eG₁
      jU hjU Bι
    let c := (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} Λ) jU p (jU ≫ p) rfl).app
      ((tateObject Λ U 1)⟦(1 : ℤ)⟧)
    have hc : IsIso c := by
      simp only [c]
      rw [← rightDerivedLowerStarComp_hom_comp_congr_hom]
      infer_instance
    have hkey : Ψ₁ ≫ (R((p)_*[ModuleCat.{u + 1} Λ])).map
        ((R((jU)_*[ModuleCat.{u + 1} Λ])).map (tU.hom⟦(1 : ℤ)⟧')) ≫
        (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} Λ) jU p (jU ≫ p) rfl).app _ =
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (jU ≫ p)).homEquiv _ _
          (Bι.hom ≫ kummerClass Λ (AffineSpace.unitLineCoord jU hjU)) := by
      have h1 : θp.hom ≫ (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) jU).homEquiv
          _ _ α ≫ (R((jU)_*[ModuleCat.{u + 1} Λ])).map (tU.hom⟦(1 : ℤ)⟧') =
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) jU).homEquiv _ _
            ((L((jU)^*[ModuleCat.{u + 1} Λ])).map θp.hom ≫ θj.hom ≫ κU) := by
        rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left]
        simp only [α, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
        erw [CategoryTheory.Functor.map_id, Category.comp_id]
      have h2 : Ψ₁ ≫ (R((p)_*[ModuleCat.{u + 1} Λ])).map
          ((R((jU)_*[ModuleCat.{u + 1} Λ])).map (tU.hom⟦(1 : ℤ)⟧')) =
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).comp
            (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) jU)).homEquiv _ _
            ((L((jU)^*[ModuleCat.{u + 1} Λ])).map θp.hom ≫ θj.hom ≫ κU) := by
        simp only [Ψ₁, Adjunction.homEquiv_comp_apply]
        refine (Adjunction.homEquiv_naturality_right
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p) _ _).symm.trans ?_
        exact congrArg ((derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1} Λ) p).homEquiv _ _) ((Category.assoc _ _ _).trans h1)
      rw [← Category.assoc, h2, Adjunction.homEquiv_comp_conjugateEquiv_app]
      congr 1
      simp only [Bι, κU, hunit, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    have h := congrArg (H 0).map hkey
    simp only [Functor.map_comp] at h
    have h3 : IsIso ((H 0).map Ψ₁ ≫ (H 0).map ((R((p)_*[ModuleCat.{u + 1} Λ])).map
        ((R((jU)_*[ModuleCat.{u + 1} Λ])).map (tU.hom⟦(1 : ℤ)⟧'))) ≫ (H 0).map c) := by
      rw [h]
      exact hgen
    have : IsIso ((H 0).map Ψ₁ ≫ (H 0).map ((R((p)_*[ModuleCat.{u + 1} Λ])).map
        ((R((jU)_*[ModuleCat.{u + 1} Λ])).map (tU.hom⟦(1 : ℤ)⟧')))) := by
      rw [← Category.assoc] at h3
      exact IsIso.of_isIso_comp_right _ ((H 0).map c)
    exact IsIso.of_isIso_comp_right _ ((H 0).map ((R((p)_*[ModuleCat.{u + 1} Λ])).map
        ((R((jU)_*[ModuleCat.{u + 1} Λ])).map (tU.hom⟦(1 : ℤ)⟧'))))
  -- `H⁰` of the boundary is invertible
  have hw : IsIso ((H 0).map (Rp.map (w⟦(1 : ℤ)⟧'))) := by
    have h := Rp.commShiftIso_hom_naturality w (1 : ℤ)
    have hw' : Rp.map (w⟦(1 : ℤ)⟧') = (Rp.commShiftIso (1 : ℤ)).hom.app _ ≫
        (Rp.map w)⟦(1 : ℤ)⟧' ≫ (Rp.commShiftIso (1 : ℤ)).inv.app _ := by
      rw [← Category.assoc, ← h]
      simp
    have := isIso_homology_zero_map_shift_of_isIso_shiftMap T.mor₃ hδ
    have hm₃ : (Rp.map w)⟦(1 : ℤ)⟧' = T.mor₃⟦(1 : ℤ)⟧' ≫
        ((Rp.commShiftIso (1 : ℤ)).inv.app _)⟦(1 : ℤ)⟧' := by
      rw [← Functor.map_comp]
      congr 1
      change Rp.map w = (Rp.map w ≫ (Rp.commShiftIso (1 : ℤ)).hom.app _) ≫ _
      rw [Category.assoc]
      erw [Iso.hom_inv_id_app, Category.comp_id]
    rw [hw', hm₃, Functor.map_comp, Functor.map_comp, Functor.map_comp]
    infer_instance
  -- the target of the adjoint is concentrated in degree zero
  let eT : Rp.obj ((R(ι)_![ModuleCat.{u + 1} Λ]).obj ((R(ι)^![Λ]).obj
      (L⟦(2 : ℤ)⟧))) ≅ T.obj₁⟦(2 : ℤ)⟧ :=
    Rp.mapIso ((R(ι)_![ModuleCat.{u + 1} Λ]).mapIso
        (((R(ι)^![Λ]).commShiftIso (2 : ℤ)).app L) ≪≫
      ((R(ι)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 : ℤ)).app _) ≪≫
    (Rp.commShiftIso (2 : ℤ)).app _
  rw [hΨ, _root_.DerivedCategory.isIso_iff]
  intro n
  by_cases hn : n = 0
  · subst hn
    simp only [Functor.map_comp]
    infer_instance
  · refine ⟨⟨0, (isZero_homology_constantComplex Λ Y n hn).eq_of_src _ _, ?_⟩⟩
    refine IsZero.eq_of_src ?_ _ _
    exact (h₁ (n + 2) (by omega)).of_iso ((H n).mapIso eT ≪≫
      ((H 0).shiftIso (2 : ℤ) n (n + 2) (by ring)).app _)

end Orientation

end Etale

end AlgebraicGeometry
