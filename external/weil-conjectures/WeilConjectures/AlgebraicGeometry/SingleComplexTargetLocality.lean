/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionDetectsIso
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionComparison
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh

/-! # Target locality of the single-complex criterion

Source: Stacks Project, Tag 0DJ9, reduction to affine bases.
(blueprint: lem-pc-single-complex-target-locality).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem qcoh_openRestriction (Y : Scheme.{u}) (U : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory Y) (hE : schemeDerivedQCohProperty Y E) :
    schemeDerivedQCohProperty U.toScheme
      ((schemeOpenRestriction Y U).mapDerivedCategory.obj E) := by
  apply (schemeDerivedQCoh_openRestriction_iff Y U E).mpr
  intro n
  have := hE n
  exact SheafOfModules.isQuasicoherent_over
    ((DerivedCategory.homologyFunctor _ n).obj E) U

set_option linter.unusedVariables false in
/-- The single-complex criterion for affine bases suffices for arbitrary bases.
The extra premise supplies only the affine-base case, to be proved separately by
source-open induction; it does not assume the original conclusion.
Source: Stacks Project, Tag 0DJ9, first paragraph of the proof.
(blueprint: lem-pc-single-complex-target-locality).

Proof: For a point of S' choose an affine neighbourhood V of its image in S, and an
affine neighbourhood V' of the point contained in g inverse-image V. Restrict f to
f inverse-image V and f' to f' inverse-image V'. Together with g restricted V' → V
and the restriction of g' these form a cartesian square with affine bases. Quasi-
compactness and quasi-separatedness survive this restriction. Restrict K, K' and
phi, using the canonical derived pullback composition comparison; quasi-coherent
cohomology and the stalk condition survive since local rings on opens agree with
the original local rings. Apply the supplied affine-base criterion. Derived direct
image commutes with restriction to inverse-image opens, as does derived pullback.
Their canonical comparisons identify the restricted composite with the local
base-change composite: this follows from naturality of the derived counits in the
adjoint description of the map. Thus the original arrow is invertible on V'.
Apply schemeDerived_isIso_of_openRestriction, since such V' cover S'. Empty bases
are covered by the vacuous locality criterion. No global compactness of S is used.
-/
theorem singleComplexBaseChange_targetLocal
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (h_affine : ∀ {X₀ X₀' S₀ S₀' : Scheme.{u}}
      (f₀ : X₀ ⟶ S₀) (f₀' : X₀' ⟶ S₀') (g₀ : S₀' ⟶ S₀) (g₀' : X₀' ⟶ X₀)
      (sq₀ : IsPullback g₀' f₀' f₀ g₀)
      [IsAffine S₀] [IsAffine S₀'] [QuasiCompact f₀] [QuasiSeparated f₀]
      (K₀ : schemeDerivedCategory X₀) (hK₀ : schemeDerivedQCohProperty X₀ K₀)
      (K₀' : schemeDerivedCategory X₀') (hK₀' : schemeDerivedQCohProperty X₀' K₀')
      (φ₀ : (derivedPullback g₀').obj K₀ ⟶ K₀')
      (h_stalk₀ : SingleComplexBaseChange.StalkCondition f₀ f₀' g₀ g₀' sq₀ K₀ K₀' φ₀),
      IsIso (schemeDerivedBaseChangeMap f₀ f₀' g₀ g₀' sq₀.w K₀ ≫
        (schemeDerivedDirectImage f₀').map φ₀))
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K')
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq K K' φ) :
    IsIso (schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
      (schemeDerivedDirectImage f').map φ) := by
  apply schemeDerived_isIso_of_openRestriction
  intro x
  obtain ⟨V, hV, hxV, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := g x) (U := ⊤) (by trivial)
  obtain ⟨V', hV', hxV', hVV'⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S') (x := x) (U := g ⁻¹ᵁ V) hxV
  have : IsAffine V.toScheme := hV
  have : IsAffine V'.toScheme := hV'
  have hU : f' ⁻¹ᵁ V' ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    calc
      f' ⁻¹ᵁ V' ≤ f' ⁻¹ᵁ (g ⁻¹ᵁ V) := f'.preimage_mono hVV'
      _ = g' ⁻¹ᵁ (f ⁻¹ᵁ V) := by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq.w]
  let j := g'.resLE (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') hU
  have sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hVV') := by
    have hUY : f' ⁻¹ᵁ V' = g' ⁻¹ᵁ (f ⁻¹ᵁ V) ⊓ f' ⁻¹ᵁ V' :=
      (inf_eq_right.mpr hU).symm
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
      Scheme.Hom.isPullback_resLE sq hVV' le_rfl hUY
  let K₀ := (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K
  let K₀' := (schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory.obj K'
  have hK₀ : schemeDerivedQCohProperty (f ⁻¹ᵁ V).toScheme K₀ :=
    qcoh_openRestriction X (f ⁻¹ᵁ V) K hK
  have hK₀' : schemeDerivedQCohProperty (f' ⁻¹ᵁ V').toScheme K₀' :=
    qcoh_openRestriction X' (f' ⁻¹ᵁ V') K' hK'
  let φ₀ := singleComplexRestrictedCoefficient g' K K' φ
    (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j (Scheme.Hom.resLE_comp_ι g' hU)
  obtain ⟨hstalk₀, a, b, hab⟩ :=
    singleComplexBaseChange_openRestrictionComparison f f' g g' sq K K' φ h_stalk
      V V' hVV' j (Scheme.Hom.resLE_comp_ι g' hU) sq₀
  have := h_affine (f ∣_ V) (f' ∣_ V') (g.resLE V V' hVV') j sq₀
    K₀ hK₀ K₀' hK₀' φ₀ hstalk₀
  refine ⟨V', hxV', ?_⟩
  rw [hab]
  infer_instance

end AlgebraicGeometry
