/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonCounit

/-!
# Canonical direct-image mate in fixed coefficients

Source: blueprint, theorem-comparison-direct-images--1, first proof paragraph;
Stacks Project, Tags 099R and 0B65
(auxiliary; not a blueprint node).

## Main definitions and statements

* `fixedComparisonPullbackPlus`: the canonical termwise pullback comparison.
* `fixedComparisonDirectImageMatePlus`: the canonical derived direct-image mate.
* `isIso_fixedComparisonDirectImageMatePlus`: its qcqs invertibility.
* `fixedComparisonDirectImageMatePlus_counit`: its specified counit normalization.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.ProEtale

/-- The pullback comparison, induced termwise from the specified sheaf comparison.
Exact pro-etale pullback is its own left derived functor.
Source: Stacks Tags 099R and 0B65; blueprint comparison-direct-image proof
(auxiliary; not a blueprint node). -/
noncomputable def fixedComparisonPullbackPlus (Λ : Type (u + 1)) [CommRing Λ]
    {U V : Scheme.{u}} (f : U ⟶ V) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus ≅
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus ⋙
        (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) U)).symm ≪≫
  Functor.mapDerivedCategoryPlusNatIso
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm ≪≫
  Functor.mapDerivedCategoryPlusCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) V)
    (upperStar (ModuleCat.{u + 1} Λ) f)

/-- The canonical derived direct-image mate of the underived counit comparison.
Its data is the existing right-derived base-change transformation, with its universal
property normalization, not a chosen isomorphism between the endpoints.
Source: Stacks Tags 099R and 0B65; blueprint comparison-direct-image proof
(auxiliary; not a blueprint node). -/
noncomputable def fixedComparisonDirectImageMatePlus (Λ : Type (u + 1)) [CommRing Λ]
    {U V : Scheme.{u}} (f : U ⟶ V) :
    Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlus ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange
    (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ))

/-- Invertibility of the specified mate for a qcqs morphism.
Source: Stacks Tag 099R; blueprint comparison-direct-image proof
(auxiliary; not a blueprint node).

Proof: the canonical underived comparison is invertible for qcqs f by
`isIso_lowerStarComparisonUpperStarBaseChange`. The comparison pullback of every
injective etale sheaf is acyclic for the pro-etale direct image by
`rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective`. Apply the general
right-derived base-change invertibility theorem to this actual underived map.
Thus it is the specified transformation, rather than an arbitrary comparison,
that is invertible. -/
theorem isIso_fixedComparisonDirectImageMatePlus (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f] :
    IsIso (fixedComparisonDirectImageMatePlus Λ f) := by
  have := isIso_lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)
  exact Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
    (asIso (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} Λ)))
    (fun I _ ↦ rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective
      (ModuleCat.{u + 1} Λ) f I)

/-- The specified counit-mate normalization. It also characterizes the named component
as the adjoint transpose of the pulled-back etale counit after inverse pullback comparison.
Source: Stacks Tag 0B65; blueprint comparison-direct-image proof, first paragraph
(auxiliary; not a blueprint node).

Proof: the iterated-mate identity identifies the underived direct-image comparison
as the mate of the specified pullback comparison. On bounded-below homotopy categories,
the factorization equations for the induced pullback comparison verify the hypothesis of
`Adjunction.derivedPlus_mateEquiv_app_fac`. Compare its conclusion with the defining
factorization of derived base change. Uniqueness of right-derived transformations gives
the derived mate identity. Identify the restricted adjunctions with `derivedPlus`, apply
`mateEquiv_counit`, and cancel the inverse pullback comparison. Compatibility of the
induced natural isomorphism with inversion is checked through the faithful inclusion
of D+ into the unbounded derived category. Naturality is built into the transformation. -/
theorem fixedComparisonDirectImageMatePlus_counit (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (fixedComparisonPullbackPlus Λ f).hom.app
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj K) ≫
      (upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus.map
        ((fixedComparisonDirectImageMatePlus Λ f).app K) ≫
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj K) =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app K) := by
  dsimp only [derivedUpperStarLowerStarAdjunctionPlus,
    Etale.derivedUpperStarLowerStarAdjunctionPlus]
  rw [Adjunction.derivedAdjunctionPlus_eq_derivedPlus,
    Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
  let σ := comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f
  let θ := (Functor.mapDerivedCategoryPlusCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) V)
    (upperStar (ModuleCat.{u + 1} Λ) f)).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso σ ≪≫
    Functor.mapDerivedCategoryPlusCompIso (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U)
  have hb : fixedComparisonDirectImageMatePlus Λ f =
      (mateEquiv (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus θ.hom) := by
    unfold fixedComparisonDirectImageMatePlus
    rw [ComparisonCore.underived_comparison_mate,
      Adjunction.rightDerivedFunctorPlusBaseChange_mateEquiv]
  rw [hb, mateEquiv_counit]
  have hθ : (fixedComparisonPullbackPlus Λ f).hom = θ.inv := by
    have hσ : (Functor.mapDerivedCategoryPlusNatIso σ.symm).hom =
        (Functor.mapDerivedCategoryPlusNatIso σ).inv := by
      apply NatTrans.ext
      funext X
      apply DerivedCategory.Plus.ι.map_injective
      rw [Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
        Functor.mapDerivedCategoryNatIso_symm]
      have h : DerivedCategory.Plus.ι.mapIso
          ((Functor.mapDerivedCategoryPlusNatIso σ).app X) =
          (Functor.mapDerivedCategoryNatIso σ).app X.obj :=
        Iso.ext (Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app σ X)
      exact (congrArg Iso.inv h).symm
    simp only [fixedComparisonPullbackPlus, θ, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, hσ, Category.assoc, σ]
  rw [hθ]
  change θ.inv.app _ ≫ θ.hom.app _ ≫ _ = _
  rw [Iso.inv_hom_id_app_assoc]

end AlgebraicGeometry.ProEtale
