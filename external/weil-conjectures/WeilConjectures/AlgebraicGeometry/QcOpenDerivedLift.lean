/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh

/-! # Lifting quasi-coherent derived objects from a quasi-compact open

Source: Stacks Project, Tag 08EE, proof invoking Tag 08ED, lemma-lift-quasi-coherent
(blueprint: lem-sc-qc-open-derived-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- Every quasi-coherent derived object on a quasi-compact open of an affine scheme
lifts to a quasi-coherent derived object on the scheme. Restriction is first to the
localized site and then transported by the canonical equivalence with the open's site.
Source: Stacks Project, Tag 08EE, proof invoking Tag 08ED, lemma-lift-quasi-coherent
(blueprint: lem-sc-qc-open-derived-lift).

Proof:
1. Write j : U → X for the open inclusion. A finite affine cover of U shows that j
   is quasi-compact: its intersections with affine opens of X are affine, since X
   is separated. Every open immersion is separated, hence j is quasi-separated.
2. Set E' = Rj_* E. By lem-pc-derived-direct-image-preserves-qcoh, its cohomology
   sheaves are quasi-coherent, so E' belongs to D_QCoh(O_X).
3. Apply lem-pc-restrict-derived-direct-image-open with f = j and V = U. The
   inverse image of U is U, and the induced map is the identity of U. This identifies
   the restriction of E' with R(id_U)_* E, which is E. -/
theorem exists_qc_derived_lift_of_isCompact_open
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedQCohCategory U.toScheme) :
    ∃ E' : schemeDerivedQCohCategory X,
      Nonempty
        (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj E'.obj ≅ E.obj) := by
  classical
  let : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have : QuasiCompact U.ι := inferInstance
  have : QuasiSeparated U.ι := inferInstance
  let F := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  let G := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
  -- Implement the restriction step directly using the underived open counit.
  have e : F ⋙ G ≅ 𝟭 (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) := by
    refine Functor.isoWhiskerLeft F (Scheme.Modules.overFunctorEquiv U) ≪≫ ?_
    exact Scheme.Modules.restrictFunctorAdjCounitIso U.ι
  -- Exact restriction commutes with right derivation, so derive this counit.
  let eD : F.rightDerivedFunctor ⋙ G.mapDerivedCategory ≅
      𝟭 (schemeDerivedCategory U.toScheme) :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F G).symm ≪≫
      Functor.rightDerivedFunctorNatIso e ≪≫
      Functor.rightDerivedFunctorIsoMapDerivedCategory
        (𝟭 (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))) ≪≫
      Functor.mapDerivedCategoryIdIso _
  refine ⟨⟨(schemeDerivedDirectImage U.ι).obj E.obj,
    schemeDerivedDirectImage_preserves_QCoh U.ι E.obj E.property⟩, ?_⟩
  exact ⟨eD.app E.obj⟩

end AlgebraicGeometry
