/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint
import WeilConjectures.CategoryTheory.Normalized.NormalizedScalarUnitAdjunction

/-! The regular scalar unit in the exact degree-zero adjunction. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private theorem ordinary_unit_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _
      (Functor.OplaxMonoidal.η (ProEtale.etaleSheafExtendScalars φ T)) =
      Functor.LaxMonoidal.ε (Sheaf.restrictScalars T.smallEtaleTopology φ) := by
  exact ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).homEquiv _ _).apply_symm_apply
    (Functor.LaxMonoidal.ε (Sheaf.restrictScalars T.smallEtaleTopology φ))

/-- The regular etale scalar unit is the exact adjunction insertion of the ordinary
restriction unit, after the canonical single/unit identifications.
Source: finite-dualizing coefficient normalization, paragraphs 1--3.
Proof: the published unit comparison satisfies the representative normalization.
Its representative is the transpose formed from the ordinary and derived scalar
adjunctions. The ordinary oplax unit has the ordinary lax restriction unit as
adjunct. Apply the normalized representative/single comparison.
(blueprint: lem-coef-etale-scalar-unit-insertion) -/
theorem scalarUnit_eq_adjointInsertion
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (Etale.scalarExtension φ T).map
        (_root_.DerivedCategory.singleFunctorObjUnitIso
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))).hom ≫
      (Etale.ExceptionalCoefficients.unitIso φ T).hom ≫
        (_root_.DerivedCategory.singleFunctorObjUnitIso
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))).inv =
      SheafExactDegreeZero.adjointInsertion
        (Sheaf.restrictScalars T.smallEtaleTopology φ)
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
        (Functor.LaxMonoidal.ε (Sheaf.restrictScalars T.smallEtaleTopology φ)) := by
  let F := ProEtale.etaleSheafExtendScalars φ T
  let U := Sheaf.restrictScalars T.smallEtaleTopology φ
  let a := ProEtale.etaleSheafExtendScalarsAdjunction φ T
  let S := Etale.scalarExtension φ T
  let ad : S ⊣ U.mapDerivedCategory := Adjunction.ofIsRightAdjoint _
  exact SheafExactDegreeZero.normalizedUnit_singleAdjunction F U a S ad
    (Etale.scalarExtensionRepresentative φ T) _
    (Etale.ExceptionalCoefficients.unitIso_existsUnique φ T).choose_spec.1
    rfl (ordinary_unit_mate φ T)

end AlgebraicGeometry.Etale
