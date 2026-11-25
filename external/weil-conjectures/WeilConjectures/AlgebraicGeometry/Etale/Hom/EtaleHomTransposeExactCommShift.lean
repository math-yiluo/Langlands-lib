/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomTransposeExactCommShiftCore

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Pretriangulated.Opposite Opposite
namespace AlgebraicGeometry.Etale

set_option linter.style.haveILetI false

/-- Evaluation transposes commute with the normalized opposite shifts.
Source: Stacks Project, Tags 08JC and 08J9; blueprint
`lem-coef-etale-hom-transpose-exact`, proof steps 3--4.

Transpose the shift square through the tensor--Hom adjunction. On K-flat models both
sides are scalar balancing after the signed source reindexing, so the canonical
comparison identifies them. Localization extends the identity to all objects.
(blueprint: lem-coef-etale-hom-transpose-exact-comm-shift) -/
theorem etaleHomComparison_reversedExact_commShift
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (X : Scheme.{u}) (φ : A →+* B) (M : DerivedCategoryModule A X)
    (v : EtaleHomLeft X φ M ⟶ EtaleHomRight X φ M)
    (hv : IsEtaleHomTranspose X φ M v)
    (sA : ((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).CommShift ℤ)
    (sB : ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
      ((scalarExtension φ X).obj M)).CommShift ℤ)
    (_chiPhi : (EtaleHomLeft X φ M).CommShift ℤ)
    (_chiPsi : (EtaleHomRight X φ M).CommShift ℤ)
    (hA : EtaleHomShiftNormalization (ModuleCat.{u + 1} A) X M sA)
    (hB : EtaleHomShiftNormalization (ModuleCat.{u + 1} B) X
      ((scalarExtension φ X).obj M) sB)
    (hPhi :
      letI := etaleHomScalarCommShift X φ
      letI := _chiPhi
      ∀ (K : DerivedCategoryModule A X) (n : ℤ),
        ((EtaleHomLeft X φ M).commShiftIso n).hom.app (op K) =
          (scalarExtension φ X).map ((sA.commShiftIso n).hom.app (op K)) ≫
            ((scalarExtension φ X).commShiftIso n).hom.app
              (((derivedHom (ModuleCat.{u + 1} A) X).flip.obj M).obj (op K)))
    (hPsi :
      letI := etaleHomScalarCommShift X φ
      letI := _chiPsi
      ∀ (K : DerivedCategoryModule A X) (n : ℤ),
        ((EtaleHomRight X φ M).commShiftIso n).hom.app (op K) =
          ((derivedHom (ModuleCat.{u + 1} B) X).flip.obj
              ((scalarExtension φ X).obj M)).map
            ((((scalarExtension φ X).commShiftIso (-n)).inv.app K).op) ≫
          (sB.commShiftIso n).hom.app (op ((scalarExtension φ X).obj K))) :
    letI := etaleHomScalarCommShift X φ
    NatTrans.CommShift v ℤ := by
  letI := _chiPhi
  letI := _chiPsi
  apply NatTrans.CommShift.of_core
  intro n
  exact etaleHomComparison_reversedExact_commShift_core X φ M v hv sA sB
    _chiPhi _chiPsi hA hB hPhi hPsi n

end AlgebraicGeometry.Etale
