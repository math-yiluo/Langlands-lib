/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomTransposeExactCommShiftComponent

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CategoryTheory.Pretriangulated.Opposite Opposite
namespace AlgebraicGeometry.Etale

/-- The evaluation transpose satisfies the shift square in one fixed integer degree.
Source: Stacks Project, Tags 08JC and 08J9; blueprint
`lem-coef-etale-hom-transpose-exact`, proof steps 3--4.

The composite shifts `_chiPhi` and `_chiPsi` are the normalized ones: `hPhi` and `hPsi`
give their components in terms of `sA`, `sB` and the scalar shift (without them the
statement is false, by twisting `_chiPhi` with the character `n ↦ (-1)^n`). Rewrite the
two components of the degree-`n` square by `hPhi` and `hPsi`; the resulting component
equation is `etaleHomComparison_reversedExact_commShift_component`, which transposes the
square through the tensor--Hom adjunction and reduces it to scalar tensor shift
cancellation.
(blueprint: lem-coef-etale-hom-transpose-exact-comm-shift-core) -/
theorem etaleHomComparison_reversedExact_commShift_core
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
          (sB.commShiftIso n).hom.app (op ((scalarExtension φ X).obj K)))
    (n : ℤ) :
    letI := etaleHomScalarCommShift X φ
    letI := _chiPhi
    letI := _chiPsi
    NatTrans.CommShiftCore v n := by
  refine ⟨?_⟩
  ext ⟨K⟩
  have h := etaleHomComparison_reversedExact_commShift_component X φ M v hv sA sB hA hB K n
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [hPhi K n, hPsi K n]
  exact h

end AlgebraicGeometry.Etale
