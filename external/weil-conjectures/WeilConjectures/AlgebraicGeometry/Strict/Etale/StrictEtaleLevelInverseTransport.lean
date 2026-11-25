/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientTransportInterfaces

/-! # Normalized finite inverse-image transport

Source: Zheng, Construction 5.15 and Proposition 2.29(2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

/-- A finite inverse-image/scalar square, normalized by insertion of the tensor unit
and by its universal derived computation arrow. No exactness of scalar extension is
assumed. The ordinary square and the computation equation fix the derived square on
flat-term K-flat representatives, hence on every object by naturality.
Source: Zheng, Construction 5.15 and Proposition 2.29(2).
(blueprint: def-pur-strict-etale-level-inverse-transport). -/
structure StrictEtaleLevelInverseTransport
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PTA : StrictEtaleEvaluation T O ell} {PSA : StrictEtaleEvaluation S O ell}
    {PTB : StrictEtaleEvaluation T O' mu} {PSB : StrictEtaleEvaluation S O' mu}
    (UT : StrictEtaleCoefficientTransport a T PTA PTB)
    (US : StrictEtaleCoefficientTransport a S PSA PSB)
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)
    (DA : ∀ n, CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    (DB : ∀ n, CoefficientDerivedImage (B.lift n).modules (B.right n) (B.levelAdj n))
    (n : ℕ) where
  ordinary : siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n) ⋙
      (B.lift n).modules ≅ (A.lift (index n)).modules ⋙
        siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)
  derived : (US.level n).derived ⋙ (DB n).inverse ≅
    (DA (index n)).inverse ⋙ (UT.level n).derived
  unit : ∀ M,
    (sheafCompose T.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map
        (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf T n)
          ((A.lift (index n)).modules.obj M)) ≫
      (coefficientUnderlying (J := T.smallEtaleTopology) O' mu n).map
        (ordinary.inv.app M) ≫
      (B.lift n).moduleUnderlying.hom.app
        ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n)).obj M) =
    (A.lift (index n)).moduleUnderlying.hom.app M ≫
      (Scheme.etaleSetPullback g).map
        ((sheafCompose S.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying.{u + 1, u, u + 1} (a.sheaf S n) M))
  representative : ∀ K,
    CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientQuotientSheaf (J := S.smallEtaleTopology) O ell (index n)) K →
    (∀ i : ℤ, IsFlatOnSite (J := S.smallEtaleTopology)
      (R := coefficientQuotientSheaf (J := S.smallEtaleTopology) O ell (index n)) (K.X i)) →
    derived.hom.app (DerivedCategory.Q.obj K) ≫
      (UT.level n).derived.map ((DA (index n)).inverseFactors.hom.app K) ≫
      (UT.level n).counit.app
        (((A.lift (index n)).modules.mapHomologicalComplex (.up ℤ)).obj K) =
    (DB n).inverse.map ((US.level n).counit.app K) ≫
      (DB n).inverseFactors.hom.app
        (((siteCoefficientTensor.{u + 1, u, u + 1}
          (a.sheaf S n)).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app K)

end AlgebraicGeometry
