/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdCoefficientComparison
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.FourierTransform.FdCoefficientScalarLiftNormalization

/-! # Ambient normalization in the canonical coefficient presentation

Source: trace-definition coefficient-category comparison, integral steps 1--6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Ambient scalar normalization in the canonical datum-free transition presentation.
Source: trace-definition coefficient comparison, ambient normalization step
(blueprint: lem-fd-integral-ambient-scalar-normalization).

Proof: use fdCoefficientScalarLift_normalization. The redundant characteristic
parameter in the constructibility preservation proof changes neither the objects
nor the morphisms of the restricted completed extension: unfold its restriction
and discard the proof field by proof irrelevance. Thus its comparison has exactly
the canonical integralTransition target, and retains the same representative
normalization without changing any map.
-/
theorem fdIntegralAmbientScalarNormalization
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    ∃ (ordinary : FdOrdinaryScalarTransport l Ω T h)
      (comparison :
      (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T).ι ⋙
          integralDetailedTransport T l (pbcFiniteField.{u} l Ω E) ⋙
            pbcAmbientScalarExtension l Ω T h ≅
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω T E L h ⋙
          (sfIntegralConstructible l (pbcFiniteField.{u} l Ω L) T).ι ⋙
            integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)),
    (∀ (P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
    (hP : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T
      (DerivedCategory.Q.obj P.obj)),
    HEq (comparison.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
      (integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).map
        ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).hom.app P) ≫
      (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω L) T).hom.app
        ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).obj P.obj))
      ((pbcAmbientScalarExtension l Ω T h).map
        ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T).hom.app P.obj) ≫
      pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
        (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex
          (.up ℤ)).obj P.obj) ≫
      DerivedCategory.Q.map (ordinary.completion l Ω P.obj))) := by
  have hn := fdCoefficientScalarLift_normalization l D hl Ω T h
  dsimp only [GeneralAlgebraicallyClosedCoefficients.integralTransition,
    AlgebraicallyClosedCoefficients.Coefficient,
    AlgebraicallyClosedCoefficients.coefficientInclusion, pbcFiniteField,
    pbcFiniteFieldInclusion, sfConstructibleIntegralScalarExtension,
    pbcFiniteFieldField, pbcFiniteFieldAlgebra] at hn ⊢
  exact hn

end WeilConjectures
