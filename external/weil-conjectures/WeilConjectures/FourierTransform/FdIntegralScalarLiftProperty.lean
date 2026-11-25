/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdRawLocalization.FdRawLocalizationScalarData

/-! # The normalized representative equation for integral scalar comparison

Source: trace-definition coefficient-category comparison, integral steps 1--6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.FdRawLocalization
namespace WeilConjectures

/-- The good-representative normalization of an integral scalar comparison.
This predicate is exactly the displayed lift equation, including the integral
identity cast; it introduces no replacement comparison or additional assumption.
Source: trace-definition integral comparison, representative-lift clause
(blueprint: def-fd-integral-scalar-lift-property). -/
def fdIntegralScalarLiftProperty
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (ordinary : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      FdOrdinaryScalarTransport l Ω T h)
    (b : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L)
 : Prop :=
  ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
      (V : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E) T).FullSubcategory)
      (hV : sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) T
        (DerivedCategory.Q.obj V.obj)),
      HEq (((b h).hom.app ⟨DerivedCategory.Q.obj V.obj, hV⟩).hom ≫
        eqToHom (congrArg (fun F ↦ F.obj
          ((U l Ω T h).obj ⟨DerivedCategory.Q.obj V.obj, hV⟩))
          (stage L).integral_identity) ≫
        (integralDetailedTransport T l (pbcFiniteField.{u} l Ω L)).map
          ((integralScalarExtensionComparison l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).hom.app V) ≫
        (fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω L) T).hom.app
          ((integralScalarComplexFunctor l (pbcFiniteField.{u} l Ω E)
            (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T).obj V.obj))
        ((pbcAmbientScalarExtension l Ω T h).map
          ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) T).hom.app V.obj) ≫
        pbcComplexCounit (pbcCompletedScalarMap l Ω T h)
          (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) T).mapHomologicalComplex
            (.up ℤ)).obj V.obj) ≫
        DerivedCategory.Q.map ((ordinary h).completion l Ω V.obj))

end WeilConjectures
