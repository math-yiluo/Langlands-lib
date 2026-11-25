/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
public import WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps

/-! # The native derived scalar functor and the fixed scalar adjoint

The counit comparison is isolated from monoidal coherence to keep kernel checking small.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale.ExceptionalCoefficients

attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit

/-- Uniqueness of scalar left adjoints identifies the fixed representative with the
transported native left-derived cochain counit.
Source: Stacks 06YY and 07A4
(blueprint: lem-coef-etale-scalar-derived-comparison).

Proof: ordinary sheaf scalar extension is left adjoint to exact restriction. Derive
that adjunction and compare it to the fixed derived scalar adjunction by
leftAdjointUniq. The native leftDerivedCochainCounit equation computes the counit
of the fixed adjunction. Its cochain unit is the published mapComplex unit formula,
so the result is exactly scalarExtensionRepresentative. -/
theorem scalarExtension_derivedComparison
    (A B : Type (u + 1)) [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    [(ProEtale.etaleSheafExtendScalars φ T).PreservesKFlatQuasiIso] :
    ∃ e : scalarExtension φ T ≅ (ProEtale.etaleSheafExtendScalars φ T).leftDerivedFunctor,
      ∀ P, scalarExtensionRepresentative φ T P =
        e.hom.app (_root_.DerivedCategory.Q.obj P) ≫
          (ProEtale.etaleSheafExtendScalars φ T).rightExact_cochainCounit P := by
  let E := ProEtale.etaleSheafExtendScalars φ T
  let U := Sheaf.restrictScalars T.smallEtaleTopology φ
  let adj : E ⊣ U := ProEtale.etaleSheafExtendScalarsAdjunction φ T
  let : E.IsLeftAdjoint := adj.isLeftAdjoint
  let ad : scalarExtension φ T ⊣ U.mapDerivedCategory := Adjunction.ofIsRightAdjoint _
  let b : E.leftDerivedFunctor ⊣ U.mapDerivedCategory :=
    adj.derivedAdjunction.ofNatIsoRight U.rightDerivedFunctorIsoMapDerivedCategory
  let e : scalarExtension φ T ≅ E.leftDerivedFunctor := ad.leftAdjointUniq b
  refine ⟨e, ?_⟩
  intro P
  unfold scalarExtensionRepresentative
  rw [← mapComplex_unit_formula]
  exact (Adjunction.leftDerivedCochainCounit E U adj ad P).symm

end AlgebraicGeometry.Etale.ExceptionalCoefficients
