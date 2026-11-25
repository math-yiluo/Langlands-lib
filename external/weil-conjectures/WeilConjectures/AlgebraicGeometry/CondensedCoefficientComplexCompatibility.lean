/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexDiagram
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexDerivedTransport
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexUnderivedCompatibility

/-! # Compatibility of the coefficient-complex arrows with derived adjunctions -/

@[expose] public section
universe u v
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
open Scheme PadicAlgCl

/-- The explicit scalar-inclusion map on complexes is the mate of derived tensor
transitivity.

Source: the Hom paragraph of archived `ModuleObject/Colimit/TwoColimit.lean`, and
`new-weil-pbc-condensed-coefficient-complex-model`, step 3.
(auxiliary; not a blueprint node)

Proof: compute the mate before localization using the extension/restriction
adjunction. The unit is `m ↦ 1 ⊗ m`; tensor transitivity multiplies the two
coefficient factors. Its mate is consequently the map induced by the inclusion
of the intermediate coefficient algebra into the specified algebraic closure.
This is exactly `mixedScalarMap`, as can be checked after precomposing its
underlying morphism with the epimorphism `extendπ`. Apply the identity in every
degree. Exact extension and restriction descend to the unbounded derived
categories. Their factorization isomorphisms carry the localized units to the
derived units; the defining equations of `leftDerivedFunctorCompIso` and
`leftDerivedFunctorNatIso` carry the localized tensor comparison to
`derivedExtendScalarsCompIso`. Transport the degreewise identity along
these isomorphisms. This gives the displayed equality with the explicitly
constructed stage and vertex comparisons. All operations apply to arbitrary
complexes, including zero complexes, with no boundedness or filteredness
hypothesis. -/
theorem coefficientComplexToAlgCl_derived_compatibility
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F G : FiniteIntermediateField ℓ} (he : E ≤ G) (hf : F ≤ G)
    (C : CochainComplex
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ℤ) :
    finiteCoefficientDerivedAlgClHomEquiv X ℓ E
      (DerivedCategory.Q.obj ((coefficientComplexStage X ℓ he hf).obj C)) _
      ((derivedExtendScalarsCompIso X ℓ he).inv.app
          (DerivedCategory.Q.obj ((coefficientComplexStage X ℓ he hf).obj C)) ≫
        (derivedExtendScalarsToPadicAlgCl X ℓ G).map
          ((finiteCoefficientDerivedHomEquiv X ℓ he
              (DerivedCategory.Q.obj ((coefficientComplexStage X ℓ he hf).obj C)) _).symm
            (coefficientComplexStageIso X ℓ he hf C).hom) ≫
        (derivedExtendScalarsCompIso X ℓ hf).hom.app (DerivedCategory.Q.obj C)) =
      DerivedCategory.Q.map (coefficientComplexToAlgCl X ℓ he hf C) ≫
        (coefficientComplexVertexIso X ℓ (E := E) C).hom := by
  rw [coefficientComplex_derived_mate_transport,
    coefficientComplexToAlgCl_underived_compatibility]

end AlgebraicGeometry.ProEtale
