/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportFormulas
public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportInternalData
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportInternalLeftCorePaste

/-! The categorical paste for internal-left scalar tensor transport.

## References

* Stacks Project, Tags 06YY and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient
open ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/--
The algebraic paste for internal-left scalar tensor transport, given the three normalization
equations as hypotheses.
-/
 theorem section_tensor_transport_internal_left_core (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    (b : TensorIso a T) (hb : TensorNormalized a T b)
    (barB : tensor Λ T ⋙ c.model.T ≅
      (c.model.T.prod c.model.T) ⋙ tensor Λ' T)
    (hbarB : TensorSectionCondition a T c b barB)
    (P Q : CochainComplex (Modules Λ T) ℤ)
    (hbn :
      b.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (compute a T P ⊗ₘ compute a T Q) ≫
            Functor.LaxMonoidal.μ DerivedCategory.Q
              (((QuotientChange.extension a T).mapHomologicalComplex (.up ℤ)).obj P)
              (((QuotientChange.extension a T).mapHomologicalComplex (.up ℤ)).obj Q) =
        (D a T).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
          compute a T (P ⊗ Q) ≫ DerivedCategory.Q.map (totalScalar a T P Q))
    (hcn :
      c.derived.hom.app (DerivedCategory.Q.obj (P ⊗ Q)) ≫
          c.model.T.map (sectionLocalizationComparison Λ T (P ⊗ Q)).hom ≫
            c.model.ε.app
              (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q)) =
        (derivedFunctor Λ' T).map (compute a T (P ⊗ Q)) ≫
          (sectionLocalizationComparison Λ' T
            (((QuotientChange.extension a T).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q))).hom ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex c.ordinary (.up ℤ)).hom.app (P ⊗ Q)))
    (hqnorm :
      (qTensor Λ T).app
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P,
            ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q) =
        (tensor Λ T).map
            (Prod.mkHom (sectionLocalizationComparison Λ T P).inv
              (sectionLocalizationComparison Λ T Q).inv) ≫
          (tensorComparison Λ T).inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          (derivedEquivalence Λ T).functor.map ((internalLocalizationTensorMap Λ T).app (P, Q)) ≫
          localizedTotalComparison Λ T P Q) :
    scalarTensorSectionInput a T c P Q ≫
        barB.hom.app
          (DerivedCategory.Q.obj
              (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P),
            DerivedCategory.Q.obj
              (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q)) ≫
          (tensor Λ' T).map
            (Prod.mkHom
              (c.model.ε.app (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P))
              (c.model.ε.app (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q))) ≫
          (qTensor Λ' T).app
            ((c.model.E.mapHomologicalComplex (.up ℤ)).obj
                (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P),
              (c.model.E.mapHomologicalComplex (.up ℤ)).obj
                (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q)) =
      scalarTensorSectionPath a T c P Q := by
  simpa only [Category.assoc] using
    (section_tensor_transport_internal_left_paste a T c hc b hb barB hbarB P Q hbn hcn hqnorm)

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
