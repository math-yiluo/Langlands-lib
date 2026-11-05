import Langlands.Representation.Plancherel.FormalDegreeFixedCompactForm
import Langlands.Representation.Plancherel.FiniteSmoothFamilyForm
import Langlands.Representation.Plancherel.ProductInducedOrbitSections

/-!
# Positive cover integrals on actual smooth induced families

The inverse-Schur-degree form on each actual unitary-twisted product induction
is identified with one fixed compact form. Scalar smoothness and definiteness
then follow from the finite algebraic smooth-family model.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open MeasureTheory
open scoped TensorProduct NNReal

namespace Langlands.Plancherel

open Aubert.General HarishChandraSchwartz Induction CompactInduction
open FiniteTensor.InvariantPositiveFormProof

universe uG uI uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G))
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

include hPK in
omit [LocallyCompactSpace G] [NonarchimedeanGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace P] in
private theorem compactFactorization (g : G) :
    ∃ p ∈ P, ∃ k ∈ K, g = p * k := by
  obtain ⟨p, k, hg⟩ := hPK g
  exact ⟨p, p.property, k, k.property, hg⟩

variable
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure] [μ.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  {J : Type uJ} [Fintype J]
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))

omit [LocallyCompactSpace G] [NonarchimedeanGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Fintype J] in
/-- The torus parameter is unitary because it comes from the actual unitary
unramified subgroup. -/
theorem unitaryTorusParameter_norm (z : J → Circle) (m : M) :
    ‖((unitaryTorusParameter ν e z).val m : ℂ)‖ = 1 :=
  (e.symm z).property.2 m

/-- The actual canonical inverse-degree form in the dependent inducing fiber,
with the same prescribed central quotient and Haar measure at every parameter. -/
def unitaryTorusProductForm (z : J → Circle) :
    InvariantPositiveForm
      (productInducedCoefficientObject h hU
        (π.obj.twist (unitaryTorusParameter ν e z).val.toMonoidHom
          (unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z)))).representation :=
  formalDegreeProductForm h hU hP K hK (compactFactorization K hPK) hG hδ
    (π.obj.twist (unitaryTorusParameter ν e z).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z)))
    hcof C hC μ
    (isSquareIntegrableModCentralSubgroup_unitaryTwist C hC
      (unitaryTorusParameter ν e z).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z))
      (unitaryTorusParameter_norm ν e z) μ hsq)
    ((isIrreducible_twist_iff
      (unitaryTorusParameter ν e z).val.toMonoidHom π.obj.representation).mpr π.property.1)

omit [Fintype J] in
/-- The scalar pairing of the actual dependent fibers is exactly the pairing
of their literal compact restrictions in one fixed degree-normalized form. -/
theorem unitaryTorusProductForm_inner
    (F H : ProductInducedTorusFamilies ν e h hU π.obj) (z : J → Circle) :
    (unitaryTorusProductForm h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν e z).inner
        (F z) (H z) =
      (formalDegreeFixedProductCompactForm h hU hP K hK (compactFactorization K hPK)
        hG hδ π.obj hcof C hC μ hsq π.property.1).inner
        (productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj F z)
        (productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj H z) :=
  (formalDegreeProductInducedCompactEquiv_inner
    h hU hP K hK (compactFactorization K hPK) hG hδ π.obj hcof C hC μ hsq π.property.1
    ν hν hr (unitaryTorusParameter ν e z) (unitaryTorusParameter_norm ν e z)
    (F z) (H z)).symm

/-- Actual compact restriction on the smooth submodule retains its complete
stabilizer covariance, including its possibly nontrivial coefficient action. -/
def productInducedSmoothFamilyRestriction :
    productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π ≃ₗ[ℂ]
      finiteSmoothEquivariantFamilies J (ProductInducedCompactPicture h K π.obj)
        (unitaryStabilizerTorusHom ν e (Quotient.mk _ π))
        (unitaryStabilizerCompactRepresentation ν h K hP hK hν hr π) :=
  (productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj).ofSubmodule' _

/-- Pairing smooth actual induced families gives a smooth scalar function,
without a topology or norm on the coefficient carrier. -/
theorem isSmooth_unitaryTorusProductForm_pairing
    (F H : productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π) :
    IsSmoothFiniteTorusFunction (fun z =>
      (unitaryTorusProductForm h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν e z).inner
        (F.val z) (H.val z)) := by
  have heq := funext (unitaryTorusProductForm_inner
    h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e F.val H.val)
  rw [heq]
  exact isSmoothFiniteTorusFunction_core_pairing
    (formalDegreeFixedProductCompactForm h hU hP K hK (compactFactorization K hPK)
      hG hδ π.obj hcof C hC μ hsq π.property.1).toInnerProductCore F.property.1 H.property.1

variable (η : Measure (J → Circle)) [IsFiniteMeasure η]

/-- Compactness and finite scalar smoothness prove convergence of the actual
inverse-degree fiber pairing on the parameter cover. -/
theorem integrable_unitaryTorusProductForm_pairing
    (F H : productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π) :
    Integrable (fun z =>
      (unitaryTorusProductForm h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν e z).inner
        (F.val z) (H.val z)) η :=
  BoundedContinuousFunction.integrable η
    (BoundedContinuousFunction.mkOfCompact
      ⟨_, (isSmooth_unitaryTorusProductForm_pairing
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e F H).continuous⟩)

variable [η.IsOpenPosMeasure]

/-- The positive cover-integral core on the actual smooth dependent inducing
families. Its fiber forms require no supplied positive inducing form. -/
@[instance_reducible]
def productInducedSmoothFamilyCore :
    InnerProductSpace.Core ℂ
      (productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π) :=
  coreComap
    (finiteSmoothEquivariantFamilyCore
      (unitaryStabilizerTorusHom ν e (Quotient.mk _ π))
      (unitaryStabilizerCompactRepresentation ν h K hP hK hν hr π)
      (formalDegreeFixedProductCompactForm h hU hP K hK (compactFactorization K hPK)
        hG hδ π.obj hcof C hC μ hsq π.property.1).toInnerProductCore η)
    (productInducedSmoothFamilyRestriction h hU hP K hK hPK π ν hν hr e).toLinearMap
    (productInducedSmoothFamilyRestriction h hU hP K hK hPK π ν hν hr e).injective

/-- The constructed positive core is the integral of the actual canonical
inverse-Schur-degree forms on the varying normalized product inductions. -/
theorem productInducedSmoothFamilyCore_inner_integral
    (F H : productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π) :
    (productInducedSmoothFamilyCore
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e η).inner F H =
      ∫ z, (unitaryTorusProductForm
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν e z).inner
          (F.val z) (H.val z) ∂η := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z =>
    (unitaryTorusProductForm_inner
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e F.val H.val z).symm

local instance productFamilySmoothTensorAddCommGroup :
    AddCommGroup
      (smoothFiniteTorusFunctions J ⊗[ℂ] ProductInducedCompactPicture h K π.obj) :=
  TensorProduct.addCommGroup

/-- The same positive integral core on the actual diagonal invariant tensor
model, by restriction of the existing finite smooth tensor form. -/
@[instance_reducible]
def productInducedSmoothInvariantTensorCore :
    InnerProductSpace.Core ℂ
      (productInducedSmoothTensorRepresentation ν e h K hP hK hν hr π).invariants :=
  coreComap
    (finiteSmoothTensorCore
      (formalDegreeFixedProductCompactForm h hU hP K hK (compactFactorization K hPK)
        hG hδ π.obj hcof C hC μ hsq π.property.1).toInnerProductCore η)
    (productInducedSmoothTensorRepresentation ν e h K hP hK hν hr π).invariants.subtype
    (Submodule.subtype_injective _)

/-- Evaluation followed by actual normalized extension preserves the entire
integrated form on the source's invariant tensor model. -/
theorem productInducedSmoothTensorFamilyEquiv_inner
    (t u : (productInducedSmoothTensorRepresentation ν e h K hP hK hν hr π).invariants) :
    (productInducedSmoothFamilyCore
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e η).inner
        (productInducedSmoothTensorFamilyEquiv ν e h K hP hK hν hr hU hPK π t)
        (productInducedSmoothTensorFamilyEquiv ν e h K hP hK hν hr hU hPK π u) =
      (productInducedSmoothInvariantTensorCore
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e η).inner t u := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z =>
    congrArg₂
      (formalDegreeFixedProductCompactForm h hU hP K hK (compactFactorization K hPK)
        hG hδ π.obj hcof C hC μ hsq π.property.1).inner
      (productInducedSmoothTensorFamilyEquiv_restriction
        ν e h K hP hK hν hr hU hPK π t z)
      (productInducedSmoothTensorFamilyEquiv_restriction
        ν e h K hP hK hν hr hU hPK π u z)

/-- Positive cover integration on actual coherent smooth sections over every
representative, through the proved faithful parameter pullback. -/
@[instance_reducible]
def productInducedSmoothOrbitCoverCore :
    InnerProductSpace.Core ℂ
      (productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :=
  coreComap
    (productInducedSmoothFamilyCore
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e η)
    (productInducedSmoothOrbitFamilyEquiv
      ν π e h hU K hP hK hν hr hPK).toLinearMap
    (productInducedSmoothOrbitFamilyEquiv
      ν π e h hU K hP hK hν hr hPK).injective

/-- The coherent-section form integrates their actual values at the literal
parameter representatives, with the same canonical degree normalization. -/
theorem productInducedSmoothOrbitCoverCore_inner_integral
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    (productInducedSmoothOrbitCoverCore
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e η).inner q r =
      ∫ z, (unitaryTorusProductForm
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν e z).inner
          (q.val (unitaryOrbitParameterRepresentative ν π e z))
          (r.val (unitaryOrbitParameterRepresentative ν π e z)) ∂η :=
  productInducedSmoothFamilyCore_inner_integral
    h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e η
    (productInducedSmoothOrbitFamilyEquiv ν π e h hU K hP hK hν hr hPK q)
    (productInducedSmoothOrbitFamilyEquiv ν π e h hU K hP hK hν hr hPK r)

/-- The source's concrete invariant tensor to coherent-section equivalence is
an isometry for these positive parameter-cover integrals. -/
theorem productInducedSmoothTensorOrbitEquiv_inner
    (t u : (productInducedSmoothTensorRepresentation ν e h K hP hK hν hr π).invariants) :
    (productInducedSmoothOrbitCoverCore
      h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e η).inner
        (productInducedSmoothTensorOrbitEquiv ν π e h hU K hP hK hν hr hPK t)
        (productInducedSmoothTensorOrbitEquiv ν π e h hU K hP hK hν hr hPK u) =
      (productInducedSmoothInvariantTensorCore
        h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e η).inner t u := by
  change (productInducedSmoothFamilyCore
    h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e η).inner
      ((productInducedSmoothOrbitFamilyEquiv ν π e h hU K hP hK hν hr hPK)
        ((productInducedSmoothOrbitFamilyEquiv ν π e h hU K hP hK hν hr hPK).symm
          (productInducedSmoothTensorFamilyEquiv ν e h K hP hK hν hr hU hPK π t)))
      ((productInducedSmoothOrbitFamilyEquiv ν π e h hU K hP hK hν hr hPK)
        ((productInducedSmoothOrbitFamilyEquiv ν π e h hU K hP hK hν hr hPK).symm
          (productInducedSmoothTensorFamilyEquiv ν e h K hP hK hν hr hU hPK π u))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact productInducedSmoothTensorFamilyEquiv_inner
    h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e η t u

end Langlands.Plancherel
