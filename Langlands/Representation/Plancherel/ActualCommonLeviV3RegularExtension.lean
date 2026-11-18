import Langlands.Representation.Plancherel.ActualCommonLeviCompactAction
import Langlands.Representation.Plancherel.ActualCommonLeviV3GermProof

/-! # Actual common-Levi intertwining maps from regular germs -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualCommonLeviV3

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviRationalTensor
open UnramifiedOperatorFamily

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicCommonLeviContinuation.radicalMeasurable
  DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable
  DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
  (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)

local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)
local notation "V₀" => compactFiber χ K ψ hψ A
local notation "V₁" => compactFiber χ K ψ' hψ' A
local notation "G₀" => RationalPoint F G.X
local notation "D" => genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
local notation "J" => compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
local notation "ρ₀" => compactTensorRepresentation χ hG K hK ψ hψ hψK A
local notation "ρ₁" => compactTensorRepresentation χ hG K hK ψ' hψ' hψ'K A
local notation "E₀" => compactTensorRepresentationEquiv χ hG K hK ψ hψ hψK A
local notation "E₁" => compactTensorRepresentationEquiv χ hG K hK ψ' hψ' hψ'K A
local notation "R" => RegularGermAt χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q
local notation "L" => regularGermValue χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q

/-- The actual generic compact comparison intertwines the full product actions. -/
theorem compactComparison_intertwines (z : D) (x : G₀ × G₀) :
    (J z).comp (ρ₀ z.val x) = (ρ₁ z.val x).comp (J z) := by
  let e₀ := E₀ z.val
  let e₁ := E₁ z.val
  let T := genericComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z
  let Tc : (ρ₀ z.val).IntertwiningMap (ρ₁ z.val) :=
    e₁.toIntertwiningMap.comp (T.comp e₀.symm.toIntertwiningMap)
  have hTc : Tc.toLinearMap = J z := by
    apply LinearMap.ext
    intro v
    have hs := compactComparison_square χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q z
      (e₀.symm v)
    change e₁ (T (e₀.symm v)) = J z (e₀ (e₀.symm v)) at hs
    rw [e₀.apply_symm_apply] at hs
    exact hs
  calc
    (J z).comp (ρ₀ z.val x) = Tc.toLinearMap.comp (ρ₀ z.val x) :=
      congrArg (fun M : V₀ →ₗ[ℂ] V₁ => M.comp (ρ₀ z.val x)) hTc.symm
    _ = (ρ₁ z.val x).comp Tc.toLinearMap := Tc.isIntertwining' x
    _ = (ρ₁ z.val x).comp (J z) :=
      congrArg (fun M : V₀ →ₗ[ℂ] V₁ => (ρ₁ z.val x).comp M) hTc

/-- On the whole open set of a regular representative, its numerator
intertwines the two full actions. -/
theorem IsLocalRepresentative.intertwines
    (hD : Dense D) {U : Set X} {N : X → V₀ →ₗ[ℂ] V₁}
    {b : unramifiedRegularFunctions (normCharacters χ)}
    (h : IsLocalRepresentative χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q U N b)
    (z : X) (hz : z ∈ U) (x : G₀ × G₀) :
    (N z).comp (ρ₀ z x) = (ρ₁ z x).comp (N z) := by
  apply LinearMap.ext
  intro v
  let f : X → V₁ := fun w => N w (ρ₀ w x v) - ρ₁ w x (N w v)
  have h₀ : IsPolynomialOperatorOn (Set.univ : Set X) (fun w => ρ₀ w.val x) :=
    compactTensorRepresentation_polynomial χ hG K hK ψ hψ hψK A x
  have h₁ : IsPolynomialOperatorOn (Set.univ : Set X) (fun w => ρ₁ w.val x) :=
    compactTensorRepresentation_polynomial χ hG K hK ψ' hψ' hψ'K A x
  have hN : IsPolynomialOperatorOn (Set.univ : Set X) (fun w => N w.val) := h.2.1
  have hpoly : IsPolynomialOn (Set.univ : Set X) (fun w => f w.val) :=
    ((hN.comp h₀) v).sub ((h₁.comp hN) v)
  have hzero := polynomial_eq_zero_on_open_of_dense hD h.1 f hpoly (by
    intro w hwD hwU
    let wD : D := ⟨w, hwD⟩
    have hclear (a : V₀) : N w a = b.val w • J wD a :=
      congrArg (fun M : V₀ →ₗ[ℂ] V₁ => M a) (h.2.2.2 wD hwU)
    have he : J wD (ρ₀ w x v) = ρ₁ w x (J wD v) :=
      congrArg (fun M : V₀ →ₗ[ℂ] V₁ => M v)
        (compactComparison_intertwines χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q wD x)
    change N w (ρ₀ w x v) - ρ₁ w x (N w v) = 0
    simp only [hclear, map_smul, he, sub_self])
  exact sub_eq_zero.mp (hzero z hz)

/-- The value of a regular germ intertwines the actual full product actions
on the compact carriers. -/
theorem RegularGermAt.intertwines (hD : Dense D) {z : X} {M : V₀ →ₗ[ℂ] V₁}
    (hM : R z M) (x : G₀ × G₀) :
    M.comp (ρ₀ z x) = (ρ₁ z x).comp M := by
  obtain ⟨U, N, b, hz, hrep, hvalue⟩ := hM
  let c : ℂ := (b.val z)⁻¹
  have hpoint (v : V₀) : M v = c • N z v :=
    congrArg (fun B : V₀ →ₗ[ℂ] V₁ => B v) hvalue
  have hcomm := hrep.intertwines χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q hD z hz x
  apply LinearMap.ext
  intro v
  calc
    M (ρ₀ z x v) = c • N z (ρ₀ z x v) := hpoint (ρ₀ z x v)
    _ = c • ρ₁ z x (N z v) :=
      congrArg (fun w : V₁ => c • w) (congrArg (fun B : V₀ →ₗ[ℂ] V₁ => B v) hcomm)
    _ = ρ₁ z x (c • N z v) := ((ρ₁ z x).map_smul c (N z v)).symm
    _ = ρ₁ z x (M v) := congrArg (fun w : V₁ => ρ₁ z x w) (hpoint v).symm

variable
  (hD : Dense (genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q))
  (hg : ∀ z : unitaryUnramifiedCharacters (normCharacters χ),
    ∃ M : compactFiber χ K ψ hψ A →ₗ[ℂ] compactFiber χ K ψ' hψ' A,
      RegularGermAt χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q (unitaryParameter χ z) M)

/-- Choose the regular value at every unitary parameter and transport its
intertwining map back to the actual coefficient fibers. -/
def comparisonFamilyOfRegularGerms : UnitaryComparisonFamily χ A ψ hψ ψ' hψ' := fun z =>
  let w := unitaryParameter χ z
  let T : (ρ₀ w).IntertwiningMap (ρ₁ w) :=
    ⟨L w (hg z), (regularGermValue_spec χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q w
      (hg z)).intertwines χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q hD⟩
  (E₁ w).symm.toIntertwiningMap.comp (T.comp (E₀ w).toIntertwiningMap)

local notation "T" => comparisonFamilyOfRegularGerms χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q hD hg

private theorem compact_transport_cancel
    {B₀ B₁ W₀ W₁ : Type*}
    [AddCommGroup B₀] [Module ℂ B₀] [AddCommGroup B₁] [Module ℂ B₁]
    [AddCommGroup W₀] [Module ℂ W₀] [AddCommGroup W₁] [Module ℂ W₁]
    (e₀ : B₀ ≃ₗ[ℂ] W₀) (e₁ : B₁ ≃ₗ[ℂ] W₁) (M : W₀ →ₗ[ℂ] W₁) :
    e₁.toLinearMap.comp
      ((e₁.symm.toLinearMap.comp (M.comp e₀.toLinearMap)).comp e₀.symm.toLinearMap) = M := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]

/-- The compact value of the actual extension is exactly the chosen germ value. -/
theorem compactValue_comparisonFamilyOfRegularGerms (z : Xu) :
    compactValue χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K T z =
      L (unitaryParameter χ z) (hg z) := by
  let w := unitaryParameter χ z
  exact compact_transport_cancel (E₀ w).toLinearEquiv (E₁ w).toLinearEquiv (L w (hg z))

/-- A representative at a given point works for the extended family at every
unitary point of the same open set, by uniqueness of the rational germ. -/
theorem comparisonFamilyOfRegularGerms_isRegular :
    IsRegularUnitaryExtension χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q T := by
  intro z
  obtain ⟨U, N, b, hz, hrep, _⟩ :=
    regularGermValue_spec χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q (unitaryParameter χ z) (hg z)
  refine ⟨U, N, b, hz, hrep, fun w hw => ?_⟩
  exact (compactValue_comparisonFamilyOfRegularGerms χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K
    p q hD hg w).trans
    (regularGermValue_eq χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q hD
      (unitaryParameter χ w) (hg w) ⟨U, N, b, hw, hrep, rfl⟩)

end Langlands.Plancherel.ActualCommonLeviV3
