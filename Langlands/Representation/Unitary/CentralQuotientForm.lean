import Langlands.Analysis.Local.NormalSubgroupHaarModulus
import Langlands.Representation.Unitary.SquareIntegrableProof
import Mathlib.MeasureTheory.Group.ModularCharacter

/-! # Positive forms on square-integrable representations of unimodular groups -/

noncomputable section

namespace Langlands

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

universe uG uV

namespace Haar

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The continuous automorphism given by conjugation by the specified element. -/
def conjugationContinuousMulEquiv (g : G) : G ≃ₜ* G where
  toFun x := g * x * g⁻¹
  invFun x := g⁻¹ * x * g
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_mul' x y := by simp [mul_assoc]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

variable [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- A trivial ambient modular character makes every regular Haar measure
right invariant. -/
theorem isMulRightInvariant_of_modularCharacter_eq_one
    (hmod : ∀ g : G, modularCharacter g = 1)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    μ.IsMulRightInvariant := by
  constructor
  intro g
  have : (μ.map (fun x => x * g)).Regular := Regular.map (Homeomorph.mulRight g)
  rw [isMulLeftInvariant_eq_smul_of_regular (μ.map (fun x => x * g)) μ,
    ← modularCharacterFun_eq_haarScalarFactor μ g,
    show modularCharacterFun g = 1 from hmod g, one_smul]

omit [LocallyCompactSpace G] in
private theorem map_conjugation (μ : Measure G) [μ.IsMulLeftInvariant] (g : G) :
    μ.map (conjugationContinuousMulEquiv g) = μ.map (fun x => x * g⁻¹) := by
  have hc : (conjugationContinuousMulEquiv g : G → G) =
      (fun x => x * g⁻¹) ∘ (fun x => g * x) := rfl
  rw [hc, ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _),
    map_mul_left_eq_self]

/-- Inner automorphisms of a unimodular group preserve Haar measure. -/
theorem mulEquivHaarChar_conjugation_eq_one
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant]
    (g : G) :
    mulEquivHaarChar (conjugationContinuousMulEquiv g) = 1 := by
  rw [mulEquivHaarChar_eq μ]
  simp only [map_conjugation, map_mul_right_eq_self, haarScalarFactor_self]

/-- Trivial Haar modulus for every inner automorphism gives right invariance
of every regular left Haar measure. -/
theorem isMulRightInvariant_of_conjugationHaarChar_eq_one
    (hconj : ∀ g : G, mulEquivHaarChar (conjugationContinuousMulEquiv g) = 1)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    μ.IsMulRightInvariant := by
  constructor
  intro g
  have h := mulEquivHaarChar_smul_map μ (conjugationContinuousMulEquiv g⁻¹)
  rw [hconj, one_smul, map_conjugation, inv_inv] at h
  exact h

variable [T2Space G]

/-- The full central quotient of a unimodular locally compact Hausdorff group
is unimodular. No second-countability assumption is required. -/
theorem centralQuotient_isMulRightInvariant
    (hmod : ∀ g : G, modularCharacter g = 1)
    [MeasurableSpace (G ⧸ Subgroup.center G)]
    [BorelSpace (G ⧸ Subgroup.center G)]
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.Regular] :
    μ.IsMulRightInvariant := by
  have hZ : IsClosed (Subgroup.center G : Set G) := by
    simpa only [Set.centralizer_univ, Subgroup.coe_center] using
      (Set.isClosed_centralizer (Set.univ : Set G))
  have : LocallyCompactSpace (Subgroup.center G) := hZ.locallyCompactSpace
  let : MeasurableSpace (Subgroup.center G) := borel _
  have : BorelSpace (Subgroup.center G) := ⟨rfl⟩
  let μG : Measure G := haar
  let μZ : Measure (Subgroup.center G) := haar
  have : μZ.IsMulRightInvariant := by
    constructor
    intro z
    have hc : (fun x : Subgroup.center G => x * z) = (fun x => z * x) := by
      funext x
      exact Subtype.ext (Subgroup.mem_center_iff.mp z.property x)
    rw [hc, map_mul_left_eq_self]
  have : μG.IsMulRightInvariant :=
    isMulRightInvariant_of_modularCharacter_eq_one hmod μG
  apply isMulRightInvariant_of_conjugationHaarChar_eq_one _ μ
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    let α := conjugationContinuousMulEquiv g
    have hα : ∀ x : G, α x ∈ Subgroup.center G ↔ x ∈ Subgroup.center G := by
      intro x
      constructor
      · intro hx
        have hcomm := (Subgroup.mem_center_iff.mp hx g)
        have hfix : α x = x := by
          change g * (g * x * g⁻¹) = (g * x * g⁻¹) * g at hcomm
          simpa [α, conjugationContinuousMulEquiv, mul_assoc] using
            congrArg (fun y => g⁻¹ * y) hcomm
        rwa [hfix] at hx
      · intro hx
        have hcomm := Subgroup.mem_center_iff.mp hx g
        change g * x * g⁻¹ ∈ Subgroup.center G
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
        exact hx
    have hαZ : QuotientIntegration.subgroupAutomorphism (Subgroup.center G) α hα =
        ContinuousMulEquiv.refl (Subgroup.center G) := by
      ext z
      have hcomm := Subgroup.mem_center_iff.mp z.property g
      change g * (z : G) * g⁻¹ = z
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hαQ : QuotientIntegration.quotientGroupAutomorphism
        (Subgroup.center G) α hα =
        conjugationContinuousMulEquiv (g : G ⧸ Subgroup.center G) := by
      ext x
      induction x using QuotientGroup.induction_on with
      | H x => rfl
    have h := QuotientIntegration.mulEquivHaarChar_eq_mul_quotientGroupAutomorphism
      (Subgroup.center G) hZ μG μZ α hα
    dsimp only at h
    rw [show mulEquivHaarChar α = 1 from
      mulEquivHaarChar_conjugation_eq_one μG g, hαZ,
      mulEquivHaarChar_refl (G := Subgroup.center G),
      one_mul, hαQ] at h
    exact h.symm

end Haar

namespace UnitaryCentralCharacter

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

/-- The coefficient-integral positive form needs only ambient unimodularity;
right invariance of the full central quotient is derived. -/
def unimodularCoefficientProductForm (c : UnitaryCentralCharacter ρ)
    (hmod : ∀ g : G, modularCharacter g = 1)
    (hρ : IsSmooth ρ) (hirr : Representation.IsIrreducible ρ)
    (ℓ : Module.Dual ℂ V) (hℓ : ℓ ≠ 0)
    [MeasurableSpace (G ⧸ Subgroup.center G)]
    [BorelSpace (G ⧸ Subgroup.center G)]
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsHaarMeasure] [μ.Regular]
    (hL2 : ∀ v, MemLp (c.coefficientNorm ℓ v) 2 μ) :
    InvariantPositiveForm ρ := by
  let : MeasurableSpace G := borel _
  have : BorelSpace G := ⟨rfl⟩
  have : μ.IsMulRightInvariant := Haar.centralQuotient_isMulRightInvariant hmod μ
  exact c.coefficientProductForm hρ hirr ℓ hℓ μ hL2

end UnitaryCentralCharacter

end Langlands
