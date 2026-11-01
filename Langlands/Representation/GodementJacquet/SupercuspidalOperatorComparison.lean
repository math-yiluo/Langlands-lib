import Langlands.Representation.GodementJacquet.SupercuspidalMonomialOutputs
import Langlands.Representation.Smooth.Schur.Proof
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Descending the Fourier-regular operator comparison -/

noncomputable section

namespace Langlands.GodementJacquet

universe uI uV

variable {I : Type uI} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Finite complex linear combinations of all outputs of an operator family. -/
def operatorFamilyLinearCombination (A : I → Module.End ℂ V) :
    ((I × V) →₀ ℂ) →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ (fun iv : I × V => A iv.1 iv.2)

@[simp] theorem operatorFamilyLinearCombination_single
    (A : I → Module.End ℂ V) (i : I) (v : V) :
    operatorFamilyLinearCombination A (Finsupp.single (i, v) 1) = A i v := by
  simp [operatorFamilyLinearCombination]

/-- The cross identity preserves every finite linear relation among outputs
when the original family has zero common kernel. -/
theorem operatorFamilyLinearCombination_ker_le
    (A D : I → Module.End ℂ V)
    (hsep : ∀ v : V, (∀ i : I, A i v = 0) → v = 0)
    (hcross : ∀ i j : I, A i * D j = D i * A j) :
    LinearMap.ker (operatorFamilyLinearCombination A) ≤
      LinearMap.ker (operatorFamilyLinearCombination D) := by
  have hex (i : I) :
      (A i).comp (operatorFamilyLinearCombination D) =
        (D i).comp (operatorFamilyLinearCombination A) := by
    apply Finsupp.lhom_ext
    intro j c
    simp only [LinearMap.comp_apply, operatorFamilyLinearCombination,
      Finsupp.linearCombination_single, map_smul]
    exact congrArg (fun f : Module.End ℂ V => c • f j.2) (hcross i j.1)
  intro x hx
  apply hsep
  intro i
  have h := congrArg (fun f => f x) (hex i)
  change A i (operatorFamilyLinearCombination D x) =
    D i (operatorFamilyLinearCombination A x) at h
  rw [show operatorFamilyLinearCombination A x = 0 from hx, map_zero] at h
  exact h

/-- Descend the second family through the first family's finite-output
presentation of the whole carrier. -/
def operatorFamilyComparison
    (A D : I → Module.End ℂ V)
    (hsurj : Function.Surjective (operatorFamilyLinearCombination A))
    (hsep : ∀ v : V, (∀ i : I, A i v = 0) → v = 0)
    (hcross : ∀ i j : I, A i * D j = D i * A j) : Module.End ℂ V :=
  ((LinearMap.ker (operatorFamilyLinearCombination A)).liftQ
      (operatorFamilyLinearCombination D)
      (operatorFamilyLinearCombination_ker_le A D hsep hcross)).comp
    ((operatorFamilyLinearCombination A).quotKerEquivOfSurjective hsurj).symm.toLinearMap

theorem operatorFamilyComparison_apply_output
    (A D : I → Module.End ℂ V)
    (hsurj : Function.Surjective (operatorFamilyLinearCombination A))
    (hsep : ∀ v : V, (∀ i : I, A i v = 0) → v = 0)
    (hcross : ∀ i j : I, A i * D j = D i * A j) (i : I) (v : V) :
    operatorFamilyComparison A D hsurj hsep hcross (A i v) = D i v := by
  rw [← operatorFamilyLinearCombination_single A i v]
  dsimp only [operatorFamilyComparison, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply,
    operatorFamilyLinearCombination_single]

/-- The descended comparison commutes with every operator in the first
family; the output-presentation surjectivity extends the cross identity. -/
theorem operatorFamilyComparison_commutes
    (A D : I → Module.End ℂ V)
    (hsurj : Function.Surjective (operatorFamilyLinearCombination A))
    (hsep : ∀ v : V, (∀ i : I, A i v = 0) → v = 0)
    (hcross : ∀ i j : I, A i * D j = D i * A j) (i : I) :
    A i * operatorFamilyComparison A D hsurj hsep hcross =
      operatorFamilyComparison A D hsurj hsep hcross * A i := by
  let f := operatorFamilyComparison A D hsurj hsep hcross
  have hf : f.comp (operatorFamilyLinearCombination A) =
      operatorFamilyLinearCombination D := by
    apply Finsupp.lhom_ext
    intro j c
    simp only [LinearMap.comp_apply, operatorFamilyLinearCombination,
      Finsupp.linearCombination_single, map_smul]
    exact congrArg (fun v : V => c • v)
      (operatorFamilyComparison_apply_output A D hsurj hsep hcross j.1 j.2)
  apply LinearMap.ext
  intro v
  obtain ⟨x, rfl⟩ := hsurj v
  change A i (f (operatorFamilyLinearCombination A x)) =
    f (A i (operatorFamilyLinearCombination A x))
  have hfx : f (operatorFamilyLinearCombination A x) =
      operatorFamilyLinearCombination D x :=
    congrArg (fun g => g x) hf
  rw [hfx]
  have hex : (A i).comp (operatorFamilyLinearCombination D) =
      (D i).comp (operatorFamilyLinearCombination A) := by
    apply Finsupp.lhom_ext
    intro j c
    simp only [LinearMap.comp_apply, operatorFamilyLinearCombination,
      Finsupp.linearCombination_single, map_smul]
    exact congrArg (fun g : Module.End ℂ V => c • g j.2) (hcross i j.1)
  rw [show A i (operatorFamilyLinearCombination D x) =
      D i (operatorFamilyLinearCombination A x) from congrArg (fun g => g x) hex]
  exact (operatorFamilyComparison_apply_output A D hsurj hsep hcross i
    (operatorFamilyLinearCombination A x)).symm

namespace Padic

open MeasureTheory HarmonicAnalysis RankinSelberg

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance comparisonTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance comparisonValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance comparisonLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance comparisonT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance comparisonDisconnected : TotallyDisconnectedSpace F.Carrier :=
  (padicLatticeGeometry F F.canonicalTopologicalData).1
local instance comparisonMeasurable : MeasurableSpace F.Carrier := borel _
local instance comparisonBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance comparisonGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance comparisonGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {m : ℕ}

/-- Restrict the actual compact zeta operator to Fourier-regular tests. -/
def fourierRegularMatrixZetaOperator
    (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hρ : IsSmooth ρ)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (s : ℂ) :
    fourierRegularMatrixTests (m + 1) ψ ν hsd →ₗ[ℂ] Module.End ℂ V :=
  (regularMatrixZetaOperator F ρ hρ s).comp
    (Submodule.inclusion (show fourierRegularMatrixTests (m + 1) ψ ν hsd ≤
      regularMatrixTests (K := F.Carrier) (m + 1) from inf_le_left))

@[simp] theorem fourierRegularMatrixZetaOperator_apply
    (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hρ : IsSmooth ρ)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (s : ℂ)
    (Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd) :
    fourierRegularMatrixZetaOperator F ρ hρ ψ ν hsd s Φ =
      regularMatrixZetaOperator F ρ hρ s ⟨Φ.val, Φ.property.1⟩ := rfl

/-- The Fourier-regular operator family has zero common kernel at every
exponent, by the nonzero constant-output witness on a chosen nonzero input. -/
theorem fourierRegularMatrixZetaOperator_separates
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (s : ℂ) (v : V)
    (hv : ∀ Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd,
      fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ v = 0) :
    v = 0 := by
  by_contra hv0
  obtain ⟨Φ, u, hu, hΦ⟩ :=
    exists_fourierRegular_constant_output F hm ρ hρ ψ ν hsd v hv0
  exact hu ((hΦ s).symm.trans (hv Φ))

/-- At every exponent the finite-output presentation is surjective, because
the monomial outputs on one nonzero input span and spectral powers are nonzero. -/
theorem fourierRegularMatrixZetaOperator_output_surjective
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (s : ℂ) :
    Function.Surjective (operatorFamilyLinearCombination
      (fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s)) := by
  let := hi
  let : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear (m + 1) F.Carrier)) ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← span_fourierRegularMonomialOutputs_eq_top F hm ρ hρ hi ψ ν hsd v hv]
  apply Submodule.span_le.mpr
  intro u hu
  obtain ⟨Φ, k, hΦ⟩ := hu
  have hout : fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ v ∈
      LinearMap.range (operatorFamilyLinearCombination
        (fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s)) :=
    ⟨Finsupp.single (Φ, v) 1, operatorFamilyLinearCombination_single _ _ _⟩
  change regularMatrixZetaOperator F ρ hρ.1.1 s ⟨Φ.val, Φ.property.1⟩ v ∈ _ at hout
  rw [hΦ s] at hout
  exact (Submodule.smul_mem_iff _ (zpow_ne_zero k (spectralPoint_ne_zero_of_pos
    (Nat.zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one) s))).mp hout

/-- A comparison that commutes with all Fourier-regular test operators
commutes with the representation, by left translation and output spanning. -/
theorem intertwining_of_commutes_fourierRegularMatrixZetaOperator
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (s : ℂ) (f : Module.End ℂ V)
    (hf : ∀ Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd,
      fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ * f =
        f * fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ)
    (a : GeneralLinear (m + 1) F.Carrier) :
    f.comp (ρ a) = (ρ a).comp f := by
  let A := fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s
  have ht (Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd) (w : V) :
      A (fourierRegularMatrixTranslate F ψ ν hsd a⁻¹ 1 Φ) w =
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) a s •
          ρ a (A Φ w) :=
    regularMatrixZetaOperator_leftTranslate F ρ hρ.1.1 a s
      ⟨Φ.val, Φ.property.1⟩ w
  have hOn (Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd) (w : V) :
      f (ρ a (A Φ w)) = ρ a (f (A Φ w)) := by
    have h := congrArg (fun L : Module.End ℂ V => L w)
      (hf (fourierRegularMatrixTranslate F ψ ν hsd a⁻¹ 1 Φ))
    change A (fourierRegularMatrixTranslate F ψ ν hsd a⁻¹ 1 Φ) (f w) =
      f (A (fourierRegularMatrixTranslate F ψ ν hsd a⁻¹ 1 Φ) w) at h
    rw [ht, ht, map_smul] at h
    have hc := smul_right_injective V
      (determinantWeight_ne_zero (normalizedAbsoluteValue F.canonicalTopologicalData) a s) h
    have hfw : A Φ (f w) = f (A Φ w) :=
      congrArg (fun L : Module.End ℂ V => L w) (hf Φ)
    rw [hfw] at hc
    exact hc.symm
  have hcomb : (f.comp (ρ a)).comp (operatorFamilyLinearCombination A) =
      ((ρ a).comp f).comp (operatorFamilyLinearCombination A) := by
    apply Finsupp.lhom_ext
    intro j c
    simp only [LinearMap.comp_apply, operatorFamilyLinearCombination,
      Finsupp.linearCombination_single, map_smul]
    exact congrArg (fun w : V => c • w) (hOn j.1 j.2)
  apply LinearMap.ext
  intro v
  obtain ⟨x, rfl⟩ :=
    fourierRegularMatrixZetaOperator_output_surjective F hm ρ hρ hi ψ ν hsd s v
  exact congrArg (fun L => L x) hcomb

/-- For the actual Fourier-regular operator family, the cross identity
forces any comparison family to be a single scalar multiple at each exponent. -/
theorem exists_scalar_of_fourierRegularMatrixZetaOperator_cross
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (s : ℂ)
    (D : fourierRegularMatrixTests (m + 1) ψ ν hsd → Module.End ℂ V)
    (hcross : ∀ Φ Ψ : fourierRegularMatrixTests (m + 1) ψ ν hsd,
      fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ * D Ψ =
        D Φ * fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Ψ) :
    ∃ c : ℂ, ∀ Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd,
      D Φ = c • fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s Φ := by
  let A := fourierRegularMatrixZetaOperator F ρ hρ.1.1 ψ ν hsd s
  have hsurj := fourierRegularMatrixZetaOperator_output_surjective F hm ρ hρ hi ψ ν hsd s
  have hsep := fourierRegularMatrixZetaOperator_separates F hm ρ hρ ψ ν hsd s
  let f := operatorFamilyComparison A D hsurj hsep hcross
  let T : ρ.IntertwiningMap ρ :=
    { toLinearMap := f
      isIntertwining' := fun a =>
        intertwining_of_commutes_fourierRegularMatrixZetaOperator F hm ρ hρ hi ψ ν hsd s f
          (operatorFamilyComparison_commutes A D hsurj hsep hcross) a }
  obtain ⟨c, hc, _⟩ := admissibleSchur_scalarEndomorphism ρ hρ.1 hi T
  refine ⟨c, fun Φ => ?_⟩
  apply LinearMap.ext
  intro v
  change D Φ v = c • (A Φ v)
  rw [← operatorFamilyComparison_apply_output A D hsurj hsep hcross Φ v]
  exact congrArg (fun L : ρ.IntertwiningMap ρ => L (A Φ v)) hc

end Padic

end Langlands.GodementJacquet
