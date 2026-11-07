import Langlands.LinearAlgebra.FiniteConeBoundary
import Langlands.LinearAlgebra.RootFaceReflection
import Langlands.Geometry.Building.RealTorusDuality
import Mathlib.Tactic

/-! # Integral supporting cocharacters for finite character cones -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme.RealTorusSpace

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {ι : Type*} [Fintype ι]

/-- A finite nonnegative character combination outside the strictly positive
combination cone admits an integral supporting cocharacter. Every generator
with positive coefficient is annihilated, and some generator has positive pairing. -/
theorem exists_boundaryCocharacter (hT : IsSplitTorus T.toGrp)
    (α : ι → characterLattice T) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hstrict : ¬ ∃ d : ι → ℝ, (∀ i, 0 < d i) ∧
      (∑ i, d i • ((1 : ℝ) ⊗ₜ[ℤ] α i)) =
        ∑ i, c i • ((1 : ℝ) ⊗ₜ[ℤ] α i)) :
    ∃ μ : cocharacterLattice T,
      (∀ i, 0 ≤ latticePairing T (α i) μ) ∧
      (∃ i, 0 < latticePairing T (α i) μ) ∧
      (∀ i, 0 < c i → latticePairing T (α i) μ = 0) := by
  classical
  obtain ⟨f, hfzero, hfnonneg, hfpos⟩ :=
    Langlands.LinearAlgebra.FiniteConeBoundary.exists_supporting_functional
      (fun i => (1 : ℝ) ⊗ₜ[ℤ] α i) c hc hstrict
  have hp := isPerfPair_of_isSplitTorus hT
  obtain ⟨g, hg⟩ := hp.bijective_right.surjective f
  have heval (i : ι) : eval T (α i) g = f ((1 : ℝ) ⊗ₜ[ℤ] α i) := by
    rw [eval_eq_pair]
    exact LinearMap.congr_fun hg ((1 : ℝ) ⊗ₜ[ℤ] α i)
  have hnonneg (i : ι) : 0 ≤ eval T (α i) g := by
    rw [heval]
    exact hfnonneg i
  have hzero (i : ι) (hi : 0 < c i) : eval T (α i) g = 0 := by
    have hsum : ∑ j, c j * eval T (α j) g = 0 := by
      simp_rw [heval]
      simpa only [map_sum, map_smul, smul_eq_mul] using hfzero
    have hle := Finset.single_le_sum
      (f := fun j => c j * eval T (α j) g)
      (fun j _ => mul_nonneg (hc j) (hnonneg j)) (Finset.mem_univ i)
    rw [hsum] at hle
    exact le_antisymm (by nlinarith) (hnonneg i)
  let φ : ι × Bool → cocharacterLattice T →ₗ[ℤ] ℤ :=
    fun j => if j.2 then latticePairing T (α j.1) else -latticePairing T (α j.1)
  let ψ : ι × Bool → V T →ₗ[ℝ] ℝ :=
    fun j => if j.2 then eval T (α j.1) else -eval T (α j.1)
  have hψ : ∀ j (t : ℝ) (n : cocharacterLattice T),
      ψ j (t ⊗ₜ[ℤ] n) = t * (φ j n : ℝ) := by
    rintro ⟨i, b⟩ t n
    cases b <;> simp [φ, ψ, eval_tmul]
  obtain ⟨μ, hμ⟩ :=
    Langlands.LinearAlgebra.RootFaceCone.exists_int_sign_realization
      Finset.univ φ ψ hψ g
  have hpos (i : ι) : 0 < latticePairing T (α i) μ ↔ 0 < eval T (α i) g := by
    simpa [φ, ψ] using hμ (i, true) (Finset.mem_univ _)
  have hneg (i : ι) : latticePairing T (α i) μ < 0 ↔ eval T (α i) g < 0 := by
    simpa [φ, ψ] using hμ (i, false) (Finset.mem_univ _)
  refine ⟨μ, ?_, ?_, ?_⟩
  · intro i
    exact le_of_not_gt fun h => (not_lt_of_ge (hnonneg i)) ((hneg i).mp h)
  · obtain ⟨i, hi⟩ := hfpos
    exact ⟨i, (hpos i).mpr (by rwa [heval])⟩
  · intro i hi
    have hz := hzero i hi
    apply le_antisymm
    · exact le_of_not_gt fun h => by
        have := (hpos i).mp h
        linarith
    · exact le_of_not_gt fun h => (not_lt_of_ge (hnonneg i)) ((hneg i).mp h)

/-- A chosen genuine integral cocharacter supporting the finite character cone
at the supplied boundary combination. -/
def boundaryCocharacter (hT : IsSplitTorus T.toGrp)
    (α : ι → characterLattice T) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hstrict : ¬ ∃ d : ι → ℝ, (∀ i, 0 < d i) ∧
      (∑ i, d i • ((1 : ℝ) ⊗ₜ[ℤ] α i)) =
        ∑ i, c i • ((1 : ℝ) ⊗ₜ[ℤ] α i)) : cocharacterLattice T :=
  (exists_boundaryCocharacter hT α c hc hstrict).choose

theorem boundaryCocharacter_spec (hT : IsSplitTorus T.toGrp)
    (α : ι → characterLattice T) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hstrict : ¬ ∃ d : ι → ℝ, (∀ i, 0 < d i) ∧
      (∑ i, d i • ((1 : ℝ) ⊗ₜ[ℤ] α i)) =
        ∑ i, c i • ((1 : ℝ) ⊗ₜ[ℤ] α i)) :
    (∀ i, 0 ≤ latticePairing T (α i) (boundaryCocharacter hT α c hc hstrict)) ∧
    (∃ i, 0 < latticePairing T (α i) (boundaryCocharacter hT α c hc hstrict)) ∧
    (∀ i, 0 < c i → latticePairing T (α i) (boundaryCocharacter hT α c hc hstrict) = 0) :=
  (exists_boundaryCocharacter hT α c hc hstrict).choose_spec

end Langlands.GroupScheme.RealTorusSpace
