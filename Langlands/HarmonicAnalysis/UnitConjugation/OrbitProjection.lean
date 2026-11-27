import Langlands.HarmonicAnalysis.UnitConjugation.InvariantDistribution
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! # Projection estimates for an almost fixed orbit of additive cosets -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Set

variable {R : Type*} [NormedRing R]

/-- The preimage in the algebra of the conjugacy orbit of `X + L` under `K`,
when conjugation by `K` preserves `L`. -/
def conjugationCosetOrbit (K : Subgroup Rˣ) (L : AddSubgroup R) (X : R) : Set R :=
  {Y | ∃ k ∈ K, ∃ l ∈ L, Y = conjugationHomeomorph k X + l}

private theorem conjugation_add (k : Rˣ) (X Y : R) :
    conjugationHomeomorph k (X + Y) = conjugationHomeomorph k X + conjugationHomeomorph k Y := by
  simp only [conjugationHomeomorph_apply, mul_add, add_mul]

/-- Every point of a conjugation orbit of cosets can serve as its representative. -/
theorem conjugationCosetOrbit_eq_of_mem {K : Subgroup Rˣ} {L : AddSubgroup R}
    (hKL : ∀ k ∈ K, ∀ l ∈ L, conjugationHomeomorph k l ∈ L)
    {X X₀ : R} (hX₀ : X₀ ∈ conjugationCosetOrbit K L X) :
    conjugationCosetOrbit K L X₀ = conjugationCosetOrbit K L X := by
  obtain ⟨k₀, hk₀, l₀, hl₀, rfl⟩ := hX₀
  ext Y
  constructor
  · rintro ⟨k, hk, l, hl, rfl⟩
    refine ⟨k * k₀, K.mul_mem hk hk₀, conjugationHomeomorph k l₀ + l,
      L.add_mem (hKL k hk l₀ hl₀) hl, ?_⟩
    rw [conjugation_add, conjugationHomeomorph_mul, add_assoc]
  · rintro ⟨k, hk, l, hl, rfl⟩
    have hk' : k * k₀⁻¹ ∈ K := K.mul_mem hk (K.inv_mem hk₀)
    refine ⟨k * k₀⁻¹, hk', l - conjugationHomeomorph (k * k₀⁻¹) l₀,
      L.sub_mem hl (hKL _ hk' l₀ hl₀), ?_⟩
    rw [conjugation_add, ← conjugationHomeomorph_mul, inv_mul_cancel_right]
    abel

variable {F : Type*} [NontriviallyNormedField F] [NormedAlgebra F R] [IsUltrametricDist R]

/-- Estimates for an orbit of additive cosets meeting its image under `β`. The projection error
is controlled by the maximum of the lattice bound and the displacement of the small conjugators.
The hypothesis on `β` bounds the transverse projection by the displacement under `β`. -/
def AlmostFixedOrbitProjectionStatement [IsUltrametricDist R] (K : Subgroup Rˣ) (L : AddSubgroup R) (X : R)
    (p : R →L[F] R) (β : R → R) (a δ C : ℝ) : Prop :=
  (∀ k ∈ K, ∀ l ∈ L, conjugationHomeomorph k l ∈ L) →
  (∀ l ∈ L, ‖l‖ ≤ a) →
  (∀ k ∈ K, ∀ x : R, ‖conjugationHomeomorph k x - x‖ ≤ δ * ‖x‖) →
  0 ≤ C → (∀ x : R, ‖x - p x‖ ≤ C * ‖β x - x‖) →
  (∃ X₀ ∈ conjugationCosetOrbit K L X, β X₀ ∈ conjugationCosetOrbit K L X) →
  ∃ X₀ ∈ conjugationCosetOrbit K L X,
    ‖X₀ - p X₀‖ ≤ C * max a (δ * ‖X₀‖) ∧
    (∀ Y ∈ conjugationCosetOrbit K L X, ‖Y - X₀‖ ≤ max a (δ * ‖X₀‖)) ∧
    ∀ Y ∈ conjugationCosetOrbit K L X, ∀ Z ∈ conjugationCosetOrbit K L X,
      ‖p Y - Z‖ ≤ max 1 (max ‖p‖ C) * max a (δ * ‖X₀‖)

theorem almostFixedOrbitProjection (K : Subgroup Rˣ) (L : AddSubgroup R) (X : R)
    (p : R →L[F] R) (β : R → R) (a δ C : ℝ) :
    AlmostFixedOrbitProjectionStatement K L X p β a δ C := by
  rintro hKL hL hK hC hp ⟨X₀, hX₀, hβX₀⟩
  let B := max a (δ * ‖X₀‖)
  have horbit : ∀ Y ∈ conjugationCosetOrbit K L X, ‖Y - X₀‖ ≤ B := by
    intro Y hY
    rw [← conjugationCosetOrbit_eq_of_mem hKL hX₀] at hY
    obtain ⟨k, hk, l, hl, rfl⟩ := hY
    rw [add_sub_right_comm]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hK k hk X₀) (hL l hl)) |>.trans_eq
      (max_comm _ _)
  have hproj : ‖X₀ - p X₀‖ ≤ C * B := (hp X₀).trans (mul_le_mul_of_nonneg_left (horbit _ hβX₀) hC)
  have hB : 0 ≤ B := (norm_nonneg _).trans (horbit _ hX₀)
  let D := max 1 (max ‖p‖ C)
  refine ⟨X₀, hX₀, hproj, horbit, fun Y hY Z hZ => ?_⟩
  have h₁ : ‖p (Y - X₀)‖ ≤ D * B := calc
    _ ≤ ‖p‖ * ‖Y - X₀‖ := p.le_opNorm _
    _ ≤ ‖p‖ * B := mul_le_mul_of_nonneg_left (horbit _ hY) (norm_nonneg _)
    _ ≤ D * B := mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hB
  have h₂ : ‖p X₀ - X₀‖ ≤ D * B := calc
    _ = ‖X₀ - p X₀‖ := norm_sub_rev _ _
    _ ≤ C * B := hproj
    _ ≤ D * B := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hB
  have h₃ : ‖X₀ - Z‖ ≤ D * B := calc
    _ = ‖Z - X₀‖ := norm_sub_rev _ _
    _ ≤ B := horbit _ hZ
    _ = 1 * B := (one_mul B).symm
    _ ≤ D * B := mul_le_mul_of_nonneg_right (le_max_left _ _) hB
  rw [show p Y - Z = p (Y - X₀) + (p X₀ - X₀) + (X₀ - Z) by rw [map_sub]; abel]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le h₁ h₂)) h₃)

end Langlands.HarmonicAnalysis.UnitConjugation
