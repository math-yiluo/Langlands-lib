import Langlands.GroupScheme.MatrixRepresentation.FrobeniusConvolutionPairing
import Langlands.GroupScheme.MatrixRepresentation.FrobeniusAugmentationNilpotence

/-! # Socle detection in the actual Frobenius distribution algebra -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation.FrobeniusSocleDetection

/-- A nilpotent left ideal detects an annihilated element in every nonzero left ideal. -/
theorem exists_annihilated_mem_of_pow_eq_bot {A : Type*} [Ring A]
    (I J : Ideal A) (n : ℕ) (hI : I ^ n = ⊥) (hJ : J ≠ ⊥) :
    ∃ x ∈ J, x ≠ 0 ∧ ∀ a ∈ I, a * x = 0 := by
  have hstep : ∀ m : ℕ, ∀ x ∈ J, x ≠ 0 →
      (∀ a ∈ I ^ m, a * x = 0) →
      ∃ y ∈ J, y ≠ 0 ∧ ∀ a ∈ I, a * y = 0 := by
    intro m
    induction m with
    | zero =>
        intro x hx hne hann
        exact (hne (by
          simpa using hann 1 (by rw [Submodule.pow_zero, Ideal.one_eq_top]; trivial))).elim
    | succ m ih =>
        intro x hx hne hann
        by_cases h : ∀ a ∈ I, a * x = 0
        · exact ⟨x, hx, hne, h⟩
        · push Not at h
          obtain ⟨a, ha, hax⟩ := h
          apply ih (a * x) (J.mul_mem_left a hx) hax
          intro c hc
          rw [← mul_assoc]
          apply hann
          rw [Submodule.pow_succ]
          exact Ideal.mul_mem_mul hc ha
  obtain ⟨x, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  apply hstep n x hx hne
  intro a ha
  have ha0 : a = 0 := by simpa [hI] using ha
  rw [ha0, zero_mul]

open FrobeniusCoordinateModel FrobeniusDistributionAlgebra FrobeniusConvolutionAction
open FrobeniusConvolutionPairing FrobeniusAugmentationNilpotence FrobeniusTopIntegral
open FrobeniusPolynomialBox TorusUnipotence CoordinateWeights

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (.of k))} [IsAffineHom G.X.hom]
    (p : ℕ) [ExpChar k p] (r : ℕ)

local notation "D" => DistributionAlgebra (G := G) p r

/-- The subspace killed by every element of the actual augmentation ideal. -/
def augmentationSocle : Submodule k D where
  carrier := {ell | ∀ a ∈ augmentationIdeal (G := G) p r, a * ell = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy a ha
    rw [mul_add, hx a ha, hy a ha, zero_add]
  smul_mem' := by
    intro c x hx a ha
    rw [mul_smul_comm, hx a ha, smul_zero]

theorem integral_of_mem_augmentationSocle {ell : D}
    (hell : ell ∈ augmentationSocle (G := G) p r) (a : D) :
    a * ell = a.ofConv 1 • ell := by
  have hε : (a - a.ofConv 1 • (1 : D)) ∈ augmentationIdeal (G := G) p r := by
    change augmentation p r (a - a.ofConv 1 • (1 : D)) = 0
    have hunit : augmentation (G := G) p r (1 : D) = 1 := map_one (augmentation p r)
    rw [map_sub, map_smul, hunit]
    change a.ofConv 1 - a.ofConv 1 * 1 = 0
    rw [mul_one, sub_self]
  have h := hell _ hε
  rw [sub_mul, smul_mul_assoc, one_mul] at h
  exact sub_eq_zero.mp h

variable {S : CommGroupScheme (Spec (.of k))}
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp G)
    (ν : cocharacterLattice S)
    {d : ℕ} (w : Fin d → characterLattice S) (t : Fin d → CharacterUnits.Coord G)
    (ht : Function.Bijective (aeval t : MvPolynomial (Fin d) k →ₐ[k] CharacterUnits.Coord G))
    (htw : ∀ i, t i ∈ CoordinateWeights.weightSpace b (w i))
    (hε : ∀ i, coordCounit G (t i) = 0)
    (hw : ∀ i, 0 < latticePairing S (w i) ν)

include hS htw hw in
/-- Every socle element is the top distribution times its value on the top coordinate. -/
theorem eq_smul_top_of_mem_augmentationSocle {ell : D}
    (hell : ell ∈ augmentationSocle (G := G) p r) :
    ell = ell.ofConv (topCoordinate p r t ht) • topDistribution p r t ht hε := by
  apply eq_of_sub_eq_zero
  apply (convolutionForm_nondegenerate p r t ht hε hS b ν w htw hw).2
  intro a
  rw [map_sub, map_smul]
  change (a * ell).ofConv (topCoordinate p r t ht) -
    ell.ofConv (topCoordinate p r t ht) *
      (a * topDistribution p r t ht hε).ofConv (topCoordinate p r t ht) = 0
  rw [integral_of_mem_augmentationSocle p r hell,
    mul_top p r hS b ν w t ht htw hε hw]
  change a.ofConv 1 * ell.ofConv (topCoordinate p r t ht) -
    ell.ofConv (topCoordinate p r t ht) *
      (a.ofConv 1 * (topDistribution p r t ht hε).ofConv (topCoordinate p r t ht)) = 0
  rw [topDistribution_topCoordinate]
  ring

include hS htw hw in
/-- Every nonzero left ideal in the actual distribution algebra contains the top distribution. -/
theorem topDistribution_mem_of_ne_bot (J : Ideal D) (hJ : J ≠ ⊥) :
    topDistribution p r t ht hε ∈ J := by
  obtain ⟨n, hn⟩ := isNilpotent_augmentationIdeal (G := G) p r hS b ν w t ht htw hε hw
  obtain ⟨ell, hell, hne, hann⟩ :=
    exists_annihilated_mem_of_pow_eq_bot (augmentationIdeal (G := G) p r) J n hn hJ
  have heq := eq_smul_top_of_mem_augmentationSocle p r hS b ν w t ht htw hε hw hann
  have hc : ell.ofConv (topCoordinate p r t ht) ≠ 0 := by
    intro hc
    exact hne (by simpa [hc] using heq)
  have hmem := (J.restrictScalars k).smul_mem
    ((ell.ofConv (topCoordinate p r t ht))⁻¹) hell
  nth_rw 2 [heq] at hmem
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at hmem
  exact hmem

end Langlands.GroupScheme.MatrixRepresentation.FrobeniusSocleDetection
