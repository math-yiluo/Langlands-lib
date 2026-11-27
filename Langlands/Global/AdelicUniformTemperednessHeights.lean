import Langlands.Global.AdelicUniformTemperednessExtrapolation
import Langlands.Global.AdelicPositiveTorusLogHeightBound
import Langlands.Global.AdelicCentralPositiveHeightProof
import Langlands.Global.AdelicSiegelDominatedIntegrabilityProof

/-! # Heights of positive torus points in simple-root and central coordinates

Let `rho` be a matrix representation of `G` of size `N > 0`, and write `‖u‖` for the norm of the
simple-root and central coordinates of a positive point `u` of the maximal split torus. The
adelic height of the image of `u` in `G(𝔸)` is at most `C e^{r ‖u‖}` for some `C ≥ 1` and
`r ≥ 0`. If `rho` is moreover a closed embedding, then `‖u‖ ≤ A log ht(u) + B` for some
`A, B ≥ 0`, where `ht(u)` is that height. -/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus RepresentationGrowth
  Langlands.LinearAlgebra.RationalSpan

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {𝓕 : StandardParabolicFamily F G}

local notation "Δ" => simpleRelativeRoots 𝓕.i 𝓕.ν

omit [NumberField F] in
/-- Finitely many characters control, and are controlled by, the coordinates. -/
theorem TorusFrame.exists_coordinate_characters [Fintype Δ] (Fr : TorusFrame 𝓕) :
    ∃ (I : Type) (_ : Fintype I) (χ : I → characterLattice 𝓕.T) (c : ℝ), 0 ≤ c ∧
      ratSpan (Set.range χ) = ⊤ ∧
      ∀ ℓ : RealCharacterDual F 𝓕.T.toGrp,
        (∀ k, |ℓ (χ k)| ≤ c * ‖Fr.e ℓ‖) ∧ ‖Fr.e ℓ‖ ≤ c * ‖fun k => ℓ (χ k)‖ := by
  obtain ⟨I, hI, ⟨eT⟩⟩ := 𝓕.isSplitTorus_T
  let : Fintype I := Fintype.ofFinite I
  let χ := coordinateCharacter F I 𝓕.T eT
  have hspan : ratSpan (Set.range χ) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    induction y using TensorProduct.inductionOn with
    | add a b ha hb => exact Submodule.add_mem _ ha hb
    | tmul q ψ =>
      have hψ : toRat ψ ∈ ratSpan (Set.range χ) := by
        rw [character_eq_sum_coordinateCharacter F 𝓕.T I eT ψ, map_sum]
        refine Submodule.sum_mem _ fun k _ => ?_
        rw [map_zsmul]
        exact Submodule.smul_of_tower_mem _ _ (toRat_mem_ratSpan ⟨k, rfl⟩)
      have : q ⊗ₜ[ℤ] ψ = q • toRat ψ := by
        simp [toRat, TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ q hψ
  let D := dualCoordinatesContinuousEquiv F 𝓕.T I eT
  let Φ : (I → ℝ) ≃L[ℝ] ((Δ → ℝ) × (Fin Fr.r → ℝ)) := D.symm.trans Fr.e
  refine ⟨I, inferInstance, χ, max ‖Φ.symm.toContinuousLinearMap‖ ‖Φ.toContinuousLinearMap‖,
    le_max_of_le_left (norm_nonneg _), hspan, fun ℓ => ⟨fun k => ?_, ?_⟩⟩
  · have hD : D ℓ = fun k => ℓ (χ k) := rfl
    have h1 : D ℓ = Φ.symm (Fr.e ℓ) := by simp [Φ]
    calc |ℓ (χ k)| = ‖D ℓ k‖ := by rw [hD, Real.norm_eq_abs]
      _ ≤ ‖D ℓ‖ := norm_le_pi_norm _ k
      _ = ‖Φ.symm.toContinuousLinearMap (Fr.e ℓ)‖ := by rw [h1]; rfl
      _ ≤ ‖Φ.symm.toContinuousLinearMap‖ * ‖Fr.e ℓ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have h1 : Fr.e ℓ = Φ (fun k => ℓ (χ k)) := by
      have : (fun k => ℓ (χ k)) = D ℓ := rfl
      rw [this]
      simp [Φ]
    calc ‖Fr.e ℓ‖ = ‖Φ.toContinuousLinearMap (fun k => ℓ (χ k))‖ := by rw [h1]; rfl
      _ ≤ ‖Φ.toContinuousLinearMap‖ * ‖fun k => ℓ (χ k)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := by gcongr; exact le_max_right _ _

theorem adelicHeight_torus {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (u : AdelicGroupPoints F 𝓕.T.toGrp) :
    adelicHeight F 𝓕.T.toGrp (𝓕.i ≫ rho) u = adelicHeight F G rho (torusPoint u) := by
  unfold adelicHeight
  rw [← adelicMatrix_map]

/-- **Upper bound for heights.** For a matrix representation `rho` of size `N > 0` there are
`C ≥ 1` and `r ≥ 0` such that the height of the image in `G(𝔸)` of every positive point `u` of
the maximal split torus is at most `C e^{r ‖u‖}`. -/
theorem TorusFrame.exists_height_le [Fintype Δ] (Fr : TorusFrame 𝓕) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 ≤ r ∧ ∀ u ∈ intrinsicSubgroup F 𝓕.T,
      adelicHeight F G rho (torusPoint u) ≤ C * Real.exp (r * ‖Fr.crd u‖) := by
  obtain ⟨I, _, χ, c, hc, hspan, hctl⟩ := Fr.exists_coordinate_characters
  obtain ⟨C, r, hC, hr, h⟩ := adelicPositiveTorusLogHeightBound 𝓕.i rho (Set.range χ)
    𝓕.isSplitTorus_T hspan hN
  refine ⟨C, r * c, hC, mul_nonneg hr hc, fun u hu => ?_⟩
  have := h ⟨u, hu⟩ (c * ‖Fr.crd u‖) (mul_nonneg hc (norm_nonneg _)) (by
    rintro _ ⟨k, rfl⟩
    exact (hctl (characterLog F 𝓕.T.toGrp u)).1 k)
  rw [mul_assoc r c]
  exact this

/-- **Lower bound for heights.** For a closed matrix embedding `rho` of size `N > 0` there are
`A, B ≥ 0` such that `‖u‖ ≤ A log ht(u) + B` for every positive point `u` of the maximal split
torus, where `ht(u)` is the height of its image in `G(𝔸)`. -/
theorem TorusFrame.exists_crd_le_log_height [Fintype Δ] (Fr : TorusFrame 𝓕) {N : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hrho : IsClosedSubgroup rho) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ u ∈ intrinsicSubgroup F 𝓕.T,
      ‖Fr.crd u‖ ≤ A * Real.log (adelicHeight F G rho (torusPoint u)) + B := by
  obtain ⟨I, _, χ, c, hc, -, hctl⟩ := Fr.exists_coordinate_characters
  have hiC : IsClosedSubgroup 𝓕.i := 𝓕.maximalSplit.1.2
  have hbound := fun k => exists_characterNorm_le F (𝓕.i ≫ rho) hN (hiC.comp hrho) (χ k)
  choose Ck hCk ek hek using hbound
  let A := c * ∑ k, (ek k : ℝ)
  let B := c * ∑ k, Real.log (Ck k)
  have hA : 0 ≤ A := mul_nonneg hc (Finset.sum_nonneg fun k _ => Nat.cast_nonneg _)
  have hB : 0 ≤ B := mul_nonneg hc (Finset.sum_nonneg fun k _ => Real.log_nonneg (hCk k))
  refine ⟨A, B, hA, hB, fun u hu => ?_⟩
  set h := adelicHeight F G rho (torusPoint u) with hh
  have h1 : 1 ≤ h := one_le_adelicHeight F G rho hN _
  have hlogh : 0 ≤ Real.log h := Real.log_nonneg h1
  have hcoord (k : I) : |characterLog F 𝓕.T.toGrp u (χ k)| ≤ Real.log (Ck k) + ek k * Real.log h := by
    obtain ⟨h₁, h₂⟩ := hek k u
    rw [adelicHeight_torus] at h₁ h₂
    have hpos : (0 : ℝ) < ((characterNorm F 𝓕.T.toGrp (χ k).toMul u : ℝ≥0) : ℝ) := by
      exact_mod_cast pos_iff_ne_zero.mpr (characterNorm F 𝓕.T.toGrp (χ k).toMul u).ne_zero
    have hCpos : 0 < Ck k := lt_of_lt_of_le one_pos (hCk k)
    have hR : 0 < Ck k * h ^ ek k := mul_pos hCpos (pow_pos (lt_of_lt_of_le one_pos h1) _)
    have hlogR : Real.log (Ck k * h ^ ek k) = Real.log (Ck k) + ek k * Real.log h := by
      rw [Real.log_mul hCpos.ne' (pow_pos (lt_of_lt_of_le one_pos h1) _).ne', Real.log_pow]
    rw [characterLog_apply, abs_le]
    constructor
    · have : ((((characterNorm F 𝓕.T.toGrp (χ k).toMul u)⁻¹ : ℝ≥0ˣ) : ℝ≥0) : ℝ) =
          ((characterNorm F 𝓕.T.toGrp (χ k).toMul u : ℝ≥0) : ℝ)⁻¹ := by
        simp
      have hinv : Real.log (((characterNorm F 𝓕.T.toGrp (χ k).toMul u : ℝ≥0) : ℝ)⁻¹) ≤
          Real.log (Ck k * h ^ ek k) := by
        refine Real.log_le_log (inv_pos.mpr hpos) ?_
        rw [← this]
        exact h₂
      rw [Real.log_inv, hlogR] at hinv
      linarith
    · have hle : Real.log ((characterNorm F 𝓕.T.toGrp (χ k).toMul u : ℝ≥0) : ℝ) ≤
          Real.log (Ck k * h ^ ek k) :=
        Real.log_le_log hpos (by exact_mod_cast h₁)
      rw [hlogR] at hle
      exact hle
  have hvec : ‖fun k => characterLog F 𝓕.T.toGrp u (χ k)‖ ≤
      ∑ k, (Real.log (Ck k) + ek k * Real.log h) := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun k _ =>
      add_nonneg (Real.log_nonneg (hCk k)) (mul_nonneg (Nat.cast_nonneg _) hlogh))).mpr
      fun k => ?_
    rw [Real.norm_eq_abs]
    refine (hcoord k).trans ?_
    exact Finset.single_le_sum (f := fun k => Real.log (Ck k) + ek k * Real.log h)
      (fun k _ => add_nonneg (Real.log_nonneg (hCk k)) (mul_nonneg (Nat.cast_nonneg _) hlogh))
      (Finset.mem_univ k)
  have := (hctl (characterLog F 𝓕.T.toGrp u)).2
  change ‖Fr.crd u‖ ≤ _ at this
  calc ‖Fr.crd u‖ ≤ c * ∑ k, (Real.log (Ck k) + ek k * Real.log h) :=
        this.trans (mul_le_mul_of_nonneg_left hvec hc)
    _ = A * Real.log h + B := by
        simp only [A, B, Finset.sum_add_distrib, mul_add, ← Finset.sum_mul]
        ring

end Langlands.Global.StandardParabolicFamily
