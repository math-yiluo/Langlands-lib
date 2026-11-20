import Langlands.Representation.Archimedean.CompactWeightedOrbit
import Langlands.Analysis.OperatorTraceFiniteCompression
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # A finite compact coefficient weight with nonzero positive square -/

noncomputable section

open MeasureTheory Set
open scoped Matrix InnerProductSpace ComplexConjugate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.Analysis.OperatorIdeals

section Weights

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (K : Subgroup G) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (R : G →* (H →L[ℂ] H)) (hR : IsContinuousRepresentation R)

local notation "j" => (ContinuousMap.mk Subtype.val continuous_subtype_val : C(K, G))

/-- Matrix coefficient weights obtained by varying the second argument in a
finite-dimensional compact type. -/
def compactCoefficientWeights {d : ℕ} (i : (Fin d → ℂ) →ₗ[ℂ] H) (v : H) :
    (Fin d → ℂ) →ₗ[ℂ] C(K, ℂ) where
  toFun u := ⟨fun k => ⟪R (k : G) v, i u⟫_ℂ,
    (hR.comp (continuous_subtype_val.prodMk continuous_const)).inner continuous_const⟩
  map_add' u z := by
    ext k
    change ⟪R (k : G) v, i (u + z)⟫_ℂ = ⟪R (k : G) v, i u⟫_ℂ + ⟪R (k : G) v, i z⟫_ℂ
    rw [map_add, inner_add_right]
  map_smul' c u := by
    ext k
    change ⟪R (k : G) v, i (c • u)⟫_ℂ = c * ⟪R (k : G) v, i u⟫_ℂ
    rw [map_smul, inner_smul_right]

variable
  (hU : ∀ (k : K) (x y : H), ⟪R (k : G) x, R (k : G) y⟫_ℂ = ⟪x, y⟫_ℂ)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
include hU in
private theorem compact_inner_inverse (k : K) (x y : H) :
    ⟪R ((k⁻¹ : K) : G) x, y⟫_ℂ = ⟪x, R (k : G) y⟫_ℂ := by
  calc
    _ = ⟪R (k : G) (R ((k⁻¹ : K) : G) x), R (k : G) y⟫_ℂ := (hU k _ _).symm
    _ = _ := by
      rw [← mul_apply_eq_comp, ← map_mul, ← Subgroup.coe_mul, mul_inv_cancel,
        Subgroup.coe_one, map_one, one_apply_eq_self]

omit [IsTopologicalGroup G] in
include hU in
/-- The coefficient family carries the left translations of the finite compact type. -/
theorem compactCoefficientWeights_translate {d : ℕ} (τ : K →* Matrix (Fin d) (Fin d) ℂ)
    (i : (Fin d → ℂ) →ₗ[ℂ] H) (hi : ∀ (k : K) (u : Fin d → ℂ), i (τ k *ᵥ u) = R (k : G) (i u))
    (v : H) (k x : K) (u : Fin d → ℂ) :
    compactCoefficientWeights K R hR i v (τ k *ᵥ u) x =
      compactCoefficientWeights K R hR i v u (k⁻¹ * x) := by
  change ⟪R (x : G) v, i (τ k *ᵥ u)⟫_ℂ = ⟪R ((k⁻¹ * x : K) : G) v, i u⟫_ℂ
  rw [hi, ← compact_inner_inverse K R hU, Subgroup.coe_mul, map_mul, mul_apply_eq_comp]

variable [CompactSpace K] [MeasurableSpace K] [BorelSpace K] [CompleteSpace H]
  (ν : Measure K) [IsFiniteMeasure ν]

omit [IsTopologicalGroup G] in
private theorem inner_compactWeightedOrbit (w : C(K, ℂ)) (x y : H) :
    ⟪x, compactWeightedOrbit ν R hR j w y⟫_ℂ = ∫ k, w k * ⟪x, R (k : G) y⟫_ℂ ∂ν := by
  have hi : Integrable (fun k : K => w k • R (k : G) y) ν :=
    integrable_compactWeightedOrbit ν R hR j w y
  change (innerSL ℂ x) (∫ k, w k • R (k : G) y ∂ν) = _
  rw [← (innerSL ℂ x).integral_comp_comm hi]
  exact integral_congr_ae (Filter.Eventually.of_forall fun k => inner_smul_right _ _ _)

include hU in
/-- A weight compatible with inversion and conjugation averages to a self-adjoint
operator for a compact action preserving the Hilbert inner product. -/
theorem adjoint_compactWeightedOrbit [ν.IsInvInvariant]
    (w : C(K, ℂ)) (hw : ∀ k : K, conj (w k⁻¹) = w k) :
    (compactWeightedOrbit ν R hR j w).adjoint = compactWeightedOrbit ν R hR j w := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  let T := compactWeightedOrbit ν R hR j w
  change ⟪x, T.adjoint y⟫_ℂ = ⟪x, T y⟫_ℂ
  calc
    _ = conj ⟪y, T x⟫_ℂ := by rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]
    _ = ∫ k : K, conj (w k * ⟪y, R (k : G) x⟫_ℂ) ∂ν := by
      rw [inner_compactWeightedOrbit K R hR ν w y x, ← integral_conj]
    _ = _ := by
      rw [inner_compactWeightedOrbit K R hR ν w x y, ← integral_inv_eq_self _ ν]
      apply integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      change conj (w k⁻¹ * ⟪y, R ((k⁻¹ : K) : G) x⟫_ℂ) =
        w k * ⟪x, R (k : G) y⟫_ℂ
      rw [map_mul, hw, inner_conj_symm, compact_inner_inverse K R hU]

include hU in
/-- A diagonal coefficient weight for a unitary compact action gives a self-adjoint average. -/
theorem adjoint_compactWeightedOrbit_coefficient [ν.IsInvInvariant]
    {d : ℕ} (i : (Fin d → ℂ) →ₗ[ℂ] H) (u : Fin d → ℂ) :
    (compactWeightedOrbit ν R hR j (compactCoefficientWeights K R hR i (i u) u)).adjoint =
      compactWeightedOrbit ν R hR j (compactCoefficientWeights K R hR i (i u) u) := by
  refine adjoint_compactWeightedOrbit K R hR hU ν _ fun k => ?_
  change conj ⟪R ((k⁻¹ : K) : G) (i u), i u⟫_ℂ = ⟪R (k : G) (i u), i u⟫_ℂ
  rw [compact_inner_inverse K R hU, inner_conj_symm]

omit [IsTopologicalGroup G] in
/-- A nonzero diagonal coefficient gives a nonzero average for its conjugate weight. -/
theorem compactWeightedOrbit_ne_zero_of_coefficient [ν.IsOpenPosMeasure]
    {d : ℕ} (i : (Fin d → ℂ) →ₗ[ℂ] H) (u : Fin d → ℂ) (hu : i u ≠ 0) :
    compactWeightedOrbit ν R hR j (compactCoefficientWeights K R hR i (i u) u) ≠ 0 := by
  let v := i u
  let w := compactCoefficientWeights K R hR i v u
  let a : K → ℂ := fun k => ⟪v, R (k : G) v⟫_ℂ
  let b : K → ℝ := fun k => Complex.normSq (a k)
  have ha : Continuous a := continuous_const.inner (hR.comp (continuous_subtype_val.prodMk continuous_const))
  have hb : Continuous b := Complex.continuous_normSq.comp ha
  have hb₁ : b 1 ≠ 0 := by
    change Complex.normSq (inner ℂ v (R ((1 : K) : G) v)) ≠ 0
    rw [Subgroup.coe_one, map_one, one_apply_eq_self]
    exact (Complex.normSq_pos.mpr (inner_self_ne_zero.mpr hu)).ne'
  have hbpos : 0 < ∫ k, b k ∂ν :=
    hb.integral_pos_of_hasCompactSupport_nonneg_nonzero (HasCompactSupport.of_compactSpace _)
      (fun _ => Complex.normSq_nonneg _) (x := 1) hb₁
  have he : ⟪v, compactWeightedOrbit ν R hR j w v⟫_ℂ = Complex.ofReal (∫ k, b k ∂ν) := by
    rw [inner_compactWeightedOrbit K R hR ν, ← integral_complex_ofReal]
    apply integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    change ⟪R (k : G) v, v⟫_ℂ * a k = ((Complex.normSq (a k) : ℝ) : ℂ)
    rw [Complex.normSq_eq_conj_mul_self, inner_conj_symm]
  intro hz
  change compactWeightedOrbit ν R hR j w = 0 at hz
  rw [hz, zero_apply, inner_zero_right] at he
  exact (Complex.ofReal_ne_zero.mpr hbpos.ne') he.symm

end Weights

section PositiveSquare

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A nonzero finite-range self-adjoint operator has a nonzero trace of its square. -/
theorem operatorTrace_comp_self_ne_zero_of_selfAdjoint (P : H →L[ℂ] H)
    (hfin : FiniteDimensional ℂ P.toLinearMap.range) (hP : P.adjoint = P) (hne : P ≠ 0) :
    operatorTrace (P.comp P) ≠ 0 := by
  let M := P.toLinearMap.range
  let : FiniteDimensional ℂ M := hfin
  let : CompleteSpace M := FiniteDimensional.complete ℂ M
  let i : M →L[ℂ] H := M.subtypeL
  let p : H →L[ℂ] M := P.codRestrict M (fun x => ⟨x, rfl⟩)
  let b := stdOrthonormalBasis ℂ M
  have hcomp : i.comp (p.comp P) = P.comp P := rfl
  have hinner (x : H) : ⟪x, P (P x)⟫_ℂ = ⟪P x, P x⟫_ℂ := by
    simpa only [hP] using ContinuousLinearMap.adjoint_inner_right P x (P x)
  have hdiag (l : Fin (Module.finrank ℂ M)) :
      ⟪b l, ((p.comp P).comp i) (b l)⟫_ℂ = Complex.ofReal (‖P (i (b l))‖ ^ 2) := by
    change ⟪i (b l), P (P (i (b l)))⟫_ℂ = _
    rw [hinner]
    exact (inner_self_ofReal_re (𝕜 := ℂ) (P (i (b l)))).symm.trans
      (congrArg Complex.ofReal (inner_self_eq_norm_sq (𝕜 := ℂ) (P (i (b l)))))
  intro hzero
  rw [← hcomp, (operatorTrace_finite_compression i (p.comp P)).2,
    operatorTrace_eq_sum_diagonal b] at hzero
  simp_rw [hdiag, ← Complex.ofReal_sum] at hzero
  have hsum : ∑ l, ‖P (i (b l))‖ ^ 2 = 0 := Complex.ofReal_eq_zero.mp hzero
  have hPQ : P.toLinearMap.comp i.toLinearMap = 0 := by
    apply b.toBasis.ext
    intro l
    have hl := (Finset.sum_eq_zero_iff_of_nonneg (fun k (_ : k ∈ Finset.univ) =>
      sq_nonneg ‖P (i (b k))‖)).mp hsum l (Finset.mem_univ l)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hl)
  apply hne
  apply ContinuousLinearMap.ext
  intro x
  have hz : P (P x) = 0 := LinearMap.congr_fun hPQ (p x)
  have hx := hinner x
  rw [hz, inner_zero_right] at hx
  exact inner_self_eq_zero.mp hx.symm

end PositiveSquare

end Langlands.Archimedean
