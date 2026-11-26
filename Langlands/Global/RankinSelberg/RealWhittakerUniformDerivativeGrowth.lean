import Langlands.Analysis.LocalEllipticSystemPointwise
import Langlands.Global.RankinSelberg.RealWhittakerEllipticOperator
import Langlands.Global.RankinSelberg.RealPrincipalSeriesOrbitWord
import Langlands.Global.RankinSelberg.RealUniformWhittakerModel

/-! # Uniform derivative growth in the real ordinary Whittaker model -/

noncomputable section

open Filter Set Metric Topology
open scoped ContDiff Manifold Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 80000

namespace Langlands.Global.RankinSelbergGlobal.RealWhittakerElliptic

open Langlands.Analysis Langlands.Archimedean Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.RealJacquetFiniteGeneration (op op_tmul wordOp
  wordOp_nil wordOp_cons wordOp_append wordOp_singleton)
open RealPlaceRestriction (two_le_realMatrixHeight)

attribute [local instance 100] LieRing.ofAssociativeRing

variable {r : ℕ}

local notation "n" => r + 1
local notation "I" => Fin n
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "M" => Matrix I I ℝ
local notation "E" => EuclideanSpace ℝ (Fin (Fintype.card (I × I)))
local notation "Std" => Automorphic.realStandardKFinite n
local notation "RD" => rightDerivative (matrixModel ℝ n)

local notation "standardDerivative" => fun {ds : List RealBlock} X => op (realStandardLie n ds) X
local notation "standardDerivativeWord" => fun {ds : List RealBlock} w => wordOp (realStandardLie n ds) w

private theorem one_le_height (g : G) : 1 ≤ realMatrixHeight g :=
  le_trans (by norm_num) (two_le_realMatrixHeight (Nat.succ_pos r) g)

/-- Finitely many inducing vectors have a common moderate-growth bound. -/
private theorem exists_realWhittaker_finite_growth {J : Type*} [Fintype J]
    {ds : List RealBlock} {a : ℝˣ} {B : Std ds →ₗ[ℂ] (G → ℂ)}
    (hB : IsRealWhittakerIntertwiner r ds a B) (f : J → Std ds) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ j g, ‖B (f j) g‖ ≤ C * realMatrixHeight g ^ N := by
  classical
  have h := fun j => hB.2.2.1 (f j)
  choose C N h using h
  refine ⟨∑ j, max (C j) 0, Finset.univ.sup N,
    Finset.sum_nonneg fun _ _ => le_max_right _ _, fun j g => ?_⟩
  have hC : max (C j) 0 ≤ ∑ j, max (C j) 0 :=
    Finset.single_le_sum (f := fun j => max (C j) 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_univ j)
  have hN : N j ≤ Finset.univ.sup N := Finset.le_sup (Finset.mem_univ j)
  have hg : 0 ≤ realMatrixHeight g := zero_le_one.trans (one_le_height g)
  calc
    _ ≤ C j * realMatrixHeight g ^ N j := h j g
    _ ≤ max (C j) 0 * realMatrixHeight g ^ N j :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hg _)
    _ ≤ _ := mul_le_mul hC (pow_le_pow_right₀ (one_le_height g) hN)
      (pow_nonneg hg _) (Finset.sum_nonneg fun _ _ => le_max_right _ _)

/-- A common height bound for finitely many coefficients and their first
right derivatives in the real coordinate directions. -/
private theorem exists_realWhittaker_finite_first_growth {J : Type*} [Fintype J]
    {ds : List RealBlock} {a : ℝˣ} {B : Std ds →ₗ[ℂ] (G → ℂ)}
    (hB : IsRealWhittakerIntertwiner r ds a B) (f : J → Std ds) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧
      (∀ j g, ‖B (f j) g‖ ≤ C * realMatrixHeight g ^ N) ∧
      (∀ j (i : I × I) g,
        ‖RD (Matrix.stdBasis ℝ I I i) (B (f j)) g‖ ≤ C * realMatrixHeight g ^ N) := by
  let Y (i : I × I) := Matrix.stdBasis ℝ I I i
  let v (j : J) (i : I × I) := standardDerivative (Y i) (f j)
  let family : J ⊕ (J × (I × I)) → Std ds :=
    Sum.elim f fun p => v p.1 p.2
  obtain ⟨C, N, hC, hbound⟩ := exists_realWhittaker_finite_growth hB family
  refine ⟨C, N, hC, fun j g => hbound (Sum.inl j) g, fun j i g => ?_⟩
  have he := congrFun (hB.2.2.2.2 (Y i) (f j) (v j i) (realStandardLie_one_tmul_apply_coe _ _ (Y i) (f j))) g
  change ‖RD (Y i) (B (f j)) g‖ ≤ _
  rw [← he]
  exact hbound (Sum.inr (j, i)) g

/-- The first matrix jets of a finite coefficient family, on a fixed compact
part of the matrix chart, have a common growth exponent under left translation. -/
private theorem exists_realWhittaker_compact_first_jet_growth {J : Type*} [Fintype J]
    {ds : List RealBlock} {a : ℝˣ} {B : Std ds →ₗ[ℂ] (G → ℂ)}
    (hB : IsRealWhittakerIntertwiner r ds a B) (f : J → Std ds)
    (S : Set G) (hS : IsCompact S) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ j g h, h ∈ S →
      ‖B (f j) (g * h)‖ ≤ C * realMatrixHeight g ^ N ∧
      ‖fderiv ℝ (unitsExtension (fun k => B (f j) (g * k))) h.val‖ ≤
        C * realMatrixHeight g ^ N := by
  obtain ⟨C, N, hC, hcoef, hder⟩ := exists_realWhittaker_finite_first_growth hB f
  obtain ⟨H, hH⟩ := hS.exists_bound_of_continuousOn continuous_realMatrixHeight.continuousOn
  have hcinv : Continuous (fun h : G => (h⁻¹).val) := Units.continuous_val.comp continuous_inv
  obtain ⟨D, hD⟩ := hS.exists_bound_of_continuousOn hcinv.continuousOn
  let H₀ := max H 1
  let D₀ := max D 1
  let e := Matrix.stdBasis ℝ I I
  let coord (p : I × I) : M →L[ℝ] ℝ := (e.coord p).toContinuousLinearMap
  let K := ∑ p : I × I, ‖coord p‖
  let C₀ := C * H₀ ^ N
  let C₁ := C₀ * max 1 (K * D₀)
  have hH₀ : 0 ≤ H₀ := zero_le_one.trans (le_max_right _ _)
  have hD₀ : 0 ≤ D₀ := zero_le_one.trans (le_max_right _ _)
  have hC₀ : 0 ≤ C₀ := mul_nonneg hC (pow_nonneg hH₀ _)
  have hC₁ : 0 ≤ C₁ := mul_nonneg hC₀ (zero_le_one.trans (le_max_left _ _))
  have hgrowth (g h : G) (hh : h ∈ S) :
      C * realMatrixHeight (g * h) ^ N ≤ C₀ * realMatrixHeight g ^ N := by
    have hg : 0 ≤ realMatrixHeight g := zero_le_one.trans (one_le_height g)
    have hh' : realMatrixHeight h ≤ H₀ := by
      have hb := hH h hh
      rw [Real.norm_of_nonneg (zero_le_one.trans (one_le_height h))] at hb
      exact hb.trans (le_max_left _ _)
    have hprod := (realMatrixHeight_mul_le g h).trans (mul_le_mul_of_nonneg_left hh' hg)
    calc
      _ ≤ C * (realMatrixHeight g * H₀) ^ N :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (zero_le_one.trans (one_le_height (g * h))) hprod _) hC
      _ = _ := by rw [mul_pow]; unfold C₀; ring
  refine ⟨C₁, N, hC₁, fun j g h hh => ⟨?_, ?_⟩⟩
  · refine (hcoef j (g * h)).trans ((hgrowth g h hh).trans ?_)
    have hle : C₀ ≤ C₁ := le_mul_of_one_le_right hC₀ (le_max_left _ _)
    exact mul_le_mul_of_nonneg_right hle (pow_nonneg (zero_le_one.trans (one_le_height g)) _)
  · let u := unitsExtension (fun k => B (f j) (g * k))
    let F := fderiv ℝ u h.val
    change ‖F‖ ≤ C₁ * realMatrixHeight g ^ N
    apply F.opNorm_le_bound
      (mul_nonneg hC₁ (pow_nonneg (zero_le_one.trans (one_le_height g)) _))
    intro X
    let Y := h.inv * X
    have hX : (∑ p : I × I, coord p Y • (h.val * e p)) = X := by
      simp only [← Matrix.mul_smul, ← Matrix.mul_sum]
      change h.val * (∑ p : I × I, e.repr Y p • e p) = X
      rw [e.sum_repr, show Y = h.inv * X from rfl, ← Matrix.mul_assoc, h.val_inv, Matrix.one_mul]
    have hYn : ‖Y‖ ≤ D₀ * ‖X‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((hD h hh).trans (le_max_left _ _))
        (norm_nonneg _))
    have hDerv (p : I × I) : ‖F (h.val * e p)‖ ≤ C₀ * realMatrixHeight g ^ N := by
      have hp := (hder j p (g * h)).trans (hgrowth g h hh)
      rw [← matrixDirectionalDerivative_unitsExtension (e p) (hB.2.1 (f j)) g h] at hp
      exact hp
    calc
      ‖F X‖ = ‖∑ p : I × I, coord p Y • F (h.val * e p)‖ := by
        simp only [← map_smul, ← map_sum, hX]
      _ ≤ ∑ p : I × I, ‖coord p Y • F (h.val * e p)‖ := norm_sum_le _ _
      _ ≤ ∑ p : I × I,
          (‖coord p‖ * (D₀ * ‖X‖)) * (C₀ * realMatrixHeight g ^ N) := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [norm_smul]
        exact mul_le_mul ((coord p).le_opNorm Y |>.trans
          (mul_le_mul_of_nonneg_left hYn (norm_nonneg _))) (hDerv p) (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (mul_nonneg hD₀ (norm_nonneg _)))
      _ = C₀ * (K * D₀) * realMatrixHeight g ^ N * ‖X‖ := by
        simp only [K, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ => ?_
        ring
      _ ≤ _ := by
        have hle : C₀ * (K * D₀) ≤ C₁ := mul_le_mul_of_nonneg_left (le_max_right _ _) hC₀
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hle (pow_nonneg (zero_le_one.trans (one_le_height g)) _))
          (norm_nonneg _)


private theorem iteratedJet_le_of_coordinates (e : M ≃L[ℝ] E) (u : M → ℂ) (p : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ p u (e.symm y)‖ ≤
      ‖iteratedFDeriv ℝ p (u ∘ e.symm) y‖ * ‖e.toContinuousLinearMap‖ ^ p := by
  have he :
      iteratedFDeriv ℝ p u (e.symm y) =
        (iteratedFDeriv ℝ p (u ∘ e.symm) y).compContinuousLinearMap
          (fun _ => e.toContinuousLinearMap) := by
    ext m
    exact (CoordinateScalarOperator.iteratedFDeriv_comp_equiv e u p y m).symm
  rw [he]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ p (u ∘ e.symm) y).norm_compContinuousLinearMap_le
      (fun _ => e.toContinuousLinearMap)

private theorem exists_jet_growth_of_finite_system {J : Type*} [Fintype J]
    {ds : List RealBlock} {a : ℝˣ} {B : Std ds →ₗ[ℂ] (G → ℂ)}
    (hB : IsRealWhittakerIntertwiner r ds a B) (f : J → Std ds) (A : J → J → ℂ)
    (hA : ∀ i, squareOperator ds (f i) = ∑ j, A i j • f j) :
    ∃ (N : ℕ) (C : ℕ → ℝ), (∀ p, 0 ≤ C p) ∧ ∀ i (g : G) (p : ℕ),
      ‖iteratedFDeriv ℝ p (unitsExtension (fun h => B (f i) (g * h))) (1 : M)‖ ≤
        C p * realMatrixHeight g ^ N := by
  let D := chartOperator n
  let e := D.euclideanCoordinates
  let S : Set E := e.symm ⁻¹' {h : M | IsUnit h}
  let y₀ := e 1
  have hS : IsOpen S := isOpen_setOf_isUnit_matrix.preimage e.symm.continuous
  have hy₀ : y₀ ∈ S := by
    change IsUnit (e.symm (e 1))
    rw [e.symm_apply_apply]
    exact isUnit_one
  have hell : D.toEuclidean.IsEllipticOn S :=
    D.transport_isElliptic e (chartOperator_elliptic n)
  have han : D.toEuclidean.AnalyticCoefficientsOn S :=
    D.transport_analyticCoefficients e ((chartOperator_analytic n).mono
      (Set.subset_univ _))
  obtain ⟨R, _, hRsub, C, hC, hbound⟩ :=
    exists_localEllipticSystem_derivative_bounds (by decide : 0 < 2) D.toEuclidean
      D.toEuclidean_basis A hS (fun k w => (han k w).contDiffOn hS.uniqueDiffOn) hell hy₀
  let ψ : G → E := fun h => e h.val
  let U : Set G := ψ ⁻¹' closedBall y₀ R
  have hψ : IsEmbedding ψ := e.toHomeomorph.isEmbedding.comp Units.isOpenEmbedding_val.isEmbedding
  have hU : IsCompact U := hψ.isInducing.isCompact_preimage' (isCompact_closedBall _ _) (by
    intro y hy
    have hu : IsUnit (e.symm y) := hRsub hy
    exact ⟨hu.unit, e.apply_symm_apply y⟩)
  obtain ⟨M₀, N, hM₀, hjet⟩ := exists_realWhittaker_compact_first_jet_growth hB f U hU
  let M₁ := M₀ * max 1 ‖e.symm.toContinuousLinearMap‖
  have hM₁ : 0 ≤ M₁ := mul_nonneg hM₀ (zero_le_one.trans (le_max_left _ _))
  refine ⟨N, fun p => (C p * M₁) * ‖e.toContinuousLinearMap‖ ^ p,
    fun p => mul_nonneg (mul_nonneg (hC p) hM₁) (pow_nonneg (norm_nonneg _) _),
    fun i g p => ?_⟩
  let u (j : J) : M → ℂ := unitsExtension (fun h => B (f j) (g * h))
  let v (j : J) : E → ℂ := u j ∘ e.symm
  have huo (j : J) : ContDiffOn ℝ ∞ (u j) {h : M | IsUnit h} :=
    contDiffOn_unitsExtension ((hB.2.1 (f j)).comp contMDiff_mul_left)
  have hv (j : J) : ContDiffOn ℝ ∞ (v j) S :=
    (huo j).comp e.symm.contDiff.contDiffOn (fun _ h => h)
  have hveq (j : J) (y : E) (hy : y ∈ S) :
      D.toEuclidean.action (v j) y = ∑ k, A j k * v k y := by
    have hu : IsUnit (e.symm y) := hy
    let h : G := hu.unit
    have hh : h.val = e.symm y := rfl
    change (D.transport e).action (u j ∘ e.symm) y = _
    rw [D.transport_action, ← hh, chartOperator_intertwiner hB, hA]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [v, Function.comp_apply, ← hh, u, unitsExtension_val]
  have hg : 0 ≤ realMatrixHeight g :=
    (by norm_num : (0 : ℝ) ≤ 2).trans (two_le_realMatrixHeight (Nat.succ_pos r) g)
  have hM : 0 ≤ M₁ * realMatrixHeight g ^ N := mul_nonneg hM₁ (pow_nonneg hg _)
  have hinit (j : J) (q : ℕ) (hq : q < 2) (y : E) (hy : y ∈ ball y₀ R) :
      ‖iteratedFDeriv ℝ q (v j) y‖ ≤ M₁ * realMatrixHeight g ^ N := by
    have hcy : y ∈ closedBall y₀ R := ball_subset_closedBall hy
    have hu : IsUnit (e.symm y) := hRsub hcy
    let h : G := hu.unit
    have hh : h.val = e.symm y := rfl
    have hhU : h ∈ U := by
      change e h.val ∈ closedBall y₀ R
      rwa [hh, e.apply_symm_apply]
    obtain ⟨hval, hfd⟩ := hjet j g h hhU
    have hc : M₀ ≤ M₁ := le_mul_of_one_le_right hM₀ (le_max_left _ _)
    have hc' : M₀ * ‖e.symm.toContinuousLinearMap‖ ≤ M₁ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hM₀
    interval_cases q
    · rw [norm_iteratedFDeriv_zero]
      change ‖u j (e.symm y)‖ ≤ _
      rw [← hh]
      change ‖unitsExtension (fun k => B (f j) (g * k)) h.val‖ ≤ _
      rw [unitsExtension_val]
      exact hval.trans (mul_le_mul_of_nonneg_right hc (pow_nonneg hg _))
    · rw [norm_iteratedFDeriv_one]
      have hdiff : DifferentiableAt ℝ (u j) (e.symm y) :=
        ((huo j).contDiffAt (isOpen_setOf_isUnit_matrix.mem_nhds hu)).differentiableAt (by simp)
      change ‖fderiv ℝ (u j ∘ e.symm) y‖ ≤ _
      rw [fderiv_comp y hdiff e.symm.differentiableAt]
      change ‖(fderiv ℝ (u j) (e.symm y)).comp (fderiv ℝ (e.symm.toContinuousLinearMap) y)‖ ≤ _
      rw [ContinuousLinearMap.fderiv, ← hh]
      calc
        _ ≤ ‖fderiv ℝ (u j) h.val‖ * ‖e.symm.toContinuousLinearMap‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (M₀ * realMatrixHeight g ^ N) * ‖e.symm.toContinuousLinearMap‖ :=
          mul_le_mul_of_nonneg_right hfd (norm_nonneg _)
        _ ≤ M₁ * realMatrixHeight g ^ N := by
          rw [mul_right_comm]
          exact mul_le_mul_of_nonneg_right hc' (pow_nonneg hg _)
  have hj := hbound v hv hveq (M₁ * realMatrixHeight g ^ N) hinit i p
  rw [max_eq_right hM] at hj
  calc
    _ ≤ ‖iteratedFDeriv ℝ p (v i) y₀‖ * ‖e.toContinuousLinearMap‖ ^ p := by
      simpa only [y₀, e.symm_apply_apply] using iteratedJet_le_of_coordinates e (u i) p y₀
    _ ≤ (C p * (M₁ * realMatrixHeight g ^ N)) * ‖e.toContinuousLinearMap‖ ^ p :=
      mul_le_mul_of_nonneg_right hj (pow_nonneg (norm_nonneg _) _)
    _ = _ := by ring

/-- All matrix jets at the identity of the left translates of a fixed
Whittaker coefficient have a common polynomial height exponent. -/
private theorem exists_realWhittaker_matrix_jet_growth
    {ds : List RealBlock} {a : ℝˣ} {B : Std ds →ₗ[ℂ] (G → ℂ)}
    (hB : IsRealWhittakerIntertwiner r ds a B) (f : Std ds) :
    ∃ (N : ℕ) (C : ℕ → ℝ), (∀ p, 0 ≤ C p) ∧ ∀ (g : G) (p : ℕ),
      ‖iteratedFDeriv ℝ p (unitsExtension (fun h => B f (g * h))) (1 : M)‖ ≤
        C p * realMatrixHeight g ^ N := by
  obtain ⟨V, hdim, hf, hV⟩ := exists_invariant_squareOperator_submodule ds f
  let : FiniteDimensional ℂ V := hdim
  let : Module.Free ℂ V := Module.Free.of_divisionRing ℂ V
  let J := Fin (Module.finrank ℂ V)
  let e : Module.Basis J ℂ V := Module.finBasis ℂ V
  let v (j : Option J) : V := j.elim ⟨f, hf⟩ e
  let w (j : Option J) : V :=
    ⟨squareOperator ds (v j), hV (v j) (v j).property⟩
  let A (i j : Option J) : ℂ := j.elim 0 (e.repr (w i))
  have hA (i : Option J) :
      squareOperator ds (v i : Std ds) = ∑ j, A i j • (v j : Std ds) := by
    have hw := congrArg V.subtype (e.sum_repr (w i))
    simp only [map_sum, map_smul, Submodule.subtype_apply] at hw
    rw [Fintype.sum_option]
    simpa only [A, v, Option.elim_none, Option.elim_some, zero_smul, zero_add] using hw.symm
  obtain ⟨N, C, hC, hjet⟩ := exists_jet_growth_of_finite_system hB (fun j => (v j : Std ds)) A hA
  exact ⟨N, C, hC, hjet none⟩


private theorem matrixField_jet_le (X : M) (p : ℕ) :
    ‖iteratedFDeriv ℝ p (fun h : M => h * X) (1 : M)‖ ≤ ‖X‖ := by
  let L : M →L[ℝ] M := (ContinuousLinearMap.mul ℝ M).flip X
  change ‖iteratedFDeriv ℝ p (L : M → M) (1 : M)‖ ≤ _
  cases p with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    change ‖(1 : M) * X‖ ≤ ‖X‖
    rw [Matrix.one_mul]
  | succ p =>
    rw [← norm_iteratedFDeriv_fderiv, show fderiv ℝ (L : M → M) = fun _ => L from
      funext fun x => L.fderiv]
    cases p with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact L.opNorm_le_bound (norm_nonneg _) fun x =>
        (norm_mul_le x X).trans_eq (mul_comm _ _)
    | succ p =>
      rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero p), Pi.zero_apply, norm_zero]
      exact norm_nonneg _

private theorem matrixDirectionalDerivative_jet_le (X : M) {u : M → ℂ}
    (hu : ContDiffOn ℝ ∞ u {h : M | IsUnit h}) (p : ℕ) :
    ‖iteratedFDeriv ℝ p (matrixDirectionalDerivative X u) (1 : M)‖ ≤
      ∑ j ∈ Finset.range (p + 1),
        (p.choose j : ℝ) * ‖iteratedFDeriv ℝ (j + 1) u (1 : M)‖ * ‖X‖ := by
  let S : Set M := {h | IsUnit h}
  have hS : IsOpen S := isOpen_setOf_isUnit_matrix
  have h1 : (1 : M) ∈ S := isUnit_one
  have hfd := hu.fderiv_of_isOpen hS (show ∞ + 1 ≤ (∞ : ℕ∞ω) by simp)
  let L : M →L[ℝ] M := (ContinuousLinearMap.mul ℝ M).flip X
  have h := norm_iteratedFDerivWithin_clm_apply hfd L.contDiff.contDiffOn hS.uniqueDiffOn h1
    (show (p : ℕ∞ω) ≤ ∞ by simp)
  change ‖iteratedFDerivWithin ℝ p (matrixDirectionalDerivative X u) S 1‖ ≤ _ at h
  rw [iteratedFDerivWithin_of_isOpen p hS h1] at h
  refine h.trans (Finset.sum_le_sum fun j _ => ?_)
  rw [iteratedFDerivWithin_of_isOpen j hS h1, iteratedFDerivWithin_of_isOpen (p - j) hS h1,
    norm_iteratedFDeriv_fderiv]
  exact mul_le_mul_of_nonneg_left (matrixField_jet_le X (p - j)) (by positivity)

private theorem matrixDirectionalDerivative_standard_germ
    {ds : List RealBlock} {a : ℝˣ} {B : Std ds →ₗ[ℂ] (G → ℂ)}
    (hB : IsRealWhittakerIntertwiner r ds a B) (f : Std ds) (X : M) (g : G) :
    matrixDirectionalDerivative X (unitsExtension (fun h => B f (g * h))) =ᶠ[𝓝 (1 : M)]
      unitsExtension (fun h => B (standardDerivative X f) (g * h)) := by
  filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds (isUnit_one : IsUnit (1 : M))] with h hh
  change IsUnit h at hh
  let hUnit : G := hh.unit
  change matrixDirectionalDerivative X (unitsExtension (fun k => B f (g * k))) hUnit.val =
      unitsExtension (fun k => B (standardDerivative X f) (g * k)) hUnit.val
  rw [matrixDirectionalDerivative_unitsExtension X (hB.2.1 f), unitsExtension_val,
    hB.2.2.2.2 X f (standardDerivative X f) (realStandardLie_one_tmul_apply_coe _ _ X f)]

/-- A bound on the individual matrix directions gives a uniform constant at
each word length, with the same height exponent at every length. -/
theorem exists_realWhittaker_right_word_growth
    {ds : List RealBlock} {a : ℝˣ} {B : Std ds →ₗ[ℂ] (G → ℂ)}
    (hB : IsRealWhittakerIntertwiner r ds a B) (f : Std ds) :
    ∃ N : ℕ, ∀ D : ℝ, 0 ≤ D → ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
      ∀ (w : List M), (∀ X ∈ w, ‖X‖ ≤ D) → ∀ g : G,
        ‖B (standardDerivativeWord w f) g‖ ≤ C w.length * realMatrixHeight g ^ N := by
  obtain ⟨N, C₀, hC₀, hstart⟩ := exists_realWhittaker_matrix_jet_growth hB f
  refine ⟨N, fun D hD => ?_⟩
  let C : ℕ → ℕ → ℝ := Nat.rec C₀ fun _ C' p =>
    ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) * C' (j + 1) * D
  have hC (m p : ℕ) : 0 ≤ C m p := by
    induction m generalizing p with
    | zero => exact hC₀ p
    | succ m ih =>
      exact Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (ih _)) hD
  let u (w : List M) (g : G) : M → ℂ :=
    unitsExtension (fun h => B (standardDerivativeWord w f) (g * h))
  have hjet (w : List M) (hw : ∀ X ∈ w, ‖X‖ ≤ D) (g : G) (p : ℕ) :
      ‖iteratedFDeriv ℝ p (u w g) (1 : M)‖ ≤ C w.length p * realMatrixHeight g ^ N := by
    induction w generalizing p with
    | nil => exact hstart g p
    | cons X w ih =>
      have he : matrixDirectionalDerivative X (u w g) =ᶠ[𝓝 (1 : M)] u (X :: w) g :=
        matrixDirectionalDerivative_standard_germ hB (standardDerivativeWord w f) X g
      rw [← (he.iteratedFDeriv ℝ p).eq_of_nhds]
      have hsm : ContDiffOn ℝ ∞ (u w g) {h : M | IsUnit h} :=
        contDiffOn_unitsExtension ((hB.2.1 (standardDerivativeWord w f)).comp contMDiff_mul_left)
      have hi (j : ℕ) := ih (fun Y hY => hw Y (List.mem_cons_of_mem X hY)) (j + 1)
      have hX := hw X (List.mem_cons_self)
      have hg : 0 ≤ realMatrixHeight g :=
        (by norm_num : (0 : ℝ) ≤ 2).trans
          (two_le_realMatrixHeight (Nat.succ_pos r) g)
      refine (matrixDirectionalDerivative_jet_le X hsm p).trans ?_
      change _ ≤ (∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) * C w.length (j + 1) * D) *
        realMatrixHeight g ^ N
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      calc
        _ ≤ (p.choose j : ℝ) * (C w.length (j + 1) * realMatrixHeight g ^ N) * D :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hi j) (Nat.cast_nonneg _)) hX
            (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
              (mul_nonneg (hC _ _) (pow_nonneg hg _)))
        _ = _ := by ring
  refine ⟨fun m => C m 0, fun m => hC m 0, fun w hw g => ?_⟩
  have h := hjet w hw g 0
  rw [norm_iteratedFDeriv_zero] at h
  change ‖unitsExtension (fun k => B (standardDerivativeWord w f) (g * k)) ((1 : G).val)‖ ≤ _ at h
  rwa [unitsExtension_val, mul_one] at h

private def boundedWords {ds : List RealBlock} (B : Std ds →ₗ[ℂ] (G → ℂ)) (N : ℕ) :
    Submodule ℂ (Std ds) where
  carrier := {f | ∀ w : List M, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : G,
    ‖B (standardDerivativeWord w f) g‖ ≤ C * realMatrixHeight g ^ N}
  zero_mem' := fun _ => ⟨0, le_rfl, fun _ => by simp⟩
  add_mem' := by
    intro f h hf hh w
    obtain ⟨C, hC, hb⟩ := hf w
    obtain ⟨D, hD, hd⟩ := hh w
    refine ⟨C + D, add_nonneg hC hD, fun g => ?_⟩
    simp only [map_add, Pi.add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hb g) (hd g))
  smul_mem' := by
    intro c f hf w
    obtain ⟨C, hC, hb⟩ := hf w
    refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, fun g => ?_⟩
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb g) (norm_nonneg _)

private theorem boundedWords_lie {ds : List RealBlock} (B : Std ds →ₗ[ℂ] (G → ℂ)) (N : ℕ)
    (X : ℂ ⊗[ℝ] M) (f : Std ds) (hf : f ∈ boundedWords B N) :
    realStandardLie n ds X f ∈ boundedWords B N := by
  refine TensorProduct.inductionOn X ?_ ?_
  · intro c X
    rw [op_tmul, LinearMap.smul_apply]
    apply Submodule.smul_mem
    intro w
    simpa only [wordOp_append, wordOp_singleton, Module.End.mul_apply] using hf (w ++ [X])
  · intro X Y hX hY
    simpa only [map_add, LinearMap.add_apply] using (boundedWords B N).add_mem hX hY

private theorem wordOp_compact {ds : List RealBlock} (k : Matrix.unitaryGroup I ℝ)
    (f : Std ds) (w : List M) :
    standardDerivativeWord w (realStandardRep n ds k f) =
      realStandardRep n ds k
        (standardDerivativeWord (w.map fun X => (k⁻¹).val * X * (star k⁻¹).val) f) := by
  let ρ := realStandardRep n ds
  let π := realStandardLie n ds
  have hki (v : Std ds) : ρ k (ρ k⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hik (v : Std ds) : ρ k⁻¹ (ρ k v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hc (X : M) (v : Std ds) :
      op π X (ρ k v) = ρ k (op π ((k⁻¹).val * X * (star k⁻¹).val) v) := by
    have h := (isRealGKModule_realStandardModule n ds).2.2.2 k⁻¹ X (ρ k v)
    change ρ k⁻¹ (op π X (ρ k v)) = op π ((k⁻¹).val * X * (star k⁻¹).val) (ρ k⁻¹ (ρ k v)) at h
    rw [hik] at h
    simpa only [hki] using congrArg (ρ k) h
  induction w with
  | nil => rfl
  | cons X w ih =>
    simp only [wordOp_cons, List.map_cons, Module.End.mul_apply, ih]
    exact hc _ _

private theorem boundedWords_compact {ds : List RealBlock} {a : ℝˣ}
    {B : Std ds →ₗ[ℂ] (G → ℂ)} (hB : IsRealWhittakerIntertwiner r ds a B) (N : ℕ)
    (k : Matrix.unitaryGroup I ℝ) (f : Std ds) (hf : f ∈ boundedWords B N) :
    realStandardRep n ds k f ∈ boundedWords B N := by
  intro w
  let w' := w.map fun X : M => (k⁻¹).val * X * (star k⁻¹).val
  let f' : Std ds := standardDerivativeWord w' f
  let k' : unitaryCompact ℝ n := ⟨Unitary.toUnits k, k.property⟩
  obtain ⟨C, hC, hb⟩ := hf w'
  have hcoef := hB.2.2.2.1 k' f' (realStandardRep n ds k f')
    (realStandardRep_apply_coe n ds k f')
  refine ⟨C * realMatrixHeight k'.val ^ N, by
    exact mul_nonneg hC (pow_nonneg (RealPlaceRestriction.realMatrixHeight_nonneg _) _), fun g => ?_⟩
  rw [wordOp_compact, show standardDerivativeWord w' f = f' from rfl, hcoef]
  change ‖B f' (g * k'.val)‖ ≤ _
  calc
    _ ≤ C * realMatrixHeight (g * k'.val) ^ N := hb _
    _ ≤ C * (realMatrixHeight g * realMatrixHeight k'.val) ^ N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (RealPlaceRestriction.realMatrixHeight_nonneg _)
        (realMatrixHeight_mul_le _ _) _) hC
    _ = _ := by rw [mul_pow]; ring

private theorem bounded_directions (w : List M) : ∃ D : ℝ, 0 ≤ D ∧ ∀ X ∈ w, ‖X‖ ≤ D := by
  induction w with
  | nil => exact ⟨0, le_rfl, by simp⟩
  | cons X w ih =>
    obtain ⟨D, hD, h⟩ := ih
    refine ⟨max ‖X‖ D, hD.trans (le_max_right _ _), fun Y hY => ?_⟩
    rcases List.mem_cons.mp hY with rfl | hY
    · exact le_max_left _ _
    · exact (h Y hY).trans (le_max_right _ _)

/-- Every ordinary coefficient map on an irreducible real standard module has
one polynomial height exponent for all its standard vectors. -/
theorem isUniform_of_irreducible {ds : List RealBlock} {a : ℝˣ}
    {B : Std ds →ₗ[ℂ] (G → ℂ)} (hB : IsRealWhittakerIntertwiner r ds a B)
    (hI : IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds)) :
    IsRealUniformWhittakerIntertwiner r ds a B := by
  let : Nontrivial (Std ds) := hI.1
  obtain ⟨f, hf⟩ := exists_ne (0 : Std ds)
  obtain ⟨N, hwords⟩ := exists_realWhittaker_right_word_growth hB f
  have hF : f ∈ boundedWords B N := by
    intro w
    obtain ⟨D, hD, hw⟩ := bounded_directions w
    obtain ⟨C, hC, hgrowth⟩ := hwords D hD
    exact ⟨C w.length, hC _, hgrowth w hw⟩
  have htop : boundedWords B N = ⊤ :=
    (hI.2 _ (boundedWords_compact hB N) (boundedWords_lie B N)).resolve_left fun he => by
      have hz : f ∈ (⊥ : Submodule ℂ (Std ds)) := he ▸ hF
      exact hf (by simpa only [Submodule.mem_bot] using hz)
  refine ⟨hB, N, fun v => ?_⟩
  have hv : v ∈ boundedWords B N := by rw [htop]; exact Submodule.mem_top
  simpa only [wordOp_nil, Module.End.one_apply] using hv ([] : List M)

/-- For irreducible real standard modules the ordinary moderate-growth
and uniform-growth coefficient submodules coincide. -/
def RealIrreducibleWhittakerModelUniformityStatement : Prop :=
  ∀ (m : ℕ) (ds : List RealBlock) (a : ℝˣ),
    IsIrreducibleGKModule (realStandardRep (m + 1) ds) (realStandardLie (m + 1) ds) →
      realWhittakerModel m ds a = realUniformWhittakerModel m ds a

theorem realIrreducibleWhittakerModelUniformity :
    RealIrreducibleWhittakerModelUniformityStatement := by
  intro m ds a hI
  apply le_antisymm ?_ (RealUniformWhittaker.model_le_model ds a)
  refine iSup₂_le fun B hB => ?_
  exact le_iSup_of_le B (le_iSup_of_le (isUniform_of_irreducible hB hI) le_rfl)

end Langlands.Global.RankinSelbergGlobal.RealWhittakerElliptic
