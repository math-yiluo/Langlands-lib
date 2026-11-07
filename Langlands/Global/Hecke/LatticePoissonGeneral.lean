import Langlands.Global.Hecke.LatticePoisson
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Poisson summation for lattices in finite-dimensional real spaces

We transport Poisson summation on `ℤ^ι` (`Langlands.Global.Hecke.LatticePoisson`) to a full
lattice `L` in a finite-dimensional real normed space `E` equipped with a Haar measure `μ` and a
nondegenerate bilinear form `B`. The Fourier transform is Mathlib's
`VectorFourier.fourierIntegral 𝐞 μ B`, and the dual lattice is `B.flip.dualSubmodule L`. The
hypothesis on the function is polynomial decay of order `r > dim E`.

## Main results

* `tsum_add_latticeVec_eq`: Poisson summation for the lattice spanned by a basis `b` of `E`.
* `tsum_add_zlattice_eq`: `∑ l ∈ L, G (x + l) = covol(L)⁻¹ * ∑ w ∈ L^*, 𝓕 G w * e(B x w)`.
* `summable_add_zlattice_of_decay`, `summable_dualSubmodule_of_decay`: summability on `L` and
  on `L^*` under polynomial decay.
-/

open MeasureTheory Set TopologicalSpace Module
open scoped Real FourierTransform

noncomputable section

namespace Langlands.Global.Hecke

/-! ### Lattice vectors of a basis -/

section LatticeVec

variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

/-- The vector `∑ i, n i • b i` of the lattice spanned by a basis `b`. -/
def latticeVec (b : Basis ι ℝ E) (n : ι → ℤ) : E := b.equivFun.symm (intVec n)

lemma latticeVec_eq_sum (b : Basis ι ℝ E) (n : ι → ℤ) :
    latticeVec b n = ∑ i, (n i : ℝ) • b i := by
  simp [latticeVec, Basis.equivFun_symm_apply]

@[simp] lemma repr_latticeVec (b : Basis ι ℝ E) (n : ι → ℤ) (i : ι) :
    b.repr (latticeVec b n) i = n i := by
  rw [latticeVec_eq_sum, b.repr_sum_self]

lemma latticeVec_mem (b : Basis ι ℝ E) (n : ι → ℤ) :
    latticeVec b n ∈ Submodule.span ℤ (Set.range b) := by
  rw [b.mem_span_iff_repr_mem ℤ]
  intro i
  exact ⟨n i, by simp⟩

@[simp] lemma latticeVec_add (b : Basis ι ℝ E) (m n : ι → ℤ) :
    latticeVec b (m + n) = latticeVec b m + latticeVec b n := by
  rw [latticeVec, latticeVec, latticeVec, intVec_add, map_add]

/-- Integer coordinate vectors parametrize the lattice spanned by a basis. -/
def spanEquiv (b : Basis ι ℝ E) : (ι → ℤ) ≃ Submodule.span ℤ (Set.range b) where
  toFun n := ⟨latticeVec b n, latticeVec_mem b n⟩
  invFun x := fun i => ⌊b.repr x i⌋
  left_inv n := by ext i; simp
  right_inv x := by
    have hx := (b.mem_span_iff_repr_mem ℤ (x : E)).mp x.2
    choose k hk using hx
    ext1
    apply b.repr.injective
    ext i
    simp only [repr_latticeVec]
    rw [← hk i]
    simp

@[simp] lemma coe_spanEquiv (b : Basis ι ℝ E) (n : ι → ℤ) :
    (spanEquiv b n : E) = latticeVec b n := rfl

end LatticeVec

/-! ### Polynomial decay and local uniform summability -/

lemma rpow_neg_le_of_le_mul {a b c r : ℝ} (ha : 0 < a) (hc : 0 < c) (hr : 0 ≤ r)
    (h : a ≤ c * b) : b ^ (-r) ≤ c ^ r * a ^ (-r) := by
  have h1 : a / c ≤ b := by rw [div_le_iff₀ hc]; linarith [mul_comm c b]
  calc b ^ (-r) ≤ (a / c) ^ (-r) :=
        Real.rpow_le_rpow_of_nonpos (div_pos ha hc) h1 (by linarith)
    _ = c ^ r * a ^ (-r) := by
      rw [Real.div_rpow ha.le hc.le, Real.rpow_neg hc.le, div_inv_eq_mul, mul_comm]

section Decay

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The series `∑ n, (1 + ‖∑ i, n i • b i‖) ^ (-r)` converges for `r > dim E`. -/
lemma summable_one_add_norm_latticeVec_rpow (b : Basis ι ℝ E) {r : ℝ}
    (hr : (finrank ℝ E : ℝ) < r) :
    Summable fun n : ι → ℤ => (1 + ‖latticeVec b n‖) ^ (-r) := by
  set L := Submodule.span ℤ (Set.range b)
  have hrank : finrank ℤ L = finrank ℝ E := ZLattice.rank ℝ L
  have hL : Summable fun z : L => ‖z‖ ^ (-r) :=
    ZLattice.summable_norm_rpow L (-r) (by rw [hrank]; linarith)
  have hL' : Summable fun z : L => (1 + ‖(z : E)‖) ^ (-r) := by
    refine hL.of_norm_bounded_eventually ?_
    filter_upwards [Filter.eventually_cofinite_ne 0] with z hz
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hz' : ‖(z : E)‖ = ‖z‖ := rfl
    rw [Real.norm_of_nonneg (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos hpos (by rw [hz']; linarith)
      (by linarith [(Nat.cast_nonneg (finrank ℝ E) : (0 : ℝ) ≤ _)])
  exact (spanEquiv b).summable_iff.mpr hL'

/-- A continuous function on `E`, read in the coordinates of a basis `b`. -/
def basisCoord (b : Basis ι ℝ E) (G : C(E, ℂ)) : C(ι → ℝ, ℂ) :=
  G.comp ⟨b.equivFunL.symm, b.equivFunL.symm.continuous⟩

omit [FiniteDimensional ℝ E] in
lemma basisCoord_apply (b : Basis ι ℝ E) (G : C(E, ℂ)) (t : ι → ℝ) :
    basisCoord b G t = G (b.equivFunL.symm t) := rfl

omit [FiniteDimensional ℝ E] in
lemma equivFunL_symm_intVec (b : Basis ι ℝ E) (n : ι → ℤ) :
    b.equivFunL.symm (intVec n) = latticeVec b n := rfl

omit [FiniteDimensional ℝ E] in
lemma basisCoord_add_intVec (b : Basis ι ℝ E) (G : C(E, ℂ)) (t : ι → ℝ) (n : ι → ℤ) :
    basisCoord b G (t + intVec n) = G (b.equivFunL.symm t + latticeVec b n) := by
  rw [basisCoord_apply, map_add, equivFunL_symm_intVec]

omit [FiniteDimensional ℝ E] in
lemma basisCoord_equivFunL (b : Basis ι ℝ E) (G : C(E, ℂ)) (v : E) :
    basisCoord b G (b.equivFunL v) = G v := by
  rw [basisCoord_apply, ContinuousLinearEquiv.symm_apply_apply]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma nonneg_of_decay {G : E → ℂ} {C r : ℝ} (hdecay : ∀ v, ‖G v‖ ≤ C * (1 + ‖v‖) ^ (-r)) :
    0 ≤ C := by
  have := (norm_nonneg _).trans (hdecay 0)
  simpa using this

/-- If `‖G v‖ ≤ C (1 + ‖v‖)^(-r)` with `r > dim E`, then the lattice translates of `G` (in the
coordinates of `b`) are locally uniformly summable. -/
lemma summable_norm_restrict_of_decay (b : Basis ι ℝ E) (G : C(E, ℂ)) {C r : ℝ}
    (hr : (finrank ℝ E : ℝ) < r) (hdecay : ∀ v, ‖G v‖ ≤ C * (1 + ‖v‖) ^ (-r))
    (K : Compacts (ι → ℝ)) :
    Summable fun n : ι → ℤ =>
      ‖((basisCoord b G).comp (ContinuousMap.addRight (intVec n))).restrict K‖ := by
  obtain ⟨R, hR⟩ := K.isCompact.exists_bound_of_continuousOn
    (b.equivFunL.symm.continuous.continuousOn (s := (K : Set (ι → ℝ))))
  have hC := nonneg_of_decay hdecay
  have hr0 : 0 ≤ r := le_trans (Nat.cast_nonneg _) hr.le
  have hR0 : 0 ≤ max R 0 := le_max_right _ _
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_one_add_norm_latticeVec_rpow b hr).mul_left (C * (1 + max R 0) ^ r))
  refine (ContinuousMap.norm_le _ (by positivity)).mpr fun t => ?_
  simp only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_addRight, basisCoord_add_intVec]
  set y := b.equivFunL.symm (t : ι → ℝ)
  have hy : ‖y‖ ≤ max R 0 := (hR t t.2).trans (le_max_left _ _)
  refine (hdecay _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC
  refine rpow_neg_le_of_le_mul (by positivity) (by positivity) hr0 ?_
  have h := norm_sub_le (y + latticeVec b n) y
  rw [add_sub_cancel_left] at h
  nlinarith [norm_nonneg (y + latticeVec b n), mul_nonneg hR0 (norm_nonneg (y + latticeVec b n))]

/-- Under polynomial decay of order `r > dim E`, the translates of `G` by the lattice spanned by
`b` are summable. -/
lemma summable_add_latticeVec_of_decay (b : Basis ι ℝ E) {G : E → ℂ} {C r : ℝ}
    (hr : (finrank ℝ E : ℝ) < r) (hdecay : ∀ v, ‖G v‖ ≤ C * (1 + ‖v‖) ^ (-r)) (x : E) :
    Summable fun n : ι → ℤ => G (x + latticeVec b n) := by
  have hC := nonneg_of_decay hdecay
  have hr0 : 0 ≤ r := le_trans (Nat.cast_nonneg _) hr.le
  refine Summable.of_norm_bounded
    ((summable_one_add_norm_latticeVec_rpow b hr).mul_left (C * (1 + ‖x‖) ^ r)) fun n => ?_
  refine (hdecay _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC
  refine rpow_neg_le_of_le_mul (by positivity) (by positivity) hr0 ?_
  have h := norm_sub_le (x + latticeVec b n) x
  rw [add_sub_cancel_left] at h
  nlinarith [norm_nonneg (x + latticeVec b n), mul_nonneg (norm_nonneg x)
    (norm_nonneg (x + latticeVec b n))]

end Decay

/-! ### Change of variables to coordinates -/

section Measure

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] in
lemma map_equivFunL_eq_smul_volume (b : Basis ι ℝ E) :
    Measure.map b.equivFunL μ = μ (parallelepiped b) • volume := by
  rw [Measure.addHaarMeasure_unique (Measure.map b.equivFunL μ) (PositiveCompacts.piIcc01 ι),
    addHaarMeasure_eq_volume_pi]
  congr 1
  rw [Measure.map_apply b.equivFunL.continuous.measurable
    (PositiveCompacts.piIcc01 ι).isCompact.measurableSet]
  congr 1
  ext x
  simp [PositiveCompacts.piIcc01, parallelepiped_basis_eq b, Pi.le_def, forall_and]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measureReal_parallelepiped_pos (b : Basis ι ℝ E) : 0 < μ.real (parallelepiped b) := by
  rw [measureReal_def]
  refine ENNReal.toReal_pos ?_ ?_
  · exact (Measure.measure_pos_of_nonempty_interior μ b.parallelepiped.interior_nonempty).ne'
  · exact b.parallelepiped.isCompact.measure_lt_top.ne

omit [FiniteDimensional ℝ E] in
lemma integral_comp_equivFunL (b : Basis ι ℝ E) (g : (ι → ℝ) → ℂ) :
    ∫ v, g (b.equivFunL v) ∂μ = μ.real (parallelepiped b) • ∫ t, g t := by
  have h := integral_map_equiv (μ := μ) b.equivFunL.toHomeomorph.toMeasurableEquiv g
  change ∫ y, g y ∂Measure.map b.equivFunL μ = ∫ x, g (b.equivFunL x) ∂μ at h
  rw [← h, map_equivFunL_eq_smul_volume, integral_smul_measure, measureReal_def]

end Measure

/-! ### Poisson summation for the lattice of a basis -/

section BasisPoisson

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
  {B : LinearMap.BilinForm ℝ E} (hB : B.Nondegenerate)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
include hB in
lemma apply_dualBasis_flip_eq_repr (b : Basis ι ℝ E) (v : E) (j : ι) :
    B v (B.flip.dualBasis hB.flip b j) = b.repr v j := by
  conv_rhs => rw [← B.dualBasis_dualBasis_flip hB b]
  rw [LinearMap.BilinForm.dualBasis_repr_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
include hB in
lemma apply_latticeVec_dualBasis_flip (b : Basis ι ℝ E) (v : E) (m : ι → ℤ) :
    B v (latticeVec (B.flip.dualBasis hB.flip b) m) = intDot m (b.equivFunL v) := by
  simp [latticeVec_eq_sum, map_sum, map_smul, apply_dualBasis_flip_eq_repr hB, intDot]

omit [FiniteDimensional ℝ E] in
lemma intFourier_basisCoord (b : Basis ι ℝ E) (G : C(E, ℂ)) (m : ι → ℤ) :
    intFourier (basisCoord b G) m =
      (μ.real (parallelepiped b))⁻¹ •
        VectorFourier.fourierIntegral 𝐞 μ B G (latticeVec (B.flip.dualBasis hB.flip b) m) := by
  have hc := measureReal_parallelepiped_pos μ b
  have h := integral_comp_equivFunL μ b fun t => 𝐞 (-intDot m t) • basisCoord b G t
  simp only [basisCoord_equivFunL] at h
  rw [VectorFourier.fourierIntegral]
  simp_rw [apply_latticeVec_dualBasis_flip hB]
  rw [h, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  rfl

/-- **Poisson summation for the lattice spanned by a basis.** Let `b` be a basis of `E`, `B` a
nondegenerate bilinear form, and `b'` the basis with `B (b i) (b' j) = δ i j`. If `G` decays like
`(1 + ‖v‖)^(-r)` with `r > dim E` and its Fourier transform is summable on the lattice of `b'`, then
`∑ n, G (x + n • b) = vol(b)⁻¹ * ∑ m, 𝓕 G (m • b') * e(B x (m • b'))`. -/
theorem tsum_add_latticeVec_eq (b : Basis ι ℝ E) (G : C(E, ℂ)) {C r : ℝ}
    (hr : (finrank ℝ E : ℝ) < r) (hdecay : ∀ v, ‖G v‖ ≤ C * (1 + ‖v‖) ^ (-r))
    (h_sum : Summable fun m : ι → ℤ =>
      VectorFourier.fourierIntegral 𝐞 μ B G (latticeVec (B.flip.dualBasis hB.flip b) m))
    (x : E) :
    ∑' n : ι → ℤ, G (x + latticeVec b n) =
      (μ.real (parallelepiped b))⁻¹ * ∑' m : ι → ℤ,
        VectorFourier.fourierIntegral 𝐞 μ B G (latticeVec (B.flip.dualBasis hB.flip b) m) *
          𝐞 (B x (latticeVec (B.flip.dualBasis hB.flip b) m)) := by
  have hFour : intFourier (basisCoord b G) = fun m => (μ.real (parallelepiped b))⁻¹ •
      VectorFourier.fourierIntegral 𝐞 μ B G (latticeVec (B.flip.dualBasis hB.flip b) m) :=
    funext (intFourier_basisCoord μ hB b G)
  have hs : Summable (intFourier (basisCoord b G)) := by
    rw [hFour]; exact h_sum.const_smul _
  have h := tsum_add_intVec_eq_tsum_intFourier
    (summable_norm_restrict_of_decay b G hr hdecay) hs (b.equivFunL x)
  simp only [basisCoord_add_intVec, ContinuousLinearEquiv.symm_apply_apply, hFour,
    ← apply_latticeVec_dualBasis_flip hB] at h
  rw [h, ← tsum_mul_left]
  congr 1
  ext m
  rw [Complex.real_smul, mul_assoc]

end BasisPoisson

/-! ### Poisson summation for a lattice and its dual -/

section ZLatticePoisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {B : LinearMap.BilinForm ℝ E} (hB : B.Nondegenerate)
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The real basis of `E` underlying the chosen `ℤ`-basis of a lattice `L`. -/
def latticeBasis : Basis (Free.ChooseBasisIndex ℤ L) ℝ E :=
  (Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L

lemma span_latticeBasis : Submodule.span ℤ (Set.range (latticeBasis L)) = L :=
  (Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ L

include hB in
lemma dualSubmodule_eq_span :
    B.flip.dualSubmodule L =
      Submodule.span ℤ (Set.range (B.flip.dualBasis hB.flip (latticeBasis L))) := by
  classical
  conv_lhs => rw [← span_latticeBasis L]
  exact LinearMap.BilinForm.dualSubmodule_span_of_basis B.flip hB.flip (latticeBasis L)

/-- Integer coordinate vectors parametrize the lattice `L`. -/
def latticeEquiv : (Free.ChooseBasisIndex ℤ L → ℤ) ≃ L :=
  (spanEquiv (latticeBasis L)).trans (LinearEquiv.ofEq _ _ (span_latticeBasis L)).toEquiv

@[simp] lemma coe_latticeEquiv (n : Free.ChooseBasisIndex ℤ L → ℤ) :
    (latticeEquiv L n : E) = latticeVec (latticeBasis L) n := rfl

/-- Integer coordinate vectors parametrize the dual lattice of `L`. -/
def dualLatticeEquiv : (Free.ChooseBasisIndex ℤ L → ℤ) ≃ B.flip.dualSubmodule L :=
  (spanEquiv (B.flip.dualBasis hB.flip (latticeBasis L))).trans
    (LinearEquiv.ofEq _ _ (dualSubmodule_eq_span hB L).symm).toEquiv

@[simp] lemma coe_dualLatticeEquiv (m : Free.ChooseBasisIndex ℤ L → ℤ) :
    (dualLatticeEquiv hB L m : E) = latticeVec (B.flip.dualBasis hB.flip (latticeBasis L)) m :=
  rfl

/-- Under polynomial decay of order `r > dim E`, the translates of `G` by a lattice are
summable. -/
lemma summable_add_zlattice_of_decay {G : E → ℂ} {C r : ℝ}
    (hr : (finrank ℝ E : ℝ) < r) (hdecay : ∀ v, ‖G v‖ ≤ C * (1 + ‖v‖) ^ (-r)) (x : E) :
    Summable fun l : L => G (x + l) :=
  (latticeEquiv L).summable_iff.mp (summable_add_latticeVec_of_decay (latticeBasis L) hr hdecay x)

include hB in
/-- A function with polynomial decay of order `r > dim E` is summable on the dual lattice. -/
lemma summable_dualSubmodule_of_decay {F : E → ℂ} {C r : ℝ}
    (hr : (finrank ℝ E : ℝ) < r) (hdecay : ∀ v, ‖F v‖ ≤ C * (1 + ‖v‖) ^ (-r)) :
    Summable fun w : B.flip.dualSubmodule L => F w := by
  have h := summable_add_latticeVec_of_decay (B.flip.dualBasis hB.flip (latticeBasis L)) hr
    hdecay 0
  simp only [zero_add] at h
  exact (dualLatticeEquiv hB L).summable_iff.mp h

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

lemma covolume_eq_measureReal_parallelepiped :
    ZLattice.covolume L μ = μ.real (parallelepiped (latticeBasis L)) := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L μ
    (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) μ)]
  exact measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped (latticeBasis L) μ)

include hB in
/-- **Poisson summation for a lattice.** Let `L` be a full lattice in `E`, `μ` a Haar measure,
`B` a nondegenerate bilinear form, and `L^* = {w | ∀ l ∈ L, B l w ∈ ℤ}` the dual lattice. If `G`
decays like `(1 + ‖v‖)^(-r)` with `r > dim E` and its Fourier transform
`𝓕 G w = ∫ v, e(-B v w) G v ∂μ` is summable on `L^*`, then
`∑ l ∈ L, G (x + l) = covol(L)⁻¹ * ∑ w ∈ L^*, 𝓕 G w * e(B x w)`. -/
theorem tsum_add_zlattice_eq (G : C(E, ℂ)) {C r : ℝ}
    (hr : (finrank ℝ E : ℝ) < r) (hdecay : ∀ v, ‖G v‖ ≤ C * (1 + ‖v‖) ^ (-r))
    (h_sum : Summable fun w : B.flip.dualSubmodule L =>
      VectorFourier.fourierIntegral 𝐞 μ B G w)
    (x : E) :
    ∑' l : L, G (x + l) =
      (ZLattice.covolume L μ)⁻¹ * ∑' w : B.flip.dualSubmodule L,
        VectorFourier.fourierIntegral 𝐞 μ B G w * 𝐞 (B x w) := by
  classical
  have h_sum' : Summable fun m => VectorFourier.fourierIntegral 𝐞 μ B G
      (latticeVec (B.flip.dualBasis hB.flip (latticeBasis L)) m) :=
    (dualLatticeEquiv hB L).summable_iff.mpr h_sum
  rw [← (latticeEquiv L).tsum_eq, ← (dualLatticeEquiv hB L).tsum_eq,
    covolume_eq_measureReal_parallelepiped]
  simp only [coe_latticeEquiv, coe_dualLatticeEquiv]
  exact tsum_add_latticeVec_eq μ hB (latticeBasis L) G hr hdecay h_sum' x

end ZLatticePoisson

end Langlands.Global.Hecke

end
