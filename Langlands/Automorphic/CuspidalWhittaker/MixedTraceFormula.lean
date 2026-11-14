import Langlands.Automorphic.CuspidalWhittaker.AdelicCharacter

/-!
# The trace on the mixed space in coordinates

The Library's `CuspidalWhittaker.mixedTrace` is the `ℝ`-linear map on the mixed space
`ℝ^{r₁} × ℂ^{r₂}` of a number field that extends the trace `Tr_{K/ℚ}` along the lattice
basis. This module computes it in coordinates: it is `x ↦ ∑_{v real} x_v + ∑_{w complex}
2 Re x_w`, and evaluates it on vectors supported at a single place.
-/

noncomputable section

universe u

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Finset
open scoped Classical

namespace Langlands.Automorphic.CuspidalWhittaker

variable (K : Type u) [Field K] [NumberField K]

/-- The coordinate trace on the mixed space: the sum of the real coordinates and of twice
the real parts of the complex coordinates. -/
def coordinateTrace : mixedSpace K →ₗ[ℝ] ℝ where
  toFun x := (∑ w, x.1 w) + ∑ w, 2 * (x.2 w).re
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Complex.add_re, mul_add,
      sum_add_distrib]
    ring
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.re_ofReal_mul, RingHom.id_apply, mul_sum, mul_add]
    congr 1
    refine sum_congr rfl fun w _ => ?_
    ring

theorem coordinateTrace_apply (x : mixedSpace K) :
    coordinateTrace K x = (∑ w, x.1 w) + ∑ w, 2 * (x.2 w).re := rfl

/-- The trace of `x ∈ K` is the sum over the infinite places `w` of `mult w` times the real
part of `w.embedding x`. -/
theorem trace_eq_sum_mult_re (x : K) :
    ((Algebra.trace ℚ K x : ℚ) : ℝ) =
      ∑ w : InfinitePlace K, (mult w : ℝ) * (w.embedding x).re := by
  classical
  have h := congrArg Complex.re (trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := x))
  rw [Complex.re_sum] at h
  have hl : (algebraMap ℚ ℂ (Algebra.trace ℚ K x)).re = ((Algebra.trace ℚ K x : ℚ) : ℝ) := by
    rw [eq_ratCast, Complex.ratCast_re]
  rw [hl] at h
  rw [h, Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ).symm (fun σ => (σ x).re)
    (fun φ => (φ x).re) (fun σ => rfl)]
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun φ => (φ x).re)]
  refine sum_congr rfl fun w _ => ?_
  have hre : ∀ φ ∈ ({φ | InfinitePlace.mk φ = w} : Finset (K →+* ℂ)),
      (φ x).re = (w.embedding x).re := by
    intro φ hφ
    rw [← (Finset.mem_filter.mp hφ).2]
    rcases embedding_mk_eq φ with h | h <;> rw [h]
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  rw [sum_congr rfl hre, sum_const, card_filter_mk_eq, nsmul_eq_mul]

/-- The coordinate trace of the mixed embedding is the trace. -/
theorem coordinateTrace_mixedEmbedding (x : K) :
    coordinateTrace K (mixedEmbedding K x) = ((Algebra.trace ℚ K x : ℚ) : ℝ) := by
  classical
  rw [trace_eq_sum_mult_re, coordinateTrace_apply,
    ← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace K => IsReal w)]
  congr 1
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [mixedEmbedding_apply_isReal, mult_isReal, Nat.cast_one, one_mul,
      ← embedding_of_isReal_apply w.2 x, Complex.ofReal_re]
  · refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun w => not_isReal_iff_isComplex).symm
      _ _ fun w => ?_
    rw [mixedEmbedding_apply_isComplex]
    change 2 * ((w : InfinitePlace K).embedding x).re =
      (mult (w : InfinitePlace K) : ℝ) * ((w : InfinitePlace K).embedding x).re
    rw [mult_isComplex, Nat.cast_ofNat]

/-- **The trace on the mixed space in coordinates.** -/
theorem mixedTrace_eq_coordinateTrace : mixedTrace K = coordinateTrace K := by
  refine (latticeBasis K).ext fun i => ?_
  rw [mixedTrace, Module.Basis.constr_basis, latticeBasis_apply, coordinateTrace_mixedEmbedding]

theorem mixedTrace_apply (x : mixedSpace K) :
    mixedTrace K x = (∑ w, x.1 w) + ∑ w, 2 * (x.2 w).re := by
  rw [mixedTrace_eq_coordinateTrace, coordinateTrace_apply]

/-- At a real place the mixed trace is the coordinate. -/
theorem mixedTrace_single_real (v : {w : InfinitePlace K // IsReal w}) (s : ℝ) :
    mixedTrace K (Pi.single v s, 0) = s := by
  classical
  rw [mixedTrace_apply]
  simp

/-- At a complex place the mixed trace is twice the real part of the coordinate. -/
theorem mixedTrace_single_complex (v : {w : InfinitePlace K // IsComplex w}) (z : ℂ) :
    mixedTrace K (0, Pi.single v z) = 2 * z.re := by
  rw [mixedTrace_apply]
  simp only [Pi.zero_apply, sum_const_zero, zero_add]
  rw [Finset.sum_eq_single v (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
  simp

end Langlands.Automorphic.CuspidalWhittaker
