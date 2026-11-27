import Langlands.Algebra.RestrictScalarsTrace
import Langlands.Global.InfiniteAdelicTangentKernel

/-! # Real traces of `F_∞`-linear maps

With the pinned `RCLike` structures on the archimedean completions, `F_∞ = Π_v F_v` is a finite
free `ℝ`-algebra. For an `F_∞`-linear endomorphism `f` of a finite free `F_∞`-module, the real
trace of `f` is `Σ_v mult(v) · Re (tr_{F_∞} f)_v`. -/

noncomputable section

universe u

open NumberField

set_option autoImplicit false

namespace Langlands.Global.InfiniteAdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]

/-- The `ℝ`-algebra structure of `F_∞ = Π_v F_v` given by the pinned `RCLike` structures of the
completions. -/
@[reducible] def realAlgebra : Algebra ℝ (InfiniteAdeleRing F) := by
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  exact Pi.algebra _ _

omit [NumberField F] in
theorem realAlgebra_algebraMap (r : ℝ) :
    letI := realAlgebra F
    algebraMap ℝ (InfiniteAdeleRing F) r = realAdele F r :=
  rfl

omit [NumberField F] in
/-- At an infinite place, the imaginary unit of the pinned `RCLike` structure vanishes exactly
when the place is real. -/
theorem completion_I_eq_zero_iff (v : InfinitePlace F) :
    letI := InfinitePlaceGroupPoints.completionRCLike F v
    (RCLike.I : v.Completion) = 0 ↔ v.IsReal := by
  let := InfinitePlaceGroupPoints.completionRCLike F v
  constructor
  · intro h
    by_contra hv
    have hc : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
    let e1 : v.Completion ≃+* ℂ := InfinitePlace.Completion.ringEquivComplexOfIsComplex hc
    let e2 : v.Completion ≃+* ℝ := RCLike.realRingEquiv h
    have hx : e2 (e1.symm Complex.I) * e2 (e1.symm Complex.I) = -1 := by
      rw [← map_mul, ← map_mul, Complex.I_mul_I, map_neg, map_one, map_neg, map_one]
    nlinarith [mul_self_nonneg (e2 (e1.symm Complex.I))]
  · intro hv
    by_contra h
    let e : v.Completion ≃+* ℝ := InfinitePlace.Completion.ringEquivRealOfIsReal hv
    have hI : (RCLike.I : v.Completion) * RCLike.I = -1 := RCLike.I_mul_I_of_nonzero h
    have hx : e RCLike.I * e RCLike.I = -1 := by rw [← map_mul, hI, map_neg, map_one]
    nlinarith [mul_self_nonneg (e RCLike.I)]

omit [NumberField F] in
/-- The real trace on an archimedean completion is `mult(v) · Re`. -/
theorem algebraTrace_completion (v : InfinitePlace F) (z : v.Completion) :
    letI := InfinitePlaceGroupPoints.completionRCLike F v
    Algebra.trace ℝ v.Completion z = (v.mult : ℝ) * RCLike.re z := by
  let := InfinitePlaceGroupPoints.completionRCLike F v
  by_cases hv : v.IsReal
  · rw [Langlands.Algebra.RestrictScalarsTrace.algebraTrace_of_I_eq_zero v.Completion
      ((completion_I_eq_zero_iff F v).mpr hv), hv.mult_eq_one]
    simp
  · rw [Langlands.Algebra.RestrictScalarsTrace.algebraTrace_of_I_ne_zero v.Completion
      (fun h => hv ((completion_I_eq_zero_iff F v).mp h)),
      (InfinitePlace.not_isReal_iff_isComplex.mp hv).mult_eq_two]
    simp

/-- The real trace on `F_∞` is `Σ_v mult(v) · Re`. -/
theorem algebraTrace_infiniteAdeleRing (x : InfiniteAdeleRing F) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := realAlgebra F
    Algebra.trace ℝ (InfiniteAdeleRing F) x = ∑ v, (v.mult : ℝ) * RCLike.re (x v) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := realAlgebra F
  classical
  have h := Langlands.Algebra.RestrictScalarsTrace.algebraTrace_pi (R := ℝ)
    (S := fun v : InfinitePlace F => v.Completion) x
  refine h.trans (Finset.sum_congr rfl fun v _ => ?_)
  exact algebraTrace_completion F v (x v)

/-- The real trace of an `F_∞`-linear endomorphism of a finite free `F_∞`-module is
`Σ_v mult(v) · Re` of its `F_∞`-trace. -/
theorem trace_restrictScalars_eq_sum {M : Type*} [AddCommGroup M]
    [Module (InfiniteAdeleRing F) M] [Module.Free (InfiniteAdeleRing F) M]
    [Module.Finite (InfiniteAdeleRing F) M] [Module ℝ M]
    (hM : letI := realAlgebra F; IsScalarTower ℝ (InfiniteAdeleRing F) M)
    (f : M →ₗ[InfiniteAdeleRing F] M) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := realAlgebra F
    haveI := hM
    LinearMap.trace ℝ M (f.restrictScalars ℝ) =
      ∑ v, (v.mult : ℝ) * RCLike.re ((LinearMap.trace (InfiniteAdeleRing F) M f) v) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := realAlgebra F
  have := hM
  have : Module.Finite ℝ (InfiniteAdeleRing F) :=
    (inferInstance : Module.Finite ℝ ((v : InfinitePlace F) → v.Completion))
  have : Module.Free ℝ (InfiniteAdeleRing F) :=
    (inferInstance : Module.Free ℝ ((v : InfinitePlace F) → v.Completion))
  rw [Langlands.Algebra.RestrictScalarsTrace.trace_restrictScalars,
    algebraTrace_infiniteAdeleRing]

end Langlands.Global.InfiniteAdelicGroupPoints
