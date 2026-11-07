import Langlands.Global.AdeleQuotientCompactProof
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# A standard additive character of `𝔸_K / K`

The trace `K → ℚ` extends `ℝ`-linearly to the infinite adeles through the mixed space. Every
finite adele is a rational number plus an integral one, `𝔸_K^f = K + ∏_v 𝒪_v`, so
`ψ(x) = e(Tr_∞(x_∞ - r))`, for any `r ∈ K` with `x_f - r` integral, is a well-defined continuous
additive character of `𝔸_K`, trivial on `K`, with `e(t) = exp(2πit)`. Its restriction to each
finite completion is trivial on the integers and nontrivial, and the annihilator of `K` under
`(a, y) ↦ ψ(a y)` is `K` itself.
-/

noncomputable section

universe u

open NumberField

namespace Langlands.Automorphic.CuspidalWhittaker

open Langlands.Global

/-! ### The exponential `t ↦ exp(2πit)` -/

/-- The unit-circle exponential `t ↦ exp(2πit)`. -/
def unitExp (t : ℝ) : Circle := Circle.exp (2 * Real.pi * t)

theorem unitExp_add (s t : ℝ) : unitExp (s + t) = unitExp s * unitExp t := by
  rw [unitExp, mul_add, Circle.exp_add]
  rfl

@[simp] theorem unitExp_zero : unitExp 0 = 1 := by
  simp [unitExp]

theorem unitExp_neg (t : ℝ) : unitExp (-t) = (unitExp t)⁻¹ := by
  rw [unitExp, mul_neg, Circle.exp_neg]
  rfl

theorem unitExp_eq_one_iff (t : ℝ) : unitExp t = 1 ↔ ∃ m : ℤ, t = m := by
  rw [unitExp, Circle.exp_eq_one]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have : 2 * Real.pi * t = 2 * Real.pi * m := by rw [hm]; ring
    exact mul_left_cancel₀ hpi this
  · rintro ⟨m, rfl⟩
    exact ⟨m, by ring⟩

theorem unitExp_intCast (m : ℤ) : unitExp m = 1 :=
  (unitExp_eq_one_iff _).mpr ⟨m, rfl⟩

theorem unitExp_add_intCast (t : ℝ) (m : ℤ) : unitExp (t + m) = unitExp t := by
  rw [unitExp_add, unitExp_intCast, mul_one]

theorem continuous_unitExp : Continuous unitExp :=
  Circle.exp.continuous.comp (continuous_const.mul continuous_id)

variable (K : Type u) [Field K] [NumberField K]

/-! ### The trace on the infinite adeles -/

/-- The `ℝ`-linear trace on the mixed space: the extension of `Tr_{K/ℚ}` along the lattice
basis `mixedEmbedding (integralBasis i)`. -/
def mixedTrace : mixedEmbedding.mixedSpace K →ₗ[ℝ] ℝ :=
  (mixedEmbedding.latticeBasis K).constr ℝ fun i =>
    ((Algebra.trace ℚ K (integralBasis K i) : ℚ) : ℝ)

theorem mixedTrace_mixedEmbedding (x : K) :
    mixedTrace K (mixedEmbedding K x) = ((Algebra.trace ℚ K x : ℚ) : ℝ) := by
  let f : K →+ ℝ := (mixedTrace K).toAddMonoidHom.comp (mixedEmbedding K).toAddMonoidHom
  let g : K →+ ℝ := (Rat.castHom ℝ).toAddMonoidHom.comp (Algebra.trace ℚ K).toAddMonoidHom
  have hfg : f.toRatLinearMap = g.toRatLinearMap := (integralBasis K).ext fun i => by
    change mixedTrace K (mixedEmbedding K (integralBasis K i)) = _
    rw [← mixedEmbedding.latticeBasis_apply, mixedTrace, Module.Basis.constr_basis]
    rfl
  exact LinearMap.congr_fun hfg x

/-- The trace on the infinite adeles, through the ring isomorphism with the mixed space. -/
def infiniteTrace : InfiniteAdeleRing K →+ ℝ :=
  (mixedTrace K).toAddMonoidHom.comp
    (InfiniteAdeleRing.ringEquiv_mixedSpace K).toAddEquiv.toAddMonoidHom

theorem infiniteTrace_apply (x : InfiniteAdeleRing K) :
    infiniteTrace K x = mixedTrace K (InfiniteAdeleRing.ringEquiv_mixedSpace K x) := rfl

theorem infiniteTrace_algebraMap (x : K) :
    infiniteTrace K (algebraMap K (InfiniteAdeleRing K) x) =
      ((Algebra.trace ℚ K x : ℚ) : ℝ) := by
  rw [infiniteTrace_apply, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
    mixedTrace_mixedEmbedding]

omit [NumberField K] in
theorem continuous_ringEquiv_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  have h : (InfiniteAdeleRing.ringEquiv_mixedSpace K :
      InfiniteAdeleRing K → mixedEmbedding.mixedSpace K) = fun x =>
      (fun v : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w} =>
        NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v.1),
       fun v : {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex w} =>
        NumberField.InfinitePlace.Completion.extensionEmbedding v.1 (x v.1)) :=
    funext fun x => InfiniteAdeleRing.ringEquiv_mixedSpace_apply K x
  rw [h]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)

theorem continuous_infiniteTrace : Continuous (infiniteTrace K) :=
  (LinearMap.continuous_of_finiteDimensional (mixedTrace K)).comp
    (continuous_ringEquiv_mixedSpace K)

/-- The trace of an element of `K` integral at every finite place is an integer. -/
theorem exists_int_trace_of_mem (x : K)
    (hx : algebraMap K (FiniteAdeles K) x ∈ integralFiniteAdeles K) :
    ∃ m : ℤ, ((Algebra.trace ℚ K x : ℚ) : ℝ) = m := by
  obtain ⟨a, rfl⟩ : x ∈ (algebraMap (RingOfIntegers K) K).range := by
    refine IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K x fun v => ?_
    have h := (mem_integralFiniteAdeles K _).mp hx v
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at h
    change Valued.v ((x : v.adicCompletion K)) ≤ 1 at h
    rwa [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  refine ⟨Algebra.trace ℤ (RingOfIntegers K) a, ?_⟩
  rw [Algebra.trace_localization ℤ (nonZeroDivisors ℤ) a]
  simp

/-! ### The global character -/

section Components

variable {K}

@[simp] theorem adeles_zero_fst : (0 : Adeles K).1 = 0 := rfl
@[simp] theorem adeles_zero_snd : (0 : Adeles K).2 = 0 := rfl
@[simp] theorem adeles_add_fst (x y : Adeles K) : (x + y).1 = x.1 + y.1 := rfl
@[simp] theorem adeles_add_snd (x y : Adeles K) : (x + y).2 = x.2 + y.2 := rfl
@[simp] theorem adeles_sub_fst (x y : Adeles K) : (x - y).1 = x.1 - y.1 := rfl
@[simp] theorem adeles_sub_snd (x y : Adeles K) : (x - y).2 = x.2 - y.2 := rfl
@[simp] theorem adeles_neg_fst (x : Adeles K) : (-x).1 = -x.1 := rfl
@[simp] theorem adeles_neg_snd (x : Adeles K) : (-x).2 = -x.2 := rfl
@[simp] theorem adeles_mul_fst (x y : Adeles K) : (x * y).1 = x.1 * y.1 := rfl
@[simp] theorem adeles_mul_snd (x y : Adeles K) : (x * y).2 = x.2 * y.2 := rfl
@[simp] theorem adeles_algebraMap_fst (a : K) :
    (algebraMap K (Adeles K) a).1 = algebraMap K (InfiniteAdeleRing K) a := rfl
@[simp] theorem adeles_algebraMap_snd (a : K) :
    (algebraMap K (Adeles K) a).2 = algebraMap K (FiniteAdeles K) a := rfl

theorem adeles_ext {x y : Adeles K} (h1 : x.1 = y.1) (h2 : x.2 = y.2) : x = y :=
  Prod.ext h1 h2

end Components

/-- A chosen `r ∈ K` with `a - r` integral, for a finite adele `a`. -/
def finiteShift (a : FiniteAdeles K) : K :=
  Classical.choose (exists_sub_mem_integralFiniteAdeles a)

theorem sub_finiteShift_mem (a : FiniteAdeles K) :
    a - algebraMap K (FiniteAdeles K) (finiteShift K a) ∈ integralFiniteAdeles K :=
  Classical.choose_spec (exists_sub_mem_integralFiniteAdeles a)

/-- The underlying function of the standard character. -/
def adelicCharacterFun (x : Adeles K) : Circle :=
  unitExp (infiniteTrace K (x.1 - algebraMap K (InfiniteAdeleRing K) (finiteShift K x.2)))

/-- The value of the character may be computed with any rational shift. -/
theorem adelicCharacterFun_eq (x : Adeles K) (r : K)
    (hr : x.2 - algebraMap K (FiniteAdeles K) r ∈ integralFiniteAdeles K) :
    adelicCharacterFun K x =
      unitExp (infiniteTrace K (x.1 - algebraMap K (InfiniteAdeleRing K) r)) := by
  have hmem : algebraMap K (FiniteAdeles K) (r - finiteShift K x.2) ∈ integralFiniteAdeles K := by
    have := sub_mem (sub_finiteShift_mem K x.2) hr
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  obtain ⟨m, hm⟩ := exists_int_trace_of_mem K _ hmem
  have : x.1 - algebraMap K (InfiniteAdeleRing K) (finiteShift K x.2) =
      (x.1 - algebraMap K (InfiniteAdeleRing K) r) +
        algebraMap K (InfiniteAdeleRing K) (r - finiteShift K x.2) := by
    rw [map_sub]; abel
  rw [adelicCharacterFun, this, map_add, infiniteTrace_algebraMap, hm, unitExp_add_intCast]

/-- The standard additive character `ψ` of `𝔸_K`. -/
def adelicCharacter : AddChar (Adeles K) Circle where
  toFun := adelicCharacterFun K
  map_zero_eq_one' := by
    rw [adelicCharacterFun_eq K 0 0 (by simp)]
    simp only [adeles_zero_fst, map_zero, sub_zero, unitExp_zero]
  map_add_eq_mul' x y := by
    have hr : (x + y).2 - algebraMap K (FiniteAdeles K) (finiteShift K x.2 + finiteShift K y.2) ∈
        integralFiniteAdeles K := by
      have := add_mem (sub_finiteShift_mem K x.2) (sub_finiteShift_mem K y.2)
      convert this using 1
      rw [map_add]
      change x.2 + y.2 - _ = _
      abel
    rw [adelicCharacterFun_eq K _ _ hr, adelicCharacterFun, adelicCharacterFun, ← unitExp_add,
      ← map_add, map_add]
    congr 2
    change x.1 + y.1 - _ = _
    abel

theorem adelicCharacter_apply (x : Adeles K) (r : K)
    (hr : x.2 - algebraMap K (FiniteAdeles K) r ∈ integralFiniteAdeles K) :
    adelicCharacter K x =
      unitExp (infiniteTrace K (x.1 - algebraMap K (InfiniteAdeleRing K) r)) :=
  adelicCharacterFun_eq K x r hr

/-- `ψ` is trivial on `K`. -/
theorem adelicCharacter_algebraMap (a : K) :
    adelicCharacter K (algebraMap K (Adeles K) a) = 1 := by
  rw [adelicCharacter_apply K _ a (by rw [adeles_algebraMap_snd, sub_self]; exact zero_mem _)]
  rw [adeles_algebraMap_fst, sub_self, map_zero, unitExp_zero]

/-- `ψ` is trivial on the integral finite adeles. -/
theorem adelicCharacter_of_integral (x : Adeles K) (hx : x.2 ∈ integralFiniteAdeles K) :
    adelicCharacter K x = unitExp (infiniteTrace K x.1) := by
  rw [adelicCharacter_apply K x 0 (by rwa [map_zero, sub_zero])]
  rw [map_zero, sub_zero]

theorem continuous_adelicCharacter : Continuous (adelicCharacter K) := by
  rw [continuous_iff_continuousAt]
  intro x
  let r := finiteShift K x.2
  have hopen : IsOpen {y : Adeles K | y.2 - x.2 ∈ integralFiniteAdeles K} :=
    (isOpen_integralFiniteAdeles K).preimage
      ((continuous_snd.sub continuous_const : Continuous fun y : Adeles K => y.2 - x.2))
  have hx : x ∈ {y : Adeles K | y.2 - x.2 ∈ integralFiniteAdeles K} := by
    change x.2 - x.2 ∈ integralFiniteAdeles K
    rw [sub_self]
    exact (integralFiniteAdeles K).zero_mem
  have heq : (adelicCharacter K : Adeles K → Circle) =ᶠ[nhds x]
      fun y => unitExp (infiniteTrace K (y.1 - algebraMap K (InfiniteAdeleRing K) r)) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    refine adelicCharacter_apply K y r ?_
    have := add_mem hy (sub_finiteShift_mem K x.2)
    rwa [sub_add_sub_cancel] at this
  refine ContinuousAt.congr ?_ heq.symm
  exact (continuous_unitExp.comp ((continuous_infiniteTrace K).comp
    (continuous_fst.sub continuous_const))).continuousAt

/-- `ψ` is not identically one: `ψ(1 / (2[K : ℚ]))` at the infinite places is `-1`. -/
theorem exists_adelicCharacter_ne_one : ∃ x : Adeles K, adelicCharacter K x ≠ 1 := by
  set d : ℕ := Module.finrank ℚ K
  have hd : (d : ℚ) ≠ 0 := by
    have : 0 < d := Module.finrank_pos
    exact_mod_cast this.ne'
  let q : ℚ := 1 / (2 * d)
  let x : Adeles K := (show Adeles K from (algebraMap K (InfiniteAdeleRing K) (algebraMap ℚ K q), 0))
  refine ⟨x, ?_⟩
  rw [adelicCharacter_of_integral K x (integralFiniteAdeles K).zero_mem]
  change unitExp (infiniteTrace K (algebraMap K (InfiniteAdeleRing K) (algebraMap ℚ K q))) ≠ 1
  rw [infiniteTrace_algebraMap, Algebra.trace_algebraMap, Ne, unitExp_eq_one_iff]
  rintro ⟨m, hm⟩
  have hq' : (d • q : ℚ) = 1 / 2 := by
    simp only [nsmul_eq_mul, q]
    field_simp
  have hq : ((d • q : ℚ) : ℝ) = 1 / 2 := by
    rw [hq']
    norm_num
  rw [hq] at hm
  have h2 : (2 * m : ℝ) = 1 := by linarith
  have h2' : (2 * m : ℤ) = 1 := by exact_mod_cast h2
  omega

/-! ### The trace dual basis -/

/-- The basis of `K` dual to the integral basis for the trace form. -/
def traceDualBasis : Module.Basis (Module.Free.ChooseBasisIndex ℤ (RingOfIntegers K)) ℚ K :=
  (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) (integralBasis K)

theorem trace_traceDualBasis_mul (i j : Module.Free.ChooseBasisIndex ℤ (RingOfIntegers K)) :
    Algebra.trace ℚ K (traceDualBasis K i * integralBasis K j) = if j = i then 1 else 0 := by
  have := LinearMap.BilinForm.apply_dualBasis_left (traceForm_nondegenerate ℚ K)
    (integralBasis K) i j
  rwa [Algebra.traceForm_apply] at this

theorem traceDualBasis_repr (x : K) (i : Module.Free.ChooseBasisIndex ℤ (RingOfIntegers K)) :
    (traceDualBasis K).repr x i = Algebra.trace ℚ K (x * integralBasis K i) := by
  rw [traceDualBasis, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]

/-- An element of `K` with integral traces against `𝒪_K` has bounded denominator. -/
theorem exists_dual_denominator : ∃ N : RingOfIntegers K, N ≠ 0 ∧ ∀ x : K,
    (∀ b : RingOfIntegers K, ∃ m : ℤ,
      Algebra.trace ℚ K (x * algebraMap (RingOfIntegers K) K b) = m) →
      algebraMap (RingOfIntegers K) K N * x ∈ (algebraMap (RingOfIntegers K) K).range := by
  classical
  obtain ⟨N, hN⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (RingOfIntegers K))
    (S := K) Finset.univ (traceDualBasis K)
  refine ⟨N, nonZeroDivisors.coe_ne_zero N, fun x hx => ?_⟩
  choose m hm using fun i => hx (RingOfIntegers.basis K i)
  have hx' : x = ∑ i, (m i : ℚ) • traceDualBasis K i := by
    conv_lhs => rw [← (traceDualBasis K).sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [traceDualBasis_repr, integralBasis_apply, hm i]
  rw [hx', Finset.mul_sum]
  refine Subring.sum_mem _ fun i _ => ?_
  obtain ⟨z, hz⟩ := hN i (Finset.mem_univ i)
  refine ⟨z * (m i : RingOfIntegers K), ?_⟩
  rw [map_mul, hz, Algebra.smul_def, map_intCast, Rat.smul_def, Rat.cast_intCast]
  ring

/-! ### Local components -/

local instance : DecidableEq (Global.FinitePlace K) := Classical.decEq _

/-- Insert a local element at one finite place, with zero at the others. -/
def finiteSingle (v : Global.FinitePlace K) : FiniteCompletion K v →+ FiniteAdeles K where
  toFun t := ⟨Pi.single v t, by
    filter_upwards [show ({v}ᶜ : Set (Global.FinitePlace K)) ∈ Filter.cofinite by simp] with w hw
    rw [Pi.single_eq_of_ne (by simpa using hw)]
    exact (w.adicCompletionIntegers K).zero_mem⟩
  map_zero' := IsDedekindDomain.FiniteAdeleRing.ext K fun w => by
    change Pi.single v (0 : FiniteCompletion K v) w = 0
    simp
  map_add' t s := IsDedekindDomain.FiniteAdeleRing.ext K fun w => by
    change Pi.single v (t + s) w = Pi.single v t w + Pi.single v s w
    rw [Pi.single_add]
    rfl

theorem finiteSingle_apply_same (v : Global.FinitePlace K) (t : FiniteCompletion K v) :
    finiteSingle K v t v = t :=
  Pi.single_eq_same v t

theorem finiteSingle_apply_ne {v w : Global.FinitePlace K} (h : w ≠ v) (t : FiniteCompletion K v) :
    finiteSingle K v t w = 0 :=
  Pi.single_eq_of_ne h t

theorem finiteSingle_mem {v : Global.FinitePlace K} {t : FiniteCompletion K v}
    (ht : t ∈ v.adicCompletionIntegers K) : finiteSingle K v t ∈ integralFiniteAdeles K := by
  rw [mem_integralFiniteAdeles]
  intro w
  by_cases h : w = v
  · subst h
    rwa [finiteSingle_apply_same]
  · rw [finiteSingle_apply_ne K h]
    exact (w.adicCompletionIntegers K).zero_mem

/-- Finite adeles as adeles with zero infinite component. -/
def finiteToAdeles : FiniteAdeles K →+ Adeles K :=
  AddMonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeles K)

@[simp] theorem finiteToAdeles_fst (a : FiniteAdeles K) : (finiteToAdeles K a).1 = 0 := rfl
@[simp] theorem finiteToAdeles_snd (a : FiniteAdeles K) : (finiteToAdeles K a).2 = a := rfl

/-- The local component `χ_v = ψ ∘ ι_v` of the standard character. -/
def localCharacter (v : Global.FinitePlace K) : AddChar (FiniteCompletion K v) Circle :=
  (adelicCharacter K).compAddMonoidHom ((finiteToAdeles K).comp (finiteSingle K v))

theorem localCharacter_apply (v : Global.FinitePlace K) (t : FiniteCompletion K v) :
    localCharacter K v t = adelicCharacter K (finiteToAdeles K (finiteSingle K v t)) := rfl

/-- The value of a character on a finite adele, through a rational shift. -/
theorem adelicCharacter_finiteToAdeles (a : FiniteAdeles K) (r : K)
    (hr : a - algebraMap K (FiniteAdeles K) r ∈ integralFiniteAdeles K) :
    adelicCharacter K (finiteToAdeles K a) = unitExp (-((Algebra.trace ℚ K r : ℚ) : ℝ)) := by
  rw [adelicCharacter_apply K (finiteToAdeles K a) r hr, finiteToAdeles_fst, zero_sub, map_neg,
    infiniteTrace_algebraMap]

theorem adelicCharacter_finiteToAdeles_of_mem {a : FiniteAdeles K}
    (ha : a ∈ integralFiniteAdeles K) : adelicCharacter K (finiteToAdeles K a) = 1 := by
  rw [adelicCharacter_finiteToAdeles K a 0 (by rwa [map_zero, sub_zero])]
  simp

/-- `χ_v` is trivial on the local integers. -/
theorem localCharacter_eq_one {v : Global.FinitePlace K} {t : FiniteCompletion K v}
    (ht : t ∈ v.adicCompletionIntegers K) : localCharacter K v t = 1 :=
  adelicCharacter_finiteToAdeles_of_mem K (finiteSingle_mem K ht)

theorem coe_eq_algebraMap (v : Global.FinitePlace K) (r : K) :
    ((r : FiniteCompletion K v)) = algebraMap K (FiniteCompletion K v) r := rfl

theorem algebraMap_integer_mem (b : RingOfIntegers K) :
    algebraMap K (FiniteAdeles K) (algebraMap (RingOfIntegers K) K b) ∈ integralFiniteAdeles K :=
  (mem_integralFiniteAdeles K _).mpr fun w =>
    IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers w b

/-- `χ_v` is nontrivial. If it were trivial, every `r ∈ K` integral away from `v` would have
integral traces against `𝒪_K`, hence bounded denominator; but such `r` can have arbitrarily
negative valuation at `v`. -/
theorem exists_localCharacter_ne_one (v : Global.FinitePlace K) :
    ∃ t : FiniteCompletion K v, localCharacter K v t ≠ 1 := by
  by_contra! h
  obtain ⟨N, hN0, hN⟩ := exists_dual_denominator K
  obtain ⟨π, hπv, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  let ι := algebraMap K (FiniteCompletion K v)
  let NK : K := algebraMap (RingOfIntegers K) K N
  let πK : K := algebraMap (RingOfIntegers K) K π
  have hNK : NK ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (RingOfIntegers K) K)).mpr hN0
  have hπK : πK ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (RingOfIntegers K) K)).mpr hπ0
  let t : FiniteCompletion K v := ι (1 / (NK * πK))
  obtain ⟨r, hr⟩ := exists_sub_mem_integralFiniteAdeles (finiteSingle K v t)
  have hint : ∀ b : RingOfIntegers K, ∃ m : ℤ,
      Algebra.trace ℚ K (r * algebraMap (RingOfIntegers K) K b) = m := by
    intro b
    let bK : K := algebraMap (RingOfIntegers K) K b
    have heq : finiteSingle K v (ι bK * t) - algebraMap K (FiniteAdeles K) (r * bK) =
        algebraMap K (FiniteAdeles K) bK *
          (finiteSingle K v t - algebraMap K (FiniteAdeles K) r) := by
      refine IsDedekindDomain.FiniteAdeleRing.ext K fun w => ?_
      change finiteSingle K v (ι bK * t) w - ((r * bK : K) : FiniteCompletion K w) =
        (bK : FiniteCompletion K w) * (finiteSingle K v t w - (r : FiniteCompletion K w))
      rw [coe_eq_algebraMap, coe_eq_algebraMap, coe_eq_algebraMap]
      by_cases hw : w = v
      · subst hw
        rw [finiteSingle_apply_same, finiteSingle_apply_same, map_mul]
        ring
      · rw [finiteSingle_apply_ne K hw, finiteSingle_apply_ne K hw, map_mul]
        ring
    have hb : finiteSingle K v (ι bK * t) - algebraMap K (FiniteAdeles K) (r * bK) ∈
        integralFiniteAdeles K := by
      rw [heq]
      exact mul_mem (algebraMap_integer_mem K b) hr
    have h1 := h (ι bK * t)
    rw [localCharacter_apply, adelicCharacter_finiteToAdeles K _ (r * bK) hb,
      unitExp_eq_one_iff] at h1
    obtain ⟨m, hm⟩ := h1
    refine ⟨-m, ?_⟩
    have : ((Algebra.trace ℚ K (r * bK) : ℚ) : ℝ) = ((-m : ℤ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  obtain ⟨z, hz⟩ := hN r hint
  have hv : t - ι r ∈ v.adicCompletionIntegers K := by
    have hrv := (mem_integralFiniteAdeles K _).mp hr v
    change finiteSingle K v t v - ((r : K) : FiniteCompletion K v) ∈ _ at hrv
    rwa [finiteSingle_apply_same, coe_eq_algebraMap] at hrv
  have hNv : ι NK ∈ v.adicCompletionIntegers K :=
    IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers v N
  have hzv : ι (algebraMap (RingOfIntegers K) K z) ∈ v.adicCompletionIntegers K :=
    IsDedekindDomain.HeightOneSpectrum.coe_mem_adicCompletionIntegers v z
  have hinv : ι πK⁻¹ ∈ v.adicCompletionIntegers K := by
    have e : ι πK⁻¹ = ι NK * (t - ι r) + ι (algebraMap (RingOfIntegers K) K z) := by
      rw [hz, mul_sub, map_mul, ← map_mul, ← map_mul, sub_add_cancel]
      congr 1
      rw [one_div, map_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ hNK, one_mul]
    rw [e]
    exact add_mem (mul_mem hNv hv) hzv
  have hval : Valued.v (ι πK) < 1 := by
    have : ι πK = algebraMap (RingOfIntegers K) (FiniteCompletion K v) π :=
      (IsScalarTower.algebraMap_apply (RingOfIntegers K) K (FiniteCompletion K v) π).symm
    rw [this, valued_algebraMap_integer]
    exact (IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem v π).mpr hπv
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀] at hinv
  have hpos : 0 < Valued.v (ι πK) := by
    rw [zero_lt_iff, Ne, map_eq_zero, map_eq_zero]
    exact hπK
  exact absurd ((inv_le_one₀ hpos).mp hinv) (not_le.mpr hval)

/-! ### The annihilator of `K` -/

/-- The real linear map `Y ↦ (Tr_∞(b_j Y))_j` on the mixed space. -/
def mixedTracePairing : mixedEmbedding.mixedSpace K →ₗ[ℝ]
    (Module.Free.ChooseBasisIndex ℤ (RingOfIntegers K) → ℝ) :=
  LinearMap.pi fun j => (mixedTrace K).comp
    (LinearMap.mulLeft ℝ (mixedEmbedding.latticeBasis K j))

theorem mixedTracePairing_mixedEmbedding (x : K)
    (j : Module.Free.ChooseBasisIndex ℤ (RingOfIntegers K)) :
    mixedTracePairing K (mixedEmbedding K x) j =
      ((Algebra.trace ℚ K (integralBasis K j * x) : ℚ) : ℝ) := by
  change mixedTrace K (mixedEmbedding.latticeBasis K j * mixedEmbedding K x) = _
  rw [mixedEmbedding.latticeBasis_apply, ← map_mul, mixedTrace_mixedEmbedding]

theorem mixedTracePairing_injective : Function.Injective (mixedTracePairing K) := by
  classical
  rw [LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    rw [Module.finrank_eq_card_basis (mixedEmbedding.latticeBasis K),
      Module.finrank_fintype_fun_eq_card])]
  intro y
  refine ⟨∑ k, y k • mixedEmbedding K (traceDualBasis K k), ?_⟩
  funext j
  rw [map_sum, Finset.sum_apply]
  simp_rw [map_smul, Pi.smul_apply, mixedTracePairing_mixedEmbedding, mul_comm (integralBasis K j),
    trace_traceDualBasis_mul]
  have hite : ∀ x, y x * (((if j = x then 1 else 0 : ℚ)) : ℝ) = if j = x then y x else 0 := by
    intro x
    split_ifs <;> simp
  simp only [smul_eq_mul, hite, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- An infinite adele with integral traces against `𝒪_K` is rational. -/
theorem exists_eq_algebraMap_of_infiniteTrace (W : InfiniteAdeleRing K)
    (hW : ∀ b : RingOfIntegers K, ∃ m : ℤ,
      infiniteTrace K (algebraMap K (InfiniteAdeleRing K)
        (algebraMap (RingOfIntegers K) K b) * W) = m) :
    ∃ δ : K, W = algebraMap K (InfiniteAdeleRing K) δ := by
  classical
  choose m hm using fun j => hW (RingOfIntegers.basis K j)
  refine ⟨∑ k, (m k : ℚ) • traceDualBasis K k, ?_⟩
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
  rw [← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  apply mixedTracePairing_injective K
  funext j
  rw [mixedTracePairing_mixedEmbedding, Finset.mul_sum, map_sum]
  simp_rw [mul_smul_comm, map_smul, mul_comm (integralBasis K j), trace_traceDualBasis_mul]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  rw [Rat.cast_intCast, ← hm j]
  change mixedTrace K (mixedEmbedding.latticeBasis K j *
    InfiniteAdeleRing.ringEquiv_mixedSpace K W) = _
  rw [mixedEmbedding.latticeBasis_apply, integralBasis_apply,
    InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, ← map_mul]
  rfl

/-- A finite adele orthogonal to `K` vanishes. -/
theorem finiteAdele_eq_zero_of_orthogonal (w : FiniteAdeles K)
    (hw : ∀ a : K,
      adelicCharacter K (finiteToAdeles K (algebraMap K (FiniteAdeles K) a * w)) = 1) :
    w = 0 := by
  by_contra hne
  obtain ⟨p, hp⟩ : ∃ p, w p ≠ 0 := by
    by_contra! h
    exact hne (IsDedekindDomain.FiniteAdeleRing.ext K h)
  obtain ⟨d, hd0, hd⟩ := exists_integer_mul_mem_adicCompletionIntegers w
  obtain ⟨t0, ht0⟩ := exists_localCharacter_ne_one K p
  apply ht0
  let dK : K := algebraMap (RingOfIntegers K) K d
  have hdK : dK ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (RingOfIntegers K) K)).mpr hd0
  let c : FiniteCompletion K p := algebraMap K (FiniteCompletion K p) dK * w p
  have hc : c ≠ 0 := mul_ne_zero ((map_ne_zero _).mpr hdK) hp
  have hcp : c ∈ p.adicCompletionIntegers K := by
    have := hd p
    rwa [IsScalarTower.algebraMap_apply (RingOfIntegers K) K (FiniteCompletion K p)] at this
  obtain ⟨s, hs⟩ := exists_sub_mem_integralFiniteAdeles (finiteSingle K p (t0 / c))
  have key : algebraMap K (FiniteAdeles K) (dK * s) * w - finiteSingle K p t0 ∈
      integralFiniteAdeles K := by
    rw [mem_integralFiniteAdeles]
    intro q
    have hsq := (mem_integralFiniteAdeles K _).mp hs q
    change finiteSingle K p (t0 / c) q - ((s : K) : FiniteCompletion K q) ∈ _ at hsq
    change ((dK * s : K) : FiniteCompletion K q) * w q - finiteSingle K p t0 q ∈ _
    rw [coe_eq_algebraMap] at hsq ⊢
    by_cases hq : q = p
    · subst hq
      rw [finiteSingle_apply_same] at hsq ⊢
      have hdKq : algebraMap K (FiniteCompletion K q) dK ≠ 0 := (map_ne_zero _).mpr hdK
      have e : algebraMap K (FiniteCompletion K q) (dK * s) * w q - t0 =
          -((t0 / c - algebraMap K (FiniteCompletion K q) s) * c) := by
        rw [sub_mul, div_mul_cancel₀ _ hc, map_mul]
        ring
      rw [e]
      exact neg_mem (mul_mem hsq hcp)
    · rw [finiteSingle_apply_ne K hq] at hsq ⊢
      have hdq : algebraMap K (FiniteCompletion K q) dK * w q ∈ q.adicCompletionIntegers K := by
        have := hd q
        rwa [IsScalarTower.algebraMap_apply (RingOfIntegers K) K (FiniteCompletion K q)] at this
      have e : algebraMap K (FiniteCompletion K q) (dK * s) * w q - 0 =
          -(0 - algebraMap K (FiniteCompletion K q) s) *
            (algebraMap K (FiniteCompletion K q) dK * w q) := by
        rw [map_mul]
        ring
      rw [e]
      exact mul_mem (neg_mem hsq) hdq
  have h := hw (dK * s)
  rw [show algebraMap K (FiniteAdeles K) (dK * s) * w = finiteSingle K p t0 +
      (algebraMap K (FiniteAdeles K) (dK * s) * w - finiteSingle K p t0) by abel,
    map_add, AddChar.map_add_eq_mul, adelicCharacter_finiteToAdeles_of_mem K key, mul_one] at h
  exact h

/-- **Self-duality of `K`**: if `ψ(a y) = 1` for every `a ∈ K`, then `y ∈ K`. -/
theorem exists_eq_algebraMap_of_orthogonal (y : Adeles K)
    (hy : ∀ a : K, adelicCharacter K (algebraMap K (Adeles K) a * y) = 1) :
    ∃ δ : K, y = algebraMap K (Adeles K) δ := by
  set r := finiteShift K y.2
  set y' := y - algebraMap K (Adeles K) r with hy'_def
  have hy' : ∀ a : K, adelicCharacter K (algebraMap K (Adeles K) a * y') = 1 := by
    intro a
    rw [hy'_def, mul_sub, ← map_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, hy a, one_mul,
      AddChar.map_neg_eq_inv, adelicCharacter_algebraMap, inv_one]
  have hy'2 : y'.2 ∈ integralFiniteAdeles K := sub_finiteShift_mem K y.2
  obtain ⟨δ, hδ⟩ := exists_eq_algebraMap_of_infiniteTrace K y'.1 fun b => by
    have h := hy' (algebraMap (RingOfIntegers K) K b)
    rw [adelicCharacter_of_integral K _ (by
      rw [adeles_mul_snd, adeles_algebraMap_snd]
      exact mul_mem (algebraMap_integer_mem K b) hy'2), unitExp_eq_one_iff] at h
    exact h
  set w := y'.2 - algebraMap K (FiniteAdeles K) δ with hw_def
  have hw : ∀ a : K,
      adelicCharacter K (finiteToAdeles K (algebraMap K (FiniteAdeles K) a * w)) = 1 := by
    intro a
    have e : finiteToAdeles K (algebraMap K (FiniteAdeles K) a * w) =
        algebraMap K (Adeles K) a * y' + -algebraMap K (Adeles K) (a * δ) := by
      refine adeles_ext ?_ ?_
      · rw [finiteToAdeles_fst, adeles_add_fst, adeles_neg_fst, adeles_mul_fst,
          adeles_algebraMap_fst, adeles_algebraMap_fst, hδ, map_mul, add_neg_cancel]
      · rw [finiteToAdeles_snd, adeles_add_snd, adeles_neg_snd, adeles_mul_snd,
          adeles_algebraMap_snd, adeles_algebraMap_snd, hw_def, map_mul]
        ring
    rw [e, AddChar.map_add_eq_mul, hy' a, AddChar.map_neg_eq_inv, adelicCharacter_algebraMap,
      inv_one, mul_one]
  have hw0 := finiteAdele_eq_zero_of_orthogonal K w hw
  refine ⟨r + δ, ?_⟩
  have hyy : y = y' + algebraMap K (Adeles K) r := by rw [hy'_def]; abel
  refine adeles_ext ?_ ?_
  · rw [hyy, adeles_add_fst, adeles_algebraMap_fst, adeles_algebraMap_fst, hδ, map_add, add_comm]
  · rw [hyy, adeles_add_snd, adeles_algebraMap_snd, adeles_algebraMap_snd, map_add]
    rw [hw_def, sub_eq_zero] at hw0
    rw [hw0]
    abel

end Langlands.Automorphic.CuspidalWhittaker
