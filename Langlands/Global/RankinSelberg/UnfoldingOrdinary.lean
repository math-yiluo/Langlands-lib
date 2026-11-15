import Langlands.Global.RankinSelberg.UnfoldingSteps

/-! # The ordinary unfolding of unequal-rank global integrals, from a Whittaker expansion -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj ENNReal Pointwise
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global

local instance unfoldingOrdinarySchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unfoldingOrdinarySchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

section Kernels

variable (F : Type u) [Field F] [NumberField F]

/-- `W(diag(g, I)) Φ(g) |det g|^(s-(r-t)/2)`: with `Φ` a cusp form this is the integrand
over `N_m(F) \ GL_m(𝔸)`, with `Φ` a Whittaker function the Whittaker integrand. -/
def ordinaryKernel {r t : ℕ} (h : t < r) (W : Points F (r + 1) → ℂ)
    (Φ : Points F (t + 1) → ℂ) (s : ℂ) (x : Points F (t + 1)) : ℂ :=
  W (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) x) * Φ x *
    detPower F (t + 1) x (s - ((r - t : ℕ) : ℂ) / 2)

theorem unequalWhittakerIntegrand_eq {r t : ℕ} (h : t < r) (W : Points F (r + 1) → ℂ)
    (W' : Points F (t + 1) → ℂ) (s : ℂ) (q : WhittakerQuotient F (t + 1)) :
    unequalWhittakerIntegrand F h W W' s q = ordinaryKernel F h W W' s q.out := rfl

/-- The integrand of the defining unequal-rank integral, at a point of `GL_m(𝔸)`. -/
def projectionKernel {r t : ℕ} (h : t < r) (ψ : AddChar (Adeles F) ℂ)
    (φ : Points F (r + 1) → ℂ) (φ' : Points F (t + 1) → ℂ) (s : ℂ) (x : Points F (t + 1)) : ℂ :=
  projection F (Nat.succ_lt_succ h) ψ φ (pad F (Nat.le_succ (t + 1)) x) * φ' x *
    detPower F (t + 1) x (s - 1 / 2)

theorem unequalIntegrand_eq {r t : ℕ} (h : t < r) (ψ : AddChar (Adeles F) ℂ)
    (φ : Points F (r + 1) → ℂ) (φ' : Points F (t + 1) → ℂ) (s : ℂ)
    (q : AdelicGroupPoints.RationalQuotient F (Scheme F (t + 1))) :
    unequalIntegrand F h ψ φ φ' s q = projectionKernel F h ψ φ φ' s q.out := rfl

theorem measurable_ordinaryKernel {r t : ℕ} (h : t < r) {W : Points F (r + 1) → ℂ}
    {Φ : Points F (t + 1) → ℂ} (hW : Measurable W) (hΦ : Measurable Φ) (s : ℂ) :
    Measurable (ordinaryKernel F h W Φ s) :=
  ((hW.comp (continuous_pad F _).measurable).mul hΦ).mul
    (continuous_detPower F (t + 1) _).measurable

/-- The exponents of the expansion and of the defining integral combine. -/
theorem detPower_unfolding_exponent {r t : ℕ} (h : t < r) (x : Points F (t + 1)) (s : ℂ) :
    detPower F (t + 1) x (-((r - (t + 1) : ℕ) : ℂ) / 2) * detPower F (t + 1) x (s - 1 / 2) =
      detPower F (t + 1) x (s - ((r - t : ℕ) : ℂ) / 2) := by
  rw [← detPower_add]
  congr 1
  rw [Nat.cast_sub (by omega : t + 1 ≤ r), Nat.cast_sub (by omega : t ≤ r)]
  push_cast
  ring

end Kernels

section Cusp

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- Left translation of the kernel by `N_m(𝔸)`. -/
theorem ordinaryKernel_unipotent_mul {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (Φ : Points F (t + 1) → ℂ) (s : ℂ)
    (n : unipotentAdelic F (t + 1)) (x : Points F (t + 1)) :
    ordinaryKernel F h (cuspWhittaker F T ψ v) Φ s ((n : Points F (t + 1)) * x) =
      genericCharacter F t ψ (fun _ => 1) n *
        (cuspWhittaker F T ψ v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) x) *
          Φ ((n : Points F (t + 1)) * x) * detPower F (t + 1) x (s - ((r - t : ℕ) : ℂ) / 2)) := by
  unfold ordinaryKernel
  rw [pad_mul, detPower_unipotent_mul]
  have hp : pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) (n : Points F (t + 1)) =
      (padUnipotent F (Nat.le_of_lt (Nat.succ_lt_succ h)) n : Points F (r + 1)) := rfl
  rw [hp, cuspWhittaker_mul_left F T ψ hψ v, genericCharacter_padUnipotent]
  ring

/-- The kernel with a cusp form is left invariant under `N_m(F)`. -/
theorem ordinaryKernel_rational_mul {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (v' : T'.Space) (s : ℂ)
    {k : Points F (t + 1)} (hk : k ∈ unipotentRationalImage F (t + 1)) (x : Points F (t + 1)) :
    ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspFunction F T' v') s (k * x) =
      ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspFunction F T' v') s x := by
  have hkΓ := unipotentRationalImage_le F (t + 1) hk
  obtain ⟨l, rfl⟩ := (mem_unipotentRationalImage_iff F (t + 1) k).mp hk
  rw [ordinaryKernel_unipotent_mul F h T ψ hψ v, genericCharacter_rational F t ψ hψ.2.2.1,
    one_mul, cuspFunction_rational_mul F T' v' hkΓ]
  rfl

/-- The Whittaker kernel is left invariant under `N_m(𝔸)`. -/
theorem ordinaryKernel_whittaker_unipotent_mul {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (v' : T'.Space) (s : ℂ)
    (n : unipotentAdelic F (t + 1)) (x : Points F (t + 1)) :
    ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspWhittaker F T' ψ⁻¹ v') s
        ((n : Points F (t + 1)) * x) =
      ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspWhittaker F T' ψ⁻¹ v') s x := by
  rw [ordinaryKernel_unipotent_mul F h T ψ hψ v,
    cuspWhittaker_mul_left F T' ψ⁻¹ (isStandardAdditiveCharacter_inv F ψ hψ) v',
    genericCharacter_inv F t ψ hψ.2.2.2]
  have hn : genericCharacter F t ψ (fun _ => 1) n *
      starRingEnd ℂ (genericCharacter F t ψ (fun _ => 1) n) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_genericCharacter F t ψ hψ.2.2.2]
    simp
  unfold ordinaryKernel
  linear_combination (cuspWhittaker F T ψ v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) x) *
    cuspWhittaker F T' ψ⁻¹ v' x * detPower F (t + 1) x (s - ((r - t : ℕ) : ℂ) / 2)) * hn

/-- The Whittaker expansion of the projection, Cogdell 2004, p.205: for `h ∈ GL_m(𝔸)`,
`P^n_m φ (diag(h,1)) = |det h|^{-(n-m-1)/2} Σ_{γ ∈ N_m(F) \ GL_m(F)} W_φ(diag(γ h, I_{n-m}))`,
with `n = r + 1` and `m = t + 1`. -/
def ProjectionWhittakerExpansion {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r) : Prop :=
  ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    ∀ (v : T.Space) (g : Points F (t + 1)),
      HasSum (fun q : RationalCosetIndex F (t + 1) =>
          detPower F (t + 1) g (-((r - (t + 1) : ℕ) : ℂ) / 2) *
            cuspWhittaker F T ψ v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h))
              (rationalCosetRep F (t + 1) q * g)))
        (projection F (Nat.succ_lt_succ h) ψ (cuspFunction F T v)
          (pad F (Nat.le_succ (t + 1)) g))

/-- The defining integrand is the orbit sum of the kernel. -/
theorem hasSum_projectionKernel {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t)
    (hE : ProjectionWhittakerExpansion F h T) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (v' : T'.Space) (s : ℂ)
    (x : Points F (t + 1)) :
    HasSum (fun q => ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspFunction F T' v') s
        (rationalCosetRep F (t + 1) q * x))
      (projectionKernel F h ψ (cuspFunction F T v) (cuspFunction F T' v') s x) := by
  have h1 := (hE ψ hψ v x).mul_right (cuspFunction F T' v' x * detPower F (t + 1) x (s - 1 / 2))
  convert h1 using 1
  · funext q
    have hq : rationalCosetRep F (t + 1) q ∈
        AdelicGroupPoints.rationalSubgroup F (Scheme F (t + 1)) :=
      cosetRep_mem _ _ q
    unfold ordinaryKernel
    rw [cuspFunction_rational_mul F T' v' hq, detPower_rational_mul F (t + 1) hq,
      ← detPower_unfolding_exponent F h x s]
    ring
  · unfold projectionKernel
    ring

end Cusp

section OrdinaryUnfolding

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance ordinaryUnipotentAdelicLocallyCompactSpace (n : ℕ) :
    LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

/-- Averaging the kernel of the cusp form `φ'` over `N_m(F) \ N_m(𝔸)` gives the mass times
the kernel of its `ψ⁻¹`-Whittaker function. -/
theorem setIntegral_unipotent_ordinaryKernel {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (v' : T'.Space) (s : ℂ)
    (x : Points F (t + 1)) :
    ∫ n in unipotentFundamentalDomain F (t + 1),
        ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspFunction F T' v') s
          ((n : Points F (t + 1)) * x) ∂Measure.haar =
      ((Measure.haar : Measure (unipotentAdelic F (t + 1)))
          (unipotentFundamentalDomain F (t + 1))).toReal •
        ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspWhittaker F T' ψ⁻¹ v') s x := by
  have hψ' := isStandardAdditiveCharacter_inv F ψ hψ
  have hφ'm : Measurable (cuspFunction F T' v') := (continuous_cuspFunction F T' v').measurable
  set a : ℝ := ((Measure.haar : Measure (unipotentAdelic F (t + 1)))
    (unipotentFundamentalDomain F (t + 1))).toReal with ha
  set c : ℝ := (AdelicSubgroupPoints.quotientMassNormalizer F (Scheme F (t + 1))
    (upperUnipotent F (t + 1))).toReal with hc
  have hac : (c : ℂ) * (a : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ha, hc, quotientMassNormalizer_mul_haar, Complex.ofReal_one]
  have hconj : ∀ n : unipotentAdelic F (t + 1),
      starRingEnd ℂ (genericCharacter F t ψ⁻¹ (fun _ => 1) n) =
        genericCharacter F t ψ (fun _ => 1) n := fun n => by
    rw [genericCharacter_inv F t ψ hψ.2.2.2, Complex.conj_conj]
  have hW' := subgroupCharacterCoefficient_eq_setIntegral F (Scheme F (t + 1))
    (upperUnipotent F (t + 1)) (genericCharacter F t ψ⁻¹ fun _ => 1)
    (continuous_genericCharacter F t ψ⁻¹ hψ'.1 _).measurable
    (genericCharacter_rational_mul F t ψ⁻¹ hψ') (cuspFunction F T' v') hφ'm
    (fun k y => cuspFunction_rational_mul F T' v' (mem_rationalSubgroup_of_unipotent F k) y) x
  simp_rw [hconj] at hW'
  have hW'eq : cuspWhittaker F T' ψ⁻¹ v' x = (c : ℂ) *
      ∫ n in unipotentFundamentalDomain F (t + 1),
        cuspFunction F T' v' ((n : Points F (t + 1)) * x) *
          genericCharacter F t ψ (fun _ => 1) n ∂Measure.haar := by
    rw [← Complex.real_smul]
    exact hW'
  simp_rw [ordinaryKernel_unipotent_mul F h T ψ hψ v (cuspFunction F T' v') s]
  have e1 : (fun n : unipotentAdelic F (t + 1) => genericCharacter F t ψ (fun _ => 1) n *
      (cuspWhittaker F T ψ v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) x) *
        cuspFunction F T' v' ((n : Points F (t + 1)) * x) *
          detPower F (t + 1) x (s - ((r - t : ℕ) : ℂ) / 2))) =
      fun n : unipotentAdelic F (t + 1) =>
        (cuspWhittaker F T ψ v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) x) *
          detPower F (t + 1) x (s - ((r - t : ℕ) : ℂ) / 2)) *
        (cuspFunction F T' v' ((n : Points F (t + 1)) * x) *
          genericCharacter F t ψ (fun _ => 1) n) := by
    funext n
    ring
  rw [e1, integral_const_mul]
  unfold ordinaryKernel
  rw [hW'eq, Complex.real_smul]
  linear_combination (-(cuspWhittaker F T ψ v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) x) *
      detPower F (t + 1) x (s - ((r - t : ℕ) : ℂ) / 2) *
      ∫ n in unipotentFundamentalDomain F (t + 1),
        cuspFunction F T' v' ((n : Points F (t + 1)) * x) *
          genericCharacter F t ψ (fun _ => 1) n ∂Measure.haar)) * hac

/-- Ordinary unfolding (Cogdell 2004, pp.205–206), from the Whittaker expansion of the
projection and absolute integrability of the kernel over `N_m(F) \ GL_m(𝔸)`. -/
theorem ordinary_unfolding {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t)
    (hE : ProjectionWhittakerExpansion F h T) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (v : T.Space) (v' : T'.Space) (s : ℂ)
    (hint : Integrable (fun q : LeftCosetSpace (unipotentRationalImage F (t + 1)) =>
        ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspFunction F T' v') s q.out)
      (LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (t + 1))
        (isDiscrete_unipotentRationalImage F (t + 1)))) :
    Integrable (unequalWhittakerIntegrand F h (cuspWhittaker F T ψ v)
        (cuspWhittaker F T' ψ⁻¹ v') s) (whittakerQuotientMeasure F (t + 1)) ∧
      unequalIntegral F h ψ (cuspFunction F T v) (cuspFunction F T' v') s =
        unequalWhittakerIntegral F h (cuspWhittaker F T ψ v) (cuspWhittaker F T' ψ⁻¹ v') s := by
  have hψ' := isStandardAdditiveCharacter_inv F ψ hψ
  have hf₀m : Measurable (ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspFunction F T' v') s) :=
    measurable_ordinaryKernel F h (measurable_cuspWhittaker F T ψ hψ v)
      (continuous_cuspFunction F T' v').measurable s
  have hf₂m : Measurable
      (ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspWhittaker F T' ψ⁻¹ v') s) :=
    measurable_ordinaryKernel F h (measurable_cuspWhittaker F T ψ hψ v)
      (measurable_cuspWhittaker F T' ψ⁻¹ hψ' v') s
  have hf₀Λ : ∀ k ∈ unipotentRationalImage F (t + 1), ∀ x : Points F (t + 1),
      ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspFunction F T' v') s (k * x) =
      ordinaryKernel F h (cuspWhittaker F T ψ v) (cuspFunction F T' v') s x :=
    fun k hk x => ordinaryKernel_rational_mul F h T T' ψ hψ v v' s hk x
  have hf₀sΛ := (integrable_out_iff _ hf₀m (fun k x => hf₀Λ k k.property x) _ _).mp hint
  obtain ⟨hf₂sΛ, havg⟩ := setIntegral_eq_of_average F hf₀m hf₀Λ hf₀sΛ
    (setIntegral_unipotent_ordinaryKernel F h T T' ψ hψ v v' s)
  obtain ⟨hint', hR⟩ := integrable_and_integral_whittakerQuotient F hf₂m
    (ordinaryKernel_whittaker_unipotent_mul F h T T' ψ hψ v v' s) hf₂sΛ
  refine ⟨hint', ?_⟩
  calc unequalIntegral F h ψ (cuspFunction F T v) (cuspFunction F T' v') s =
        ∫ q, projectionKernel F h ψ (cuspFunction F T v) (cuspFunction F T' v') s q.out
          ∂AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (t + 1)) := rfl
    _ = _ := integral_rationalQuotient_eq_of_hasSum F hf₀m hf₀Λ
          (hasSum_projectionKernel F h T T' hE ψ hψ v v' s) hf₀sΛ
    _ = _ := havg
    _ = _ := hR.symm

end OrdinaryUnfolding

end Langlands.Global.RankinSelbergGlobal.Unfolding
