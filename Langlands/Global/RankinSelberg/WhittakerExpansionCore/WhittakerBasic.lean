import Langlands.Global.RankinSelberg.WhittakerExpansionCore.Interface

/-! # Basic properties of Whittaker functions of left invariant functions -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints PrimitiveAdelicHeight

local instance basicSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance basicSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

section Equivariance

variable {r : ℕ} (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
  (f : Points F (r + 1) → ℂ)
  (hfΓ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x, f (k * x) = f x)

include hψ hfΓ

/-- Equivariance of `W_f` under `N_(r+1)(𝔸)`. -/
theorem whittaker_mul_left (u : unipotentAdelic F (r + 1)) (g : Points F (r + 1)) :
    whittaker F r ψ f ((u : Points F (r + 1)) * g) =
      genericCharacter F r ψ (fun _ => 1) u * whittaker F r ψ f g := by
  have := compactSpace_unipotentRationalQuotient F (r + 1)
  exact subgroupCharacterCoefficient_mul_left F (Scheme F (r + 1)) (upperUnipotent F (r + 1))
    (genericCharacter F r ψ fun _ => 1) (genericCharacter_mul F r ψ _)
    (genericCharacter_rational F r ψ hψ.2.2.1 _) (norm_genericCharacter F r ψ hψ.2.2.2 _)
    f (fun k x => hfΓ _ (mem_rationalSubgroup_of_unipotent F k) x) u g

/-- Left translation of `W_f` by a column point. -/
theorem whittaker_colPoint_mul {j : ℕ} (hj : j < r) (c : Fin (r + 1) → Adeles F)
    (g : Points F (r + 1)) :
    whittaker F r ψ f (colPoint F (j := j) c * g) =
      ψ (c (Fin.castSucc ⟨j, hj⟩)) * whittaker F r ψ f g := by
  have h := whittaker_mul_left F ψ hψ f hfΓ ⟨_, colPoint_mem_unipotentAdelic F (j := j) c⟩ g
  rw [h]
  congr 1
  simp only [genericCharacter, map_one, one_mul]
  congr 1
  change ∑ i : Fin r, pointMatrix F (colPoint F (j := j) c) i.castSucc i.succ = _
  rw [pointMatrix_colPoint, sum_superdiag_one_add_colMatrix F hj]

/-- `W_f` is left invariant under padded rational unipotent elements. -/
theorem whittaker_padRational_unipotent_mul {k : ℕ} (hk : k ≤ r + 1) {n : RationalGL F k}
    (hn : n ∈ rationalUpperUnipotent F k) (z : Points F (r + 1)) :
    whittaker F r ψ f (padRational F hk n * z) = whittaker F r ψ f z := by
  have hu : IsUnitriangular (pointMatrix F (padRational F hk n)) := by
    rw [pointMatrix_padRational, padGL_rational]
    exact (isUnitriangular_padGL hk _ ((mem_rationalUpperUnipotent_iff F n).mp hn)).map _
  have hmem : padRational F hk n ∈ unipotentAdelic F (r + 1) := by
    rw [mem_unipotentAdelic_iff]
    exact hu
  rw [whittaker_mul_left F ψ hψ f hfΓ ⟨_, hmem⟩ z]
  convert one_mul _
  simp only [genericCharacter, map_one, one_mul]
  change ψ (∑ i : Fin r, pointMatrix F (padRational F hk n) i.castSucc i.succ) = 1
  rw [pointMatrix_padRational, padGL_rational]
  simp only [AdelicGL.rational_apply]
  rw [← map_sum]
  exact hψ.2.2.1 _

/-- `W_f(diag(g, I) x)` depends only on the coset `N_k(F) g`. -/
theorem whittaker_padRational_of_rightRel {k : ℕ} (hk : k ≤ r + 1) {a b : RationalGL F k}
    (hab : QuotientGroup.rightRel (rationalUpperUnipotent F k) a b) (z : Points F (r + 1)) :
    whittaker F r ψ f (padRational F hk b * z) = whittaker F r ψ f (padRational F hk a * z) := by
  have h := QuotientGroup.rightRel_apply.mp hab
  have hb : b = (b * a⁻¹) * a := by group
  rw [hb, padRational_mul, mul_assoc, whittaker_padRational_unipotent_mul F ψ hψ f hfΓ hk h]

/-- Left translation of `W_f(diag(γ, I) ·)` by a column point: the character value is
`ψ(Σ_a (g0)_(j,a) c_a)`. -/
theorem whittaker_padRational_colPoint {j : ℕ} (hj : j < r) (g0 : RationalGL F (j + 1))
    (c : Fin (r + 1) → Adeles F) (hc : IsColSupported j c) (y : Points F (r + 1)) :
    whittaker F r ψ f (padRational F (by omega : j + 1 ≤ r + 1) g0 * (colPoint F (j := j) c * y)) =
      ψ (∑ a : Fin (r + 1), (if h : (a : ℕ) < j + 1 then
        algebraMap F (Adeles F) ((g0 : Matrix (Fin (j + 1)) (Fin (j + 1)) F) (Fin.last j)
          ⟨a, h⟩) else 0) * c a) *
        whittaker F r ψ f (padRational F (by omega : j + 1 ≤ r + 1) g0 * y) := by
  rw [← mul_assoc, padRational_mul_column F hj g0 (colPoint_mem_column F c),
    colVec_eq_of_pointMatrix_eq F hj hc (pointMatrix_colPoint F c), mul_assoc,
    whittaker_colPoint_mul F ψ hψ f hfΓ hj, mulVec_padRational_row]

end Equivariance

local instance basicUnipotentLocallyCompact (n : ℕ) :
    LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

section Integral

variable {r : ℕ} (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)

include hψ

/-- A bound on the left `N(𝔸)`-translates of `g` bounds `W_f(g)`. -/
theorem norm_whittaker_le (f : Points F (r + 1) → ℂ) (g : Points F (r + 1)) (B : ℝ)
    (hB : ∀ u : unipotentAdelic F (r + 1), ‖f ((u : Points F (r + 1)) * g)‖ ≤ B) :
    ‖whittaker F r ψ f g‖ ≤ B := by
  have := compactSpace_unipotentRationalQuotient F (r + 1)
  have := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F (Scheme F (r + 1))
    (upperUnipotent F (r + 1))
  unfold whittaker generalLinearWhittakerFunction subgroupCharacterCoefficient
  refine (MeasureTheory.norm_integral_le_of_norm_le_const (C := B) (ae_of_all _ fun x => ?_)).trans ?_
  · rw [norm_mul, Complex.norm_conj, norm_genericCharacter F r ψ hψ.2.2.2, mul_one]
    exact hB _
  · rw [probReal_univ, mul_one]

/-- **Band bound.** A bound for `f` on a determinant band bounds `W_f` on the same band. -/
theorem norm_whittaker_le_of_band (f : Points F (r + 1) → ℂ) {lo hi B : ℝ}
    (hB : ∀ x : Points F (r + 1), lo ≤ detNorm F (r + 1) x → detNorm F (r + 1) x ≤ hi →
      ‖f x‖ ≤ B)
    (g : Points F (r + 1)) (hlo : lo ≤ detNorm F (r + 1) g) (hhi : detNorm F (r + 1) g ≤ hi) :
    ‖whittaker F r ψ f g‖ ≤ B := by
  refine norm_whittaker_le F ψ hψ f g B fun u => hB _ ?_ ?_
  · rw [detNorm_mul, detNorm_unipotent, one_mul]
    exact hlo
  · rw [detNorm_mul, detNorm_unipotent, one_mul]
    exact hhi

omit hψ in
/-- Right translation commutes with taking Whittaker functions. -/
theorem whittaker_mul_right (f : Points F (r + 1) → ℂ) (g h : Points F (r + 1)) :
    whittaker F r ψ f (g * h) = whittaker F r ψ (fun x => f (x * h)) g := by
  simp only [whittaker, generalLinearWhittakerFunction, subgroupCharacterCoefficient, mul_assoc]

omit hψ in
/-- `W_f` is right invariant under every right invariance of `f`. -/
theorem whittaker_mul_right_of_invariant (f : Points F (r + 1) → ℂ) (h : Points F (r + 1))
    (hf : ∀ x, f (x * h) = f x) (g : Points F (r + 1)) :
    whittaker F r ψ f (g * h) = whittaker F r ψ f g := by
  rw [whittaker_mul_right]
  simp only [hf]

/-- `W_f` as a set integral over the Borel fundamental domain of `N(F)` in `N(𝔸)`. -/
theorem whittaker_eq_setIntegral (f : Points F (r + 1) → ℂ) (hf : Continuous f)
    (hfΓ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x, f (k * x) = f x)
    (g : Points F (r + 1)) :
    whittaker F r ψ f g =
      (quotientMassNormalizer F (Scheme F (r + 1)) (upperUnipotent F (r + 1))).toReal •
        ∫ n in LeftCosetSpace.fundamentalDomain
            (rationalSubgroup F (Scheme F (r + 1)) (upperUnipotent F (r + 1)))
            (isDiscrete_rationalSubgroup F _ _),
          f ((n : Points F (r + 1)) * g) * starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) n)
          ∂Measure.haar :=
  subgroupCharacterCoefficient_eq_setIntegral F (Scheme F (r + 1)) (upperUnipotent F (r + 1))
    (genericCharacter F r ψ fun _ => 1) (continuous_genericCharacter F r ψ hψ.1 _).measurable
    (genericCharacter_rational_mul F r ψ hψ) f hf.measurable
    (fun k x => hfΓ _ (mem_rationalSubgroup_of_unipotent F k) x) g

omit hψ in
/-- The fundamental domain of `N(F)` in `N(𝔸)` has finite Haar measure. -/
theorem haar_unipotentFundamentalDomain_lt_top :
    (Measure.haar : Measure (unipotentAdelic F (r + 1)))
      (LeftCosetSpace.fundamentalDomain
        (rationalSubgroup F (Scheme F (r + 1)) (upperUnipotent F (r + 1)))
        (isDiscrete_rationalSubgroup F _ _)) < ⊤ := by
  have := compactSpace_unipotentRationalQuotient F (r + 1)
  have : IsFiniteMeasure (LeftCosetSpace.haarQuotientMeasure
      (rationalSubgroup F (Scheme F (r + 1)) (upperUnipotent F (r + 1)))
      (isDiscrete_rationalSubgroup F _ _)) :=
    rationalQuotientHaarMeasure_isFiniteMeasure F _ _
  exact (LeftCosetSpace.haar_fundamentalDomain_ne_top _ _).lt_top

/-- The integrand of the set-integral form is integrable when `f` is bounded on `N(𝔸) g`. -/
theorem integrableOn_whittakerIntegrand (f : Points F (r + 1) → ℂ) (hf : Continuous f)
    (g : Points F (r + 1)) (B : ℝ)
    (hB : ∀ u : unipotentAdelic F (r + 1), ‖f ((u : Points F (r + 1)) * g)‖ ≤ B) :
    IntegrableOn (fun n : unipotentAdelic F (r + 1) =>
        f ((n : Points F (r + 1)) * g) * starRingEnd ℂ (genericCharacter F r ψ (fun _ => 1) n))
      (LeftCosetSpace.fundamentalDomain
        (rationalSubgroup F (Scheme F (r + 1)) (upperUnipotent F (r + 1)))
        (isDiscrete_rationalSubgroup F _ _)) Measure.haar := by
  refine IntegrableOn.of_bound (haar_unipotentFundamentalDomain_lt_top F (r := r)) ?_ B
    (ae_of_all _ fun n => ?_)
  · exact ((hf.comp (continuous_subtype_val.mul continuous_const)).mul
      (Complex.continuous_conj.comp (continuous_genericCharacter F r ψ hψ.1 _))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_conj, norm_genericCharacter F r ψ hψ.2.2.2, mul_one]
    exact hB n

/-- Additivity of `f ↦ W_f(g)` for continuous invariant `f`, `f'` bounded on `N(𝔸) g`. -/
theorem whittaker_add (f f' : Points F (r + 1) → ℂ) (hf : Continuous f) (hf' : Continuous f')
    (hfΓ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x, f (k * x) = f x)
    (hf'Γ : ∀ k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1)), ∀ x,
      f' (k * x) = f' x)
    (g : Points F (r + 1)) (B B' : ℝ)
    (hB : ∀ u : unipotentAdelic F (r + 1), ‖f ((u : Points F (r + 1)) * g)‖ ≤ B)
    (hB' : ∀ u : unipotentAdelic F (r + 1), ‖f' ((u : Points F (r + 1)) * g)‖ ≤ B') :
    whittaker F r ψ (f + f') g = whittaker F r ψ f g + whittaker F r ψ f' g := by
  rw [whittaker_eq_setIntegral F ψ hψ f hf hfΓ, whittaker_eq_setIntegral F ψ hψ f' hf' hf'Γ,
    whittaker_eq_setIntegral F ψ hψ (f + f') (hf.add hf') (fun k hk x => by
      simp only [Pi.add_apply, hfΓ k hk, hf'Γ k hk]), ← smul_add,
    ← integral_add (integrableOn_whittakerIntegrand F ψ hψ f hf g B hB)
      (integrableOn_whittakerIntegrand F ψ hψ f' hf' g B' hB')]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun n => ?_)
  simp only [Pi.add_apply]
  ring

omit hψ in
/-- Homogeneity of `f ↦ W_f(g)`. -/
theorem whittaker_smul (c : ℂ) (f : Points F (r + 1) → ℂ) (g : Points F (r + 1)) :
    whittaker F r ψ (c • f) g = c * whittaker F r ψ f g := by
  simp only [whittaker, generalLinearWhittakerFunction, subgroupCharacterCoefficient,
    Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

end Integral

end Langlands.Global.RankinSelbergGlobal.Unfolding
