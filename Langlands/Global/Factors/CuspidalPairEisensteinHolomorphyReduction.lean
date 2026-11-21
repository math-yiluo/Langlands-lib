import Langlands.Global.Factors.CuspidalPairEisensteinHolomorphyStatement
import Langlands.Global.Factors.CuspidalPairEisensteinJointContinuationStatement
import Langlands.Global.RankinSelberg.UnfoldingGL
import Langlands.Global.RankinSelberg.UnfoldingCoefficient
import Langlands.Global.ImaginaryAxisAveraging
import Langlands.Representation.Archimedean.PrincipalSeriesMatrixCoefficientAnalytic

/-! # The generic coefficient of the cuspidal-pair Eisenstein series from its joint continuation

Integration over the compact quotient `N₀(F) \ N₀(𝔸)` carries the joint continuation of the
Eisenstein series (`CuspidalPairEisensteinJointContinuationStatement`) to its generic Fourier
coefficient, which gives `CuspidalPairEisensteinHolomorphyStatement` (Shahidi 1981, proof of
Theorem 5.1, p. 352). -/

noncomputable section

set_option autoImplicit false

universe u

open NumberField MeasureTheory Metric Set Filter Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairEisenstein

open RankinSelbergGlobal AdelicSubgroupPoints

local instance reductionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance reductionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F]

/-- The generic coefficient `∫_{N(F) \ N(𝔸)} f(u) conj(ψ_N(u)) du` at the identity of a
function `f` on `GL_(n+2)(𝔸)`, with the generic character of `ψ` and the normalized quotient
measure. For `n = r + t` and `f = E(φ, s, ·)` it is `coeff ψ φ s` by definition. -/
def genericCoeff (n : ℕ) (ψ : AddChar (Adeles F) ℂ) (f : AdelicGL F (n + 2) → ℂ) : ℂ :=
  generalLinearWhittakerFunction F (n + 1) ψ (fun _ => 1)
    (fun g => f (GeneralLinearGroupPoints.adelicEquiv F (n + 2) g)) 1

/-- The generic coefficient is homogeneous: the Lean integral is linear in constant factors
whether or not the integrand is integrable. -/
theorem genericCoeff_const_mul (n : ℕ) (ψ : AddChar (Adeles F) ℂ) (c : ℂ)
    (f : AdelicGL F (n + 2) → ℂ) :
    genericCoeff n ψ (fun g => c * f g) = c * genericCoeff n ψ f := by
  simp only [genericCoeff, generalLinearWhittakerFunction, subgroupCharacterCoefficient,
    mul_assoc]
  exact integral_const_mul c _

/-- **Holomorphy under the compact unipotent integral.** If `k(s, g)` is jointly continuous on
`W × GL_(n+2)(𝔸)`, holomorphic in `s ∈ W` and left invariant under `GL_(n+2)(F)`, then its
generic coefficient is holomorphic on `W`. -/
theorem differentiableOn_genericCoeff (n : ℕ) (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) (k : ℂ → AdelicGL F (n + 2) → ℂ) {W : Set ℂ}
    (hW : IsOpen W)
    (hk : ContinuousOn (fun q : ℂ × AdelicGL F (n + 2) => k q.1 q.2) (W ×ˢ univ))
    (hkd : ∀ g, DifferentiableOn ℂ (fun s => k s g) W)
    (hinv : ∀ s ∈ W, ∀ (c₀ : RationalGL F (n + 2)) (g : AdelicGL F (n + 2)),
      k s (AdelicGL.rational F (n + 2) c₀ * g) = k s g) :
    DifferentiableOn ℂ (fun s => genericCoeff n ψ (k s)) W := by
  intro s₀ hs₀
  obtain ⟨R, hR, hRW⟩ : ∃ R > 0, closedBall s₀ R ⊆ W := by
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW s₀ hs₀
    exact ⟨ε / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hεW⟩
  set Γ := rationalSubgroup F (Scheme F (n + 1 + 1)) (upperUnipotent F (n + 1 + 1)) with hΓ
  set χ := genericCharacter F (n + 1) ψ (fun _ => 1) with hχ
  let f : ℂ → unipotentAdelic F (n + 1 + 1) → ℂ := fun s x =>
    k s (GeneralLinearGroupPoints.adelicEquiv F (n + 2) ((x : Points F (n + 1 + 1)) * 1)) *
      starRingEnd ℂ (χ x)
  have he : Continuous (GeneralLinearGroupPoints.adelicEquiv F (n + 2)) :=
    (GeneralLinearGroupPoints.adelicHomeomorph F (n + 2)).continuous
  have hfc : ContinuousOn (fun q : ℂ × unipotentAdelic F (n + 1 + 1) => f q.1 q.2)
      (W ×ˢ univ) := by
    have h0 : Continuous fun q : ℂ × unipotentAdelic F (n + 1 + 1) =>
        (q.2 : Points F (n + 1 + 1)) * 1 :=
      (continuous_subtype_val.comp continuous_snd).mul continuous_const
    have h1 : Continuous fun q : ℂ × unipotentAdelic F (n + 1 + 1) =>
        (q.1, GeneralLinearGroupPoints.adelicEquiv F (n + 2)
          ((q.2 : Points F (n + 1 + 1)) * 1)) :=
      continuous_fst.prodMk (he.comp h0)
    have h2 : ContinuousOn (fun q : ℂ × unipotentAdelic F (n + 1 + 1) =>
        k q.1 (GeneralLinearGroupPoints.adelicEquiv F (n + 2)
          ((q.2 : Points F (n + 1 + 1)) * 1))) (W ×ˢ univ) :=
      hk.comp h1.continuousOn fun q hq => ⟨hq.1, mem_univ _⟩
    have h3 : Continuous fun q : ℂ × unipotentAdelic F (n + 1 + 1) => starRingEnd ℂ (χ q.2) :=
      Complex.continuous_conj.comp
        ((Unfolding.continuous_genericCharacter F (n + 1) ψ hψ.1 _).comp continuous_snd)
    exact h2.mul h3.continuousOn
  have hfinv : ∀ s ∈ W, ∀ c ∈ Γ, ∀ x, f s (c * x) = f s x := by
    intro s hs c hc x
    obtain ⟨q, hq⟩ := id hc
    have hc' : ((c : unipotentAdelic F (n + 1 + 1)) : Points F (n + 1 + 1)) =
        AdelicGroupPoints.rational F (Scheme F (n + 1 + 1)) q.val := by
      rw [← hq, rational_coe]
    have hcx : GeneralLinearGroupPoints.adelicEquiv F (n + 2)
        (((c * x : unipotentAdelic F (n + 1 + 1)) : Points F (n + 1 + 1)) * 1) =
        AdelicGL.rational F (n + 2) (GeneralLinearGroupPoints.rationalEquiv F (n + 2) q.val) *
          GeneralLinearGroupPoints.adelicEquiv F (n + 2) ((x : Points F (n + 1 + 1)) * 1) := by
      rw [Subgroup.coe_mul, mul_assoc, map_mul, hc']
      exact congrArg (· * _) (GeneralLinearGroupPoints.adelicEquiv_rational F (n + 2) q.val)
    simp only [f]
    have hχcx : χ (c * x) = χ x :=
      Unfolding.genericCharacter_rational_mul F (n + 1) ψ hψ ⟨c, hc⟩ x
    rw [hcx, hinv s hs, hχcx]
  have hq := ImaginaryAxis.continuousOn_out_of_invariant Γ f W hW hfc hfinv
  have := rationalQuotientBorelSpace F (Scheme F (n + 1 + 1)) (upperUnipotent F (n + 1 + 1))
  have := Unfolding.compactSpace_unipotentRationalQuotient F (n + 1 + 1)
  have := normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F (Scheme F (n + 1 + 1))
    (upperUnipotent F (n + 1 + 1))
  have key := Langlands.Archimedean.MatrixCoefficientAnalytic.hasDerivAt_integral_of_holomorphic
    (normalizedRationalQuotientHaarMeasure F (Scheme F (n + 1 + 1)) (upperUnipotent F (n + 1 + 1)))
    (F := fun s (q : LeftCosetSpace Γ) => f s q.out) hR
    (hq.mono (prod_mono hRW subset_rfl))
    (fun q s hs => by
      simp only [f]
      exact ((hkd _).mono (ball_subset_closedBall.trans hRW) s hs).mul_const _)
  exact key.differentiableAt.differentiableWithinAt

/-- **Reduction.** The joint continuation of the cuspidal-pair Eisenstein series
(`CuspidalPairEisensteinJointContinuationStatement`) implies the continuation and the
imaginary-axis holomorphy of its generic coefficient
(`CuspidalPairEisensteinHolomorphyStatement`). -/
def CuspidalPairEisensteinHolomorphyReductionStatement : Prop :=
  CuspidalPairEisensteinJointContinuationStatement.{u} →
    CuspidalPairEisensteinHolomorphyStatement.{u}

theorem cuspidalPairEisensteinHolomorphyReduction :
    CuspidalPairEisensteinHolomorphyReductionStatement.{u} := by
  intro hJ F _ _ _ r t T T' hT hT' ψ hψ φ hφ
  obtain ⟨E, σ, hEσ, hloc⟩ := hJ F r t T T' hT hT' φ hφ
  refine ⟨fun s => genericCoeff (r + t) ψ (E s), fun s₀ _ => ?_, fun y => ?_, σ,
    fun s hs => ?_⟩
  · obtain ⟨m, W, h, hWo, hs₀, hc, hd, hinv, heq, -⟩ := hloc s₀
    have hH : DifferentiableOn ℂ (fun s => genericCoeff (r + t) ψ (h s)) W :=
      differentiableOn_genericCoeff (r + t) ψ hψ h hWo hc hd hinv
    have hA : AnalyticAt ℂ (fun z => (z - s₀) * genericCoeff (r + t) ψ (h z)) s₀ :=
      (analyticAt_id.sub analyticAt_const).mul (hH.analyticAt (hWo.mem_nhds hs₀))
    refine ⟨m + 1, hA.congr ?_⟩
    filter_upwards [hWo.mem_nhds hs₀] with z hz
    by_cases hzs : z = s₀
    · subst hzs
      simp
    · have hhz : h z = fun g => (z - s₀) ^ m * E z g := funext (heq z hz hzs)
      simp only [hhz, genericCoeff_const_mul, smul_eq_mul, pow_succ]
      ring
  · have hre : ((y : ℂ) * Complex.I).re = 0 := by simp
    obtain ⟨m, W, h, hWo, hs₀, hc, hd, hinv, heq, hax⟩ := hloc (y * Complex.I)
    obtain ⟨rfl, h0⟩ := hax hre
    have hH : DifferentiableOn ℂ (fun s => genericCoeff (r + t) ψ (h s)) W :=
      differentiableOn_genericCoeff (r + t) ψ hψ h hWo hc hd hinv
    refine (hH.analyticAt (hWo.mem_nhds hs₀)).congr ?_
    filter_upwards [hWo.mem_nhds hs₀] with z hz
    by_cases hzs : z = y * Complex.I
    · subst hzs
      simp only [funext h0]
    · have hhz : h z = E z := funext fun g => by rw [heq z hz hzs g, pow_zero, one_mul]
      simp only [hhz]
  · show genericCoeff (r + t) ψ (E s) = coeff (r := r) (t := t) ψ φ s
    rw [hEσ s hs]
    rfl

end Langlands.Global.CuspidalPairEisenstein
