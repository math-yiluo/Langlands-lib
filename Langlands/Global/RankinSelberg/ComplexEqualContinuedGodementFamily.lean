import Langlands.Global.RankinSelberg.ComplexGodementGeneratorFamily
import Langlands.Global.RankinSelberg.ComplexLocalEqualFamily
import Langlands.Global.RankinSelberg.ComplexWhittakerTranslatedMellin

/-! # Ordinary equal-rank families of continued complex Godement tests -/

noncomputable section

open MeasureTheory Metric Set
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SchwartzMatrixNorm (EntrySchwartz)
open ComplexGodementAddedCharacter (continuedValue)
open ComplexGodementGeneratorFamily (differentiable_generatorValue)
open ComplexGodementParametric (continuous_continuedValue)
open ComplexGodementRootBounds (HasLeftWhittakerLaw complexGodementRootBounds)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexUnequalFamily (HasLeftCharacter)
open ComplexWhittakerTranslatedMellin (compact_rightTranslate_uniformSimpleRootBound)

attribute [local instance] archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel
  archimedeanComplexQMeasurable archimedeanComplexQBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => r + 1 + 1
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ

private theorem constant_rootBound {k : ℕ} {X : Type*} (S : Set X) {d : List ComplexCharacterData}
    {a : ℂˣ} (U : complexWhittakerModel k d a) : HasUniformSimpleRootBound S (fun _ => U.val) := by
  obtain ⟨N, hN⟩ := compact_rightTranslate_uniformSimpleRootBound U {1} isCompact_singleton
  refine ⟨N, fun J => ?_⟩
  obtain ⟨C, hC, hC'⟩ := hN J
  exact ⟨C, hC, fun _ _ x => by simpa only [mul_one] using hC' 1 (mem_singleton _) x⟩

/-- The continued Godement integral at a fixed smaller coefficient varies holomorphically in the
adjoining exponent. If its larger left Whittaker law is known on a right half-plane, the ordinary
larger equal-rank integrals are jointly holomorphic on uniform right half-planes over bounded
adjoining-parameter disks. -/
def ComplexEqualContinuedGodementFamilyStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r)
    (a : ℂˣ) (d : ComplexCharacterData) (ds es : List ComplexCharacterData)
    (U : complexWhittakerModel r ds a) (V : complexWhittakerModel (r + 1) es (-a))
    (Φ : EntrySchwartz m n) (φ : 𝓢(Fin n → ℂ, ℂ)),
    let W (z : ℂ) (g : G) := continuedValue D₁.groupHaar (complexSelfDualMeasure (-a)) d (-a) Φ U.val g z
    (∃ τ : ℝ, ∀ z : ℂ, τ < z.re → HasLeftCharacter a (W z)) →
    ∀ R : ℝ, let S := ball (0 : ℂ) R
    ∃ σ : ℝ, (∀ z ∈ S, ∀ s : ℂ, σ < s.re → Integrable (complexEqualIntegrand (W z) V.val φ s) D.measure) ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => complexEqualIntegral D (W x.1) V.val φ x.2)
        (S ×ˢ {s : ℂ | σ < s.re})

set_option maxHeartbeats 1000000 in
theorem complexEqualContinuedGodementFamily : ComplexEqualContinuedGodementFamilyStatement (r := r) := by
  intro D D₁ a d ds es U V Φ φ W ⟨τ, hτ⟩ R S
  let ν := D₁.groupHaar
  let : ν.IsHaarMeasure := D₁.groupHaar_isHaar
  let μ := complexSelfDualMeasure (-a)
  let Q := Fin m → ℂ
  let P := Fin n → ℂ
  let f : Q → H → ℂ := fun _ => U.val
  have hUc : Continuous U.val := (contMDiff_of_mem_complexWhittakerModel U.2).continuous
  let line (z : ℂ) : P := Fin.cons z (0 : Q)
  have hl : Differentiable ℂ line := by
    apply differentiable_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact differentiable_id
    · exact differentiable_const _
  have hF (g : G) : Differentiable ℂ (fun z => W z g) := by
    have h := differentiable_generatorValue ν μ (-a) d Φ f (fun _ => hUc)
      (fun h => differentiable_const (U.val h))
      (fun q => ⟨1, one_pos, constant_rootBound (ball q 1) U⟩) g
    exact h.comp hl
  have hLeft (z : ℂ) : HasLeftCharacter a (W z) := by
    intro u g
    let z₀ : ℂ := ((τ + 1 : ℝ) : ℂ)
    have hz₀ : τ < z₀.re := by simpa only [z₀, Complex.ofReal_re] using lt_add_one τ
    have he := AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => (hF (u.val * g)).analyticAt z)
      (fun z _ => ((hF g).const_mul (complexWhittakerCharacter a u.val)).analyticAt z)
      (z₀ := z₀) (by
        filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀] with z hz
        exact hτ z hz u g)
    exact congrFun he z
  have hWc (z : ℂ) : Continuous (W z) :=
    continuous_continuedValue ν μ (-a) d (univ : Set ℂ) (fun _ => U.val) (fun _ _ => hUc)
      (constant_rootBound _ U) z (mem_univ z) Φ z
  let c : ℂ := (((m : ℕ) + 1 : ℂ) / 2)
  have hT (z : ℂ) (hz : z ∈ S) : |(c + z - 1).re| ≤ |c.re - 1| + max R 0 := by
    have hNorm : ‖z‖ ≤ max R 0 := by
      change z ∈ ball (0 : ℂ) R at hz
      rw [mem_ball, dist_zero_right] at hz
      exact hz.le.trans (le_max_left _ _)
    rw [Complex.sub_re, Complex.add_re, Complex.one_re, add_sub_right_comm]
    exact (abs_add_le _ _).trans (add_le_add le_rfl ((Complex.abs_re_le_norm z).trans hNorm))
  have hWB : HasUniformSimpleRootBound S W := by
    apply complexGodementRootBounds (r := r) ν μ (-a) d S (fun _ => U.val) (fun _ _ => hUc)
      (constant_rootBound _ U) Φ id (|c.re - 1| + max R 0) (by positivity) hT
    intro z hz u hu g
    change W z (u * g) = complexWhittakerCharacter (-(-a)) u * W z g
    simpa only [neg_neg] using hLeft z ⟨u, hu⟩ g
  let B := S ×ˢ (univ : Set ℂ)
  have hB : IsOpen B := isOpen_ball.prod isOpen_univ
  have hWb : HasUniformSimpleRootBound B (fun x : ℂ × ℂ => W x.1) := by
    obtain ⟨N, hN⟩ := hWB
    refine ⟨N, fun J => ?_⟩
    obtain ⟨C, hC, hCb⟩ := hN J
    exact ⟨C, hC, fun x hx g => hCb x.1 hx.1 g⟩
  obtain ⟨σ, hi, hd⟩ := complexLocalEqualFamily a D B (fun x : ℂ × ℂ => W x.1) (fun _ => V.val)
    Prod.snd φ hB differentiable_snd (fun x => hLeft x.1)
    (fun _ u g => complexWhittakerModel_left_equivariant V.2 u.val u.2 g) (fun x => hWc x.1)
    (fun _ => (contMDiff_of_mem_complexWhittakerModel V.2).continuous)
    (fun g => ((hF g).comp differentiable_fst).differentiableOn) (fun g => differentiableOn_const (V.val g))
    hWb (constant_rootBound B V)
  exact ⟨σ, fun z hz s hs => hi (z, s) ⟨⟨hz, mem_univ s⟩, hs⟩,
    hd.mono (fun x hx => ⟨⟨hx.1, mem_univ x.2⟩, hx.2⟩)⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
