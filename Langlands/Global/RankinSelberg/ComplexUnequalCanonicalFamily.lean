import Langlands.Global.RankinSelberg.ComplexJacquetIntertwiner
import Langlands.Global.RankinSelberg.ComplexLocalUniformDualBounds
import Langlands.Global.RankinSelberg.ComplexUnequalDualFamily

/-! # The unequal-rank integrals along a canonical Jacquet family -/

noncomputable section

open MeasureTheory Metric Set
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open ArchimedeanLocal
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure UnitaryAdditiveCharacter)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexCompactProfileFamily (characterList compactRestriction compactRestriction_isCompactProfile
  standardSection_unitary)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexLocalIwasawa (alpha npart kpart npart_mul_logTorus_mul_kpart)
open ComplexLocalWhittakerGauge (logTorus)
open ComplexUnequalFamily (HasLeftCharacter complexUnequalOrdinaryFamily complexUnequalDualFamily
  ordinary_halfPlaneDomination dual_halfPlaneDomination dualIntegral_eq_prod)
open ComplexJacquet (uniformSimpleRootBound_compact)
open RealConvergenceAnalysis (rootPos)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r t : ℕ}
local notation "P" => Fin (r + 1) → ℂ
local notation "L" => Fin (r + 1) → ℤ
local notation "Std[" l "," q "]" => Automorphic.complexStandardKFinite (r + 1) (characterList l q)
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "H" => Langlands.GeneralLinear (t + 1) ℂ

private theorem uniformSimpleRootBound_constant {X : Type*} (S : Set X)
    (a : ℂˣ) (d : List ComplexCharacterData) (V : H → ℂ) (hV : V ∈ complexWhittakerModel t d a) :
    HasUniformSimpleRootBound S (fun _ => V) := by
  obtain ⟨N, hN⟩ := complexWhittakerSimpleRootMajorization t d a ⟨V, hV⟩
  exact ⟨N, fun J => by
    obtain ⟨C, hC, hb⟩ := hN J []
    refine ⟨C, hC, fun _ _ g => ?_⟩
    let g₀ := logTorus (alpha g) * (kpart g).val
    have hg : (npart g).val * g₀ = g := by
      rw [← mul_assoc, npart_mul_logTorus_mul_kpart]
    have hn : ‖V g‖ = ‖V g₀‖ := by
      rw [← hg, complexWhittakerModel_left_equivariant hV _ (npart g).2, norm_mul]
      simp only [complexWhittakerCharacter, UnitaryAdditiveCharacter.norm_complex, one_mul]
    rw [hn]
    simpa only [List.map_nil, List.prod_nil, Module.End.one_apply, rootPos, g₀] using hb (alpha g) (kpart g)⟩

/-- The exact ordinary and dual unequal-rank integrals for a fixed compact profile in the
larger representation and a fixed smaller Whittaker vector are jointly holomorphic on
uniform right half-planes over a bounded parameter disk. -/
def ComplexUnequalCanonicalFamilyStatement : Prop :=
  ∀ (h : t < r) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    (l : L) (q : P) (f : Std[l, q]) (p : ℂ → P), Differentiable ℂ p →
    ∀ (d : List ComplexCharacterData) (V : H → ℂ), V ∈ complexWhittakerModel t d a →
    ∀ R : ℝ,
    let W (z : ℂ) := continuedJacquet μ a l (p z) (transferProfile l q (p z) f)
    let S := ball (0 : ℂ) R
    ∃ σ : ℝ,
      (∀ z ∈ S, ∀ s : ℂ, σ < s.re →
        Integrable (complexUnequalIntegrand h (W z) V s) D.measure ∧
        Integrable (complexUnequalDualKernel h (W z) V s) (complexUnequalDualMeasure (r := r) (-a) D)) ∧
      DifferentiableOn ℂ (fun u : ℂ × ℂ => complexUnequalIntegral h D (W u.1) V u.2)
        (S ×ˢ {s : ℂ | σ < s.re}) ∧
      DifferentiableOn ℂ (fun u : ℂ × ℂ => complexUnequalDualIntegral h (-a) D (W u.1) V u.2)
        (S ×ˢ {s : ℂ | σ < s.re})

/-- The same jointly holomorphic family, with uniform raw integral bounds on each
closed spectral strip in the right half-plane and across the parameter disk. -/
def ComplexUnequalCanonicalFamilyBoundsStatement : Prop :=
  ∀ (h : t < r) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    (l : L) (q : P) (f : Std[l, q]) (p : ℂ → P), Differentiable ℂ p →
    ∀ (d : List ComplexCharacterData) (V : H → ℂ), V ∈ complexWhittakerModel t d a →
    ∀ R : ℝ,
    let W (z : ℂ) := continuedJacquet μ a l (p z) (transferProfile l q (p z) f)
    let S := ball (0 : ℂ) R
    ∃ σ : ℝ,
      (∀ z ∈ S, ∀ s : ℂ, σ < s.re →
        Integrable (complexUnequalIntegrand h (W z) V s) D.measure ∧
        Integrable (complexUnequalDualKernel h (W z) V s) (complexUnequalDualMeasure (r := r) (-a) D)) ∧
      DifferentiableOn ℂ (fun u : ℂ × ℂ => complexUnequalIntegral h D (W u.1) V u.2)
        (S ×ˢ {s : ℂ | σ < s.re}) ∧
      DifferentiableOn ℂ (fun u : ℂ × ℂ => complexUnequalDualIntegral h (-a) D (W u.1) V u.2)
        (S ×ˢ {s : ℂ | σ < s.re}) ∧
      ∀ x y : ℝ, σ < x → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ S, ∀ s : ℂ, x ≤ s.re → s.re ≤ y →
        ‖complexUnequalIntegral h D (W z) V s‖ ≤ C ∧
        ‖complexUnequalDualIntegral h (-a) D (W z) V s‖ ≤ C

set_option maxHeartbeats 700000 in
theorem complexUnequalCanonicalFamilyBounds : ComplexUnequalCanonicalFamilyBoundsStatement (r := r) (t := t) := by
  intro h μ a D l q f p hp d V hV R
  let J := canonicalJacquetFamily μ a l (compactRestriction f.val) (compactRestriction_isCompactProfile f.2)
  let W (z : ℂ) := continuedJacquet μ a l (p z) (transferProfile l q (p z) f)
  let T : Set (ℂ × ℂ) := ball 0 R ×ˢ univ
  let F (u : ℂ × ℂ) := W u.1
  let B (_ : ℂ × ℂ) := V
  have hT : IsOpen T := isOpen_ball.prod isOpen_univ
  have hJ := canonicalJacquetFamily_properties μ a l _ (compactRestriction_isCompactProfile f.2)
  have heq (z : ℂ) : W z = J (p z) := by
    let f₀ := transferProfile l q (p z) f
    have hφ : compactRestriction f₀.val = compactRestriction f.val :=
      funext fun k => standardSection_unitary (p z) (compactRestriction f.val) k
    change canonicalJacquetFamily μ a l _ (compactRestriction_isCompactProfile f₀.2) (p z) = J (p z)
    exact congrFun (canonicalJacquetFamily_congr μ a l _ _ hφ) (p z)
  have hFχ (u : ℂ × ℂ) : HasLeftCharacter (-a) (F u) := by
    intro n g
    exact (complexJacquetIntertwiner r μ a l (p u.1)).1 _ n.val n.2 g
  have hBχ (u : ℂ × ℂ) : HasLeftCharacter (-(-a)) (B u) := by
    intro n g
    rw [neg_neg]
    exact complexWhittakerModel_left_equivariant hV n.val n.2 g
  have hFc (u : ℂ × ℂ) : Continuous (F u) := by
    change Continuous (W u.1)
    rw [heq]
    exact hJ.1 _
  have hBc (u : ℂ × ℂ) : Continuous (B u) :=
    (contMDiff_of_mem_complexWhittakerModel hV).continuous
  have hFd (g : G) : DifferentiableOn ℂ (F · g) T := by
    simp only [F, heq]
    exact (((hJ.2.1 g).comp hp).comp differentiable_fst).differentiableOn
  have hBd (g : H) : DifferentiableOn ℂ (B · g) T := differentiableOn_const (V g)
  have hFb : HasUniformSimpleRootBound T F := by
    obtain ⟨N, hN⟩ := uniformSimpleRootBound_compact ((isCompact_closedBall (0 : ℂ) R).image hp.continuous)
      J hJ.2.2.1
    refine ⟨N, fun M => ?_⟩
    obtain ⟨C, hC, hb⟩ := hN M
    refine ⟨C, hC, fun u hu g => ?_⟩
    simpa only [F, heq] using hb _ (mem_image_of_mem p (ball_subset_closedBall hu.1)) g
  have hBb : HasUniformSimpleRootBound T B := uniformSimpleRootBound_constant T a d V hV
  obtain ⟨σ, hσ, hZo⟩ := complexUnequalOrdinaryFamily (E := ℂ × ℂ) (a := -a) h D T F B Prod.snd hT
    differentiable_snd hFχ hBχ hFc hBc hFd hBd hFb hBb
  obtain ⟨τ, hτ, hZd⟩ := complexUnequalDualFamily (E := ℂ × ℂ) h (-a) D T F B Prod.snd hT
    differentiable_snd hFχ hBχ hFc hBc hFd hBd hFb hBb
  obtain ⟨σ₀, hOrdDom⟩ := ordinary_halfPlaneDomination (a := -a) h D T F B Prod.snd
    hFχ hBχ hFb hBb
  obtain ⟨τ₀, hDualDom⟩ := dual_halfPlaneDomination h (-a) D T F B Prod.snd hFχ hBχ hFb hBb
  let S₀ := max (max σ τ) (max σ₀ τ₀)
  have hσ₀ : σ ≤ S₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hτ₀ : τ ≤ S₀ := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨S₀, fun z hz s hs => ?_, ?_, ?_, ?_⟩
  · exact ⟨hσ (z, s) ⟨⟨hz, mem_univ s⟩, hσ₀.trans_lt hs⟩,
      hτ (z, s) ⟨⟨hz, mem_univ s⟩, hτ₀.trans_lt hs⟩⟩
  · exact hZo.mono fun u hu => ⟨⟨hu.1, mem_univ u.2⟩, hσ₀.trans_lt hu.2⟩
  · exact hZd.mono fun u hu => ⟨⟨hu.1, mem_univ u.2⟩, hτ₀.trans_lt hu.2⟩
  · intro x y hxy
    obtain ⟨M, hM, hDom⟩ := hOrdDom y
    obtain ⟨Md, hMd, hDomd⟩ := hDualDom y
    let C := ∫ u, ‖M u‖ ∂D.measure
    let Cd := ∫ u, ‖Md u‖ ∂complexUnequalDualMeasure (r := r) (-a) D
    refine ⟨max C Cd, (integral_nonneg fun _ => norm_nonneg _).trans (le_max_left _ _), ?_⟩
    intro z hz s hs ht
    have hS : S₀ < s.re := hxy.trans_le hs
    have hzT : (z, s) ∈ T := ⟨hz, mem_univ s⟩
    have hOrdσ : σ₀ < s.re := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hS
    have hDualτ : τ₀ < s.re := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hS
    constructor
    · apply le_trans _ (le_max_left C Cd)
      apply norm_integral_le_of_norm_le hM.norm
      exact ae_of_all _ fun u => (hDom (z, s) hzT hOrdσ ht u).trans (le_abs_self _)
    · apply le_trans _ (le_max_right C Cd)
      rw [dualIntegral_eq_prod h (-a) D (W z) V s (hτ (z, s) ⟨hzT, hτ₀.trans_lt hS⟩)]
      apply norm_integral_le_of_norm_le hMd.norm
      exact ae_of_all _ fun u => (hDomd (z, s) hzT hDualτ ht u).trans (le_abs_self _)

theorem complexUnequalCanonicalFamily : ComplexUnequalCanonicalFamilyStatement (r := r) (t := t) := by
  intro h μ a D l q f p hp d V hV R
  obtain ⟨σ, hConv, hZ, hZd, _⟩ := complexUnequalCanonicalFamilyBounds h μ a D l q f p hp d V hV R
  exact ⟨σ, hConv, hZ, hZd⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
