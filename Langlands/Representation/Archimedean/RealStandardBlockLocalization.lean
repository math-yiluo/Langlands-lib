import Langlands.Representation.Archimedean.RealBlockCompactLocalization
import Langlands.Representation.Archimedean.RealStandardCompactMultiplier
import Langlands.Representation.Archimedean.RealLeviSlices

/-! # Localization of a nonnegative compact standard-module diagonal -/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealPrincipalSeriesDuality
open RealLeviChart RealLeviBlockHaar RealLeviSlices InductionStages
open OrthogonalFinitePolynomial PrincipalSeriesExtension GramFormula

attribute [local instance] measurableSpaceK secondCountableTopology_O

local instance borelSpaceK_blockLocalization (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

private abbrev K (n : ℕ) := unitaryCompact ℝ n

/-- Compact multipliers invariant under the left action of the block subgroup. -/
def BlockInvariantMultiplier {n c : ℕ} (cl : Fin n → Fin c) (φ : K n → ℂ) : Prop :=
  ∀ (h : Kc cl) k, φ (blockCompactInclusion cl h * k) = φ k

/-- The operator commutes on the compact group with multiplication by
block-invariant weights whenever the weighted vector is in the standard model. -/
def CommutesWithBlockMultipliers {n c : ℕ} (cl : Fin n → Fin c) {ds es : List RealBlock}
    (T : KFin n ds →ₗ[ℂ] KFin n es) : Prop :=
  ∀ (φ : K n → ℂ), BlockInvariantMultiplier cl φ → ∀ (F f : KFin n ds),
    (∀ k : K n, F.val k = φ k * f.val k) →
    ∀ k : K n, (T F).val k = φ k * (T f).val k

theorem CommutesWithBlockMultipliers.comp {n c : ℕ} {cl : Fin n → Fin c}
    {ds es fs : List RealBlock} {T : KFin n ds →ₗ[ℂ] KFin n es}
    {S : KFin n es →ₗ[ℂ] KFin n fs} (hS : CommutesWithBlockMultipliers cl S)
    (hT : CommutesWithBlockMultipliers cl T) : CommutesWithBlockMultipliers cl (S.comp T) :=
  fun φ hφ F f hF => hS φ hφ (T F) (T f) (hT φ hφ F f hF)

private theorem realBlockCompactLocalization_complex {n c : ℕ} (cl : Fin n → Fin c)
    (f : K n → ℂ) (hf : Continuous f)
    (hFull : ∀ φ : Matrix.unitaryGroup (Fin n) ℝ → ℝ, Continuous φ →
      (fun k => (φ k : ℂ)) ∈ polynomialFunctions n →
      BlockInvariantMultiplier cl (fun k => (φ (toUnitary n k) : ℂ)) →
      let w := ∫ k, (φ (toUnitary n k) : ℂ) ^ 2 * f k ∂haarK n
      0 ≤ w.re ∧ w.im = 0) :
    let w := ∫ k, f (blockCompactInclusion cl k) ∂μc cl
    0 ≤ w.re ∧ w.im = 0 := by
  let ι := blockCompactInclusion cl
  have hc : Continuous (fun k => f (ι k)) :=
    hf.comp (continuous_subtype_val.subtype_mk _)
  have hi : Integrable (fun k => f (ι k)) (μc cl) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTest (φ : Matrix.unitaryGroup (Fin n) ℝ → ℝ) (hφ : Continuous φ)
      (hP : (fun k => (φ k : ℂ)) ∈ polynomialFunctions n)
      (hInv : ∀ h : Kc cl, ∀ k, φ (toUnitary n (ι h) * k) = φ k) :
      (0 ≤ ∫ k, φ (toUnitary n k) ^ 2 * (f k).re ∂haarK n) ∧
      (∫ k, φ (toUnitary n k) ^ 2 * (f k).im ∂haarK n) = 0 := by
    have hiInv : BlockInvariantMultiplier cl (fun k => (φ (toUnitary n k) : ℂ)) := by
      intro h k
      change (φ (toUnitary n (ι h * k)) : ℂ) = (φ (toUnitary n k) : ℂ)
      rw [map_mul, hInv h]
    have hct : Continuous (fun k : K n => toUnitary n k) :=
      (Units.continuous_val.comp continuous_subtype_val).subtype_mk _
    have hw : Continuous (fun k : K n => (φ (toUnitary n k) : ℂ) ^ 2 * f k) :=
      ((Complex.continuous_ofReal.comp (hφ.comp hct)).pow 2).mul hf
    have hwi : Integrable (fun k : K n => (φ (toUnitary n k) : ℂ) ^ 2 * f k) (haarK n) :=
      hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hRe := integral_re (μ := haarK n) hwi
    have hIm := integral_im (μ := haarK n) hwi
    simp only [RCLike.re_eq_complex_re, RCLike.im_eq_complex_im,
      ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero] at hRe hIm
    obtain ⟨hRePos, hImZero⟩ := hFull φ hφ hP hiInv
    simp only [← Complex.ofReal_pow] at hRePos hImZero
    exact ⟨hRe.symm ▸ hRePos, hIm.trans hImZero⟩
  have hRe := realBlockCompactLocalization n c cl (fun k => (f k).re)
    (Complex.continuous_re.comp hf) fun φ hφ hP hInv => (hTest φ hφ hP hInv).1
  have hIm := realBlockCompactLocalization n c cl (fun k => (f k).im)
    (Complex.continuous_im.comp hf) fun φ hφ hP hInv => (hTest φ hφ hP hInv).2.ge
  have hNegIm := realBlockCompactLocalization n c cl (fun k => -(f k).im)
    (Complex.continuous_im.comp hf).neg fun φ hφ hP hInv => by
      simp only [mul_neg, integral_neg, (hTest φ hφ hP hInv).2, neg_zero, le_refl]
  simp only [integral_neg] at hNegIm
  change 0 ≤ RCLike.re (∫ k, f (ι k) ∂μc cl) ∧
    RCLike.im (∫ k, f (ι k) ∂μc cl) = 0
  rw [← integral_re hi, ← integral_im hi]
  exact ⟨hRe, le_antisymm (neg_nonneg.mp hNegIm) hIm⟩

private theorem rotation_mem_compactLevi {c : ℕ} (dss : Fin c → List RealBlock)
    {p : ℕ} {d : ComplexCharacterData} (hd : realInducedBlockAt (flat dss) p = some d)
    (θ : ℝ) : blockRotation (∑ i, sz dss i) p θ ∈ Kc (cls (sz dss)) := by
  have hp := realInducedBlockAt_lt hd
  rw [realRank_flat] at hp
  obtain ⟨⟨i, j⟩, he⟩ := finSigmaFinEquiv.surjective
    (⟨p, by omega⟩ : Fin (∑ i, sz dss i))
  change pos (sz dss) i j = _ at he
  have hj : start (sz dss) i + j.val = p := by
    simpa only [val_pos] using congrArg Fin.val he
  have hjd : realInducedBlockAt (dss i) j = some d := by
    rw [← realInducedBlockAt_flat dss i j j.isLt, hj]
    exact hd
  let j' : Fin (sz dss i) := ⟨j.val + 1, realInducedBlockAt_lt hjd⟩
  have he' : pos (sz dss) i j' = ⟨p + 1, hp⟩ := Fin.ext (by rw [val_pos]; dsimp [j']; omega)
  have hcl : cls (sz dss) ⟨p, by omega⟩ = cls (sz dss) ⟨p + 1, hp⟩ := by
    rw [← he, ← he', cls_pos, cls_pos]
  have h := blockRotation_mem_blockOrth hp hcl θ
  exact ⟨mem_unitaryCompact_of_mem_blockOrth h, h.2⟩

private theorem exists_weighted_block_vector {c : ℕ} (dss : Fin c → List RealBlock)
    (φ : Matrix.unitaryGroup (Fin (∑ i, sz dss i)) ℝ → ℂ) (hφ : Continuous φ)
    (hP : φ ∈ polynomialFunctions (∑ i, sz dss i))
    (hI : BlockInvariantMultiplier (cls (sz dss)) (φ ∘ toUnitary (∑ i, sz dss i)))
    (f : KFin (∑ i, sz dss i) (flat dss)) :
    ∃ F : KFin (∑ i, sz dss i) (flat dss),
      ∀ k : K (∑ i, sz dss i), F.val k = φ (toUnitary (∑ i, sz dss i) k) * f.val k := by
  let N := ∑ i, sz dss i
  have hUnits (k : K N) : Unitary.toUnits (toUnitary N k) = k.val := Units.ext rfl
  have hInv (l : Matrix.unitaryGroup (Fin N) ℝ)
      (hl : Unitary.toUnits l ∈ Kc (cls (sz dss))) (k : Matrix.unitaryGroup (Fin N) ℝ) :
      φ (l * k) = φ k := by
    have h := hI ⟨Unitary.toUnits l, hl⟩ (ofUnitary N k)
    change φ (toUnitary N (ofUnitary N l * ofUnitary N k)) =
      φ (toUnitary N (ofUnitary N k)) at h
    simpa only [map_mul, toUnitary_ofUnitary] using h
  obtain ⟨F, hF⟩ := realStandardCompactMultiplier N (flat dss) (realRank_flat dss) φ hφ hP
    (fun a k => hInv _ ⟨(signDiagonal (fun i => (a i : ℝ))).2, fun i j hij => by
      change Matrix.diagonal (fun a' => signReal ((a a' : ℝˣ) : ℝ)) i j = 0
      exact Matrix.diagonal_apply_ne _ (fun he => hij (congrArg _ he))⟩ k)
    (fun p d hd θ k => hInv _ (by
      rw [RealCompactWitnessExtension.compactBlockRotation_toUnits]
      exact rotation_mem_compactLevi dss hd θ) k) f
  exact ⟨F, fun k => by simpa only [hUnits] using hF (toUnitary N k)⟩

/-- For two compact operators that commute with block-invariant multipliers,
a real nonnegative integral of every standard-vector diagonal remains real
and nonnegative on the compact Levi subgroup. -/
def RealStandardBlockLocalizationStatement : Prop :=
  ∀ {c : ℕ} (dss : Fin c → List RealBlock) {es fs : List RealBlock},
    let N := ∑ i, sz dss i
    let cl := cls (sz dss)
    ∀ (S : KFin N (flat dss) →ₗ[ℂ] KFin N es)
      (E : KFin N (flat dss) →ₗ[ℂ] KFin N fs),
      CommutesWithBlockMultipliers cl S → CommutesWithBlockMultipliers cl E →
      ∀ a : ℂ, (∀ f : KFin N (flat dss),
        let w := ∫ k : K N, a * ((S f).val k * conj ((E f).val k)) ∂haarK N
        0 ≤ w.re ∧ w.im = 0) →
      ∀ f : KFin N (flat dss),
        let w := ∫ k : Kc cl, a * ((S f).val k * conj ((E f).val k)) ∂μc cl
        0 ≤ w.re ∧ w.im = 0

theorem realStandardBlockLocalization : RealStandardBlockLocalizationStatement := by
  intro c dss es fs N cl S E hS hE a hPos f
  let ψ : K N → ℂ := fun k => a * ((S f).val k * conj ((E f).val k))
  have hψ : Continuous ψ := continuous_const.mul
    (((continuous_of_mem_kFiniteFunctions (S f).2).comp continuous_subtype_val).mul
      (Complex.continuous_conj.comp
        ((continuous_of_mem_kFiniteFunctions (E f).2).comp continuous_subtype_val)))
  have h := realBlockCompactLocalization_complex cl ψ hψ
  refine h fun φ hφ hP hI => ?_
  obtain ⟨F, hF⟩ := exists_weighted_block_vector dss (fun k => (φ k : ℂ))
    (Complex.continuous_ofReal.comp hφ) hP hI f
  have hS' := hS _ hI F f hF
  have hE' := hE _ hI F f hF
  have he (k : K N) : (φ (toUnitary N k) : ℂ) ^ 2 * ψ k =
      a * ((S F).val k * conj ((E F).val k)) := by
    rw [hS', hE', map_mul, Complex.conj_ofReal]
    dsimp only [ψ]
    ring
  have hInt := integral_congr_ae (μ := haarK N) (Filter.Eventually.of_forall he)
  change 0 ≤ (∫ k : K N, (φ (toUnitary N k) : ℂ) ^ 2 * ψ k ∂haarK N).re ∧
    (∫ k : K N, (φ (toUnitary N k) : ℂ) ^ 2 * ψ k ∂haarK N).im = 0
  rw [hInt]
  exact hPos F

end Langlands.Archimedean
