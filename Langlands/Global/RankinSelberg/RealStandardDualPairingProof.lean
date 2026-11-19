import Langlands.Global.RankinSelberg.RealStandardPairingPremises
import Langlands.Representation.Archimedean.RealTemperedFormProof

/-! # Dual-block pairing for real standard modules

The compact integral pairs the character replacement of a standard module with the
dual-block module. The Fourier multiplier from the character replacement onto the standard
module has kernel annihilated by this pairing, so the pairing descends.
-/

noncomputable section

open MeasureTheory
open scoped ComplexConjugate Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean Langlands.Automorphic Langlands.LocalFactor.Archimedean
open RealLocalJacquet RealBlockPosition RealTemperedForm RealPrincipalSeriesDuality
open GramFormula (realPositionExponent)

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] measurableSpaceK

/-- Dualization and character replacement preserve the position signs, and the position
exponents of the two resulting lists are opposite. -/
private theorem positions_repl_dual :
    ∀ (ds : List RealBlock) (i : ℕ),
      realPositionSign (ds.map dualBlock) i = realPositionSign ds i ∧
      realPositionSign (ds.flatMap repl) i = realPositionSign ds i ∧
      realPositionExponent (ds.map dualBlock) i = -realPositionExponent (ds.flatMap repl) i
  | [], _ => by simp [realPositionSign, realPositionExponent]
  | .character c :: ds, 0 => by
      simp [repl, dualBlock, realPositionSign, realPositionExponent, RealCharacterData.inverse]
  | .character _ :: ds, i + 1 => by
      simpa [repl, dualBlock, realPositionSign, realPositionExponent] using positions_repl_dual ds i
  | .induced d :: ds, 0 => by
      by_cases hw : d.weight = 0
      · simp [repl, dualBlock, hw, realPositionSign, realPositionExponent, ComplexCharacterData.inverse]
      · simp [repl, dualBlock, hw, cLow, RealJacquetFrobenius.charData, realPositionSign,
          realPositionExponent, ComplexCharacterData.inverse]
        ring
  | .induced d :: ds, 1 => by
      by_cases hw : d.weight = 0
      · simp [repl, dualBlock, hw, realPositionSign, realPositionExponent, ComplexCharacterData.inverse]
      · simp [repl, dualBlock, hw, cHigh, RealJacquetFrobenius.charData, realPositionSign,
          realPositionExponent, ComplexCharacterData.inverse]
        ring
  | .induced d :: ds, i + 2 => by
      by_cases hw : d.weight = 0 <;>
        simpa [repl, dualBlock, hw, realPositionSign, realPositionExponent] using
          positions_repl_dual ds i

private theorem positionCharacter_repl_mul_dual (ds : List RealBlock) (i : ℕ) (x : ℝˣ) :
    realPositionCharacter (ds.flatMap repl) i x * realPositionCharacter (ds.map dualBlock) i x =
      1 := by
  obtain ⟨hdual, hrepl, hexp⟩ := positions_repl_dual ds i
  rw [realPositionCharacter_eq_charFun, realPositionCharacter_eq_charFun, hdual, hrepl, hexp]
  let c := RealJacquetFrobenius.charData (realPositionSign ds i)
    (realPositionExponent (ds.flatMap repl) i)
  have h : (c.inverse.character x : ℂ) =
      RealJacquetFrobenius.charFun (realPositionSign ds i)
        (-realPositionExponent (ds.flatMap repl) i) x := c.inverse.character_eq x
  rw [← RealJacquetFrobenius.charData_character_apply, ← h, ← Units.val_mul]
  change (((c.character x) * (c.character x)⁻¹ : ℂˣ) : ℂ) = 1
  rw [mul_inv_cancel]
  rfl

private theorem inducedBlockAt_map_dual : ∀ (ds : List RealBlock) (p : ℕ),
    realInducedBlockAt (ds.map dualBlock) p =
      (realInducedBlockAt ds p).map ComplexCharacterData.inverse
  | [], _ => rfl
  | .character _ :: _, 0 => rfl
  | .character _ :: ds, p + 1 => inducedBlockAt_map_dual ds p
  | .induced _ :: _, 0 => rfl
  | .induced _ :: _, 1 => rfl
  | .induced _ :: ds, p + 2 => inducedBlockAt_map_dual ds p

/-- Conjugating the compact restriction of a dual-block vector gives the compact
restriction of a vector of the original standard module. -/
private theorem exists_compact_conjugate {n : ℕ} {ds : List RealBlock} (hn : realRank ds = n)
    (h : realStandardKFinite n (ds.map dualBlock)) :
    ∃ f : realStandardKFinite n ds, ∀ k ∈ unitaryCompact ℝ n,
      (f : Langlands.GeneralLinear n ℝ → ℂ) k = conj ((h : Langlands.GeneralLinear n ℝ → ℂ) k) := by
  have hps := h.2.1.1
  obtain ⟨f, hf, hconj⟩ := RealLeviModes.exists_ext_conj
    (RealStrictCharacterLanglandsQuotient.isSignedPower ds)
    hps.1.continuous h.2.2 (fun i g => by
      rw [RealBlockFourierFinite.apply_signReflection_mul
        (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one _) hps i g,
        realPositionCharacter_neg_one (ds.map dualBlock), realPositionCharacter_neg_one ds,
        (positions_repl_dual ds i).1]
      simp)
  refine ⟨⟨f, mem_realStandardModule_of_unitaryCompact hn hf.1 ?_, hf.2⟩, hconj⟩
  intro p d hd j hj k hk
  have hd' : realInducedBlockAt (ds.map dualBlock) p = some d.inverse := by
    rw [inducedBlockAt_map_dual, hd]
    rfl
  rw [RealLeviModes.blockFourierCoefficient_of_eq_conj hconj p j hk,
    h.2.1.2 p d.inverse hd' (-j) (by simpa [ComplexCharacterData.inverse] using hj), map_zero]

private theorem pairing_eq_conj_integral {n : ℕ} {ds es : List RealBlock}
    (w : realStandardKFinite n es) (h : realStandardKFinite n (ds.map dualBlock))
    (f : realStandardKFinite n ds)
    (hf : ∀ k ∈ unitaryCompact ℝ n,
      (f : Langlands.GeneralLinear n ℝ → ℂ) k = conj ((h : Langlands.GeneralLinear n ℝ → ℂ) k)) :
    pairing n es (ds.map dualBlock) w h = conj (∫ k : unitaryCompact ℝ n,
      (f : Langlands.GeneralLinear n ℝ → ℂ) k * conj ((w : Langlands.GeneralLinear n ℝ → ℂ) k)
        ∂haarK n) := by
  rw [pairing_apply, ← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  dsimp only
  rw [map_mul, hf k k.2, Complex.conj_conj, Complex.conj_conj, mul_comm]

/-- The bilinear pairing with the dual-block module is invariant and separates
every vector of the dual-block module. -/
theorem realStandardDualPairing : RealStandardDualPairingStatement := by
  intro n ds hn _
  have hchain : ChainData (n := n) 0 (ds.flatMap repl) ds := by
    simpa using chain (n := n) ds [] (by simpa using hn)
  obtain ⟨T, S, L, W, hTS, hSK, hTL, hL, -, hW⟩ := hchain
  let P := pairing n (ds.flatMap repl) (ds.map dualBlock)
  refine ⟨P.comp S, ⟨?_, ?_⟩, ?_⟩
  · intro k f h
    simp only [LinearMap.comp_apply, hSK]
    exact pairing_rightTranslation _ _ ⟨Unitary.toUnits k, k.2⟩ (S f) h _ _
  · intro X f h
    simp only [LinearMap.comp_apply]
    let w := S (realStandardLie n ds (1 ⊗ₜ X) f) -
      realStandardLie n (ds.flatMap repl) (1 ⊗ₜ X) (S f)
    have hw : T w = 0 := by
      dsimp only [w]
      rw [map_sub, hTS, hTL, hTS, sub_self]
    obtain ⟨g, hg⟩ := exists_compact_conjugate hn h
    have hzero : P.flip h w = 0 := by
      change pairing n (ds.flatMap repl) (ds.map dualBlock) w h = 0
      rw [pairing_eq_conj_integral w h g hg,
        integral_mul_conj_eq_zero_of_ker hTS hL hW g hw, map_zero]
    dsimp only [w] at hzero
    rw [map_sub] at hzero
    change P (S (realStandardLie n ds (1 ⊗ₜ X) f)) h -
      P (realStandardLie n (ds.flatMap repl) (1 ⊗ₜ X) (S f)) h = 0 at hzero
    have hLie {es : List RealBlock} (v : realStandardKFinite n es) :
        realStandardLie n es (1 ⊗ₜ X) v =
          ⟨_, rightDerivative_mem_kFiniteFunctions_realStandardModule n es v.2 X⟩ :=
      Subtype.ext (realStandardLie_one_tmul_apply_coe n es X v)
    rw [sub_eq_zero.mp hzero, hLie (S f), hLie h]
    exact pairing_rightDerivative _ _ (positionCharacter_repl_mul_dual ds) X (S f) h _ _
  · intro h hh
    obtain ⟨f, hf⟩ := exists_compact_conjugate hn h
    refine ⟨f, fun hz => hh ?_⟩
    change pairing n (ds.flatMap repl) (ds.map dualBlock) (S f) h = 0 at hz
    rw [pairing_eq_conj_integral (S f) h f hf] at hz
    have hf0 := eq_zero_of_integral_mul_conj hTS hL hW f
      ((map_eq_zero_iff (starRingEnd ℂ) (starRingEnd ℂ).injective).mp hz)
    apply Subtype.ext
    refine eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact h.2.1.1 fun k hk => ?_
    have hconj := hf k hk
    rw [hf0] at hconj
    simpa using (congrArg (starRingEnd ℂ) hconj).symm

end Langlands.Global.RankinSelbergGlobal
