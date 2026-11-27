import Langlands.Global.RankinSelberg.RealParabolicSectionMultiplier
import Langlands.Global.RankinSelberg.RealExactWhittakerUniqueness
import Langlands.Global.RankinSelberg.RealPrincipalSeriesSmoothQuotient

/-! # Ascending quotients of compact parabolic sections -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open TopologicalSpace
open scoped Distributions Matrix.Norms.Operator Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

open RealStandardCompactBanach RealPrincipalSeries RealBlockFrobeniusMap RealBlockMultiplier
open RealExactWhittakerUniqueness RealStrictCharacterLanglandsQuotient

private local instance (d : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier d ds) :=
  (closureSubmodule (n := d) ds).normedAddCommGroup

private local instance (d : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier d ds) :=
  (closureSubmodule (n := d) ds).normedSpace

local notation "G" => fun d : ℕ => Langlands.GeneralLinear d ℝ
local notation "S" => realStandardModule
local notation:max "D" d:max ds:max => DerivativeSmoothVectors (matrixModel ℝ d) (representation (n := d) ds)
local notation:max "act" d:max ds:max => DerivativeSmoothVectors.representation (matrixModel ℝ d)
  (representation (n := d) ds)
local notation:max "V" d:max ds:max => Automorphic.realStandardKFinite d ds

/-- A continuous map of genuine smooth standard carriers intertwines all translations and
lifts each compact-finite vector to a compact-finite vector. -/
def IsSmoothStandardQuotientMap {d : ℕ} {ds es : List RealBlock} (T : D d ds →L[ℂ] D d es) : Prop :=
  (∀ g v, T (act d ds g v) = act d es g (T v)) ∧
  ∀ f : V d es, ∃ f' : V d ds, T (compactFiniteEquiv ds f').val = (compactFiniteEquiv es f).val

namespace IsSmoothStandardQuotientMap

protected theorem id (d : ℕ) (ds : List RealBlock) :
    IsSmoothStandardQuotientMap (ContinuousLinearMap.id ℂ (D d ds)) :=
  ⟨fun _ _ => rfl, fun f => ⟨f, rfl⟩⟩

protected theorem comp {d : ℕ} {ds es fs : List RealBlock}
    {T : D d ds →L[ℂ] D d es} {U : D d es →L[ℂ] D d fs}
    (hU : IsSmoothStandardQuotientMap U) (hT : IsSmoothStandardQuotientMap T) :
    IsSmoothStandardQuotientMap (U.comp T) := by
  refine ⟨fun g v => by simp only [ContinuousLinearMap.comp_apply, hT.1, hU.1], fun f => ?_⟩
  obtain ⟨e, he⟩ := hU.2 f
  obtain ⟨d, hd⟩ := hT.2 e
  exact ⟨d, by rw [ContinuousLinearMap.comp_apply, hd, he]⟩

end IsSmoothStandardQuotientMap

/-- A smooth parabolic quotient carries compact transverse sections to the same sections with
the two Levi maps applied to their pure inputs. All group ranks are positive. -/
def SmoothParabolicQuotient (m p : ℕ) (d₁ d₂ e₁ e₂ : List RealBlock) : Prop :=
  ∃ (hd₁ : realRank d₁ = m + 1) (hd₂ : realRank d₂ = p + 1)
    (he₁ : realRank e₁ = m + 1) (he₂ : realRank e₂ = p + 1)
    (T : D (p + 1 + m + 1) (d₂ ++ d₁) →L[ℂ] D (p + 1 + m + 1) (e₂ ++ e₁))
    (Q₁ : D (m + 1) d₁ →L[ℂ] D (m + 1) e₁) (Q₂ : D (p + 1) d₂ →L[ℂ] D (p + 1) e₂),
    IsSmoothStandardQuotientMap T ∧
    ∀ (f : S (m + 1) d₁) (g : S (p + 1) d₂)
      (φ : 𝓓((⊤ : Opens (Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ)), ℂ)),
      T (smoothSectionVector hd₁ hd₂ f g φ) =
        smoothSectionVector he₁ he₂ ((derivativeEquiv e₁).symm (Q₁ (derivativeEquiv d₁ f)))
          ((derivativeEquiv e₂).symm (Q₂ (derivativeEquiv d₂ g))) φ

namespace SmoothParabolicQuotient

protected theorem refl {m p : ℕ} {d₁ d₂ : List RealBlock} (h₁ : realRank d₁ = m + 1)
    (h₂ : realRank d₂ = p + 1) : SmoothParabolicQuotient m p d₁ d₂ d₁ d₂ := by
  refine ⟨h₁, h₂, h₁, h₂, ContinuousLinearMap.id ℂ _, ContinuousLinearMap.id ℂ _,
    ContinuousLinearMap.id ℂ _, IsSmoothStandardQuotientMap.id _ _, fun f g φ => ?_⟩
  simp only [ContinuousLinearMap.id_apply, LinearEquiv.symm_apply_apply]

protected theorem trans {m p : ℕ} {d₁ d₂ e₁ e₂ f₁ f₂ : List RealBlock}
    (h : SmoothParabolicQuotient m p d₁ d₂ e₁ e₂) (h' : SmoothParabolicQuotient m p e₁ e₂ f₁ f₂) :
    SmoothParabolicQuotient m p d₁ d₂ f₁ f₂ := by
  obtain ⟨hd₁, hd₂, he₁, he₂, T, Q₁, Q₂, hT, hsec⟩ := h
  obtain ⟨he₁', he₂', hf₁, hf₂, T', Q₁', Q₂', hT', hsec'⟩ := h'
  refine ⟨hd₁, hd₂, hf₁, hf₂, T'.comp T, Q₁'.comp Q₁, Q₂'.comp Q₂,
    hT'.comp hT, fun v w φ => ?_⟩
  rw [ContinuousLinearMap.comp_apply, hsec, hsec']
  simp only [LinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply]

end SmoothParabolicQuotient

private abbrev upperParity (d : ComplexCharacterData) : Fin 2 :=
  RealGammaReflection.positionParity d.weight.natAbs
private abbrev lowChar (d : ComplexCharacterData) : RealCharacterData := RealInducedCharacter.cb d 0
private abbrev highChar (d : ComplexCharacterData) : RealCharacterData := RealInducedCharacter.ca d (upperParity d)
private abbrev tailPair (d : ComplexCharacterData) : List RealBlock :=
  [.character (lowChar d), .character (highChar d)]
private abbrev tailParity (d : ComplexCharacterData) : ℤ := RealCharacterPair.pairParity (lowChar d) (highChar d)
private abbrev tailSign (d : ComplexCharacterData) : ℂ := (-1) ^ (upperParity d).val
private abbrev tailSymbol (d : ComplexCharacterData) : ℤ → ℂ :=
  tailMultiplier d.weight.natAbs (tailParity d) (tailSign d)

private def HasSmoothBlockQuotient (r p : ℕ) (ds es : List RealBlock) (μ : ℤ → ℂ) : Prop :=
  ∃ T : D (r + 1) ds →L[ℂ] D (r + 1) es,
    IsSmoothStandardQuotientMap T ∧ IsSmoothBlockFourierMultiplier p μ T

private theorem exists_tail_quotient (r : ℕ) (pre post : List RealBlock) (d : ComplexCharacterData)
    (hr : realRank (pre ++ [.induced d] ++ post) = r + 1) (hw : d.weight ≠ 0) :
    HasSmoothBlockQuotient r (realRank pre) (pre ++ tailPair d ++ post) (pre ++ [.induced d] ++ post)
      (tailSymbol d) := by
  let w := d.weight.natAbs
  have hl : 0 < w := Int.natAbs_pos.mpr hw
  have hp : ((upperParity d).val + (0 : Fin 2).val) % 2 = (w + 1) % 2 := by
    change ((RealGammaReflection.positionParity w).val + (0 : Fin 2).val) % 2 = _
    rw [RealGammaReflection.positionParity, Fin.val_add]
    change ((w % 2 + 1) % 2 + 0) % 2 = _
    omega
  let h := RealInducedCharacter.data_tail hr hl hp
  have hrec := RealInducedCharacter.isRecurrent_tail (pre := pre) (post := post) hl hp
  let C := ((w + (tailParity d).toNat + 1 : ℕ) : ℝ) ^ w
  obtain ⟨T, hf, hG, hFourier⟩ := realSmoothBlockFourierMultiplier r _ w _ _ _ _ _ h hrec C
    (by dsimp only [C]; positivity) (RealBlockFourierDecay.norm_tailMultiplier_le w (tailParity d) (by simp))
  refine ⟨T, ⟨hG, fun f => ?_⟩, hFourier⟩
  obtain ⟨f', hf'⟩ := RealInducedCharacter.tail_surjective hr hl hp f
  exact ⟨f', (hf f').trans (congrArg (fun v => (compactFiniteEquiv _ v).val) hf')⟩

private theorem realRank_tailPair (pre post : List RealBlock) (d : ComplexCharacterData) :
    realRank (pre ++ tailPair d ++ post) = realRank (pre ++ [.induced d] ++ post) := by
  simp only [realRank_append]
  rfl

set_option maxHeartbeats 650000 in
private theorem parabolic_tail_first (m p : ℕ) (pre post d₂ : List RealBlock) (d : ComplexCharacterData)
    (hm : realRank (pre ++ [.induced d] ++ post) = m + 1) (hp : realRank d₂ = p + 1)
    (hw : d.weight ≠ 0) :
    SmoothParabolicQuotient m p (pre ++ tailPair d ++ post) d₂ (pre ++ [.induced d] ++ post) d₂ := by
  obtain ⟨Q, _, hQ⟩ := exists_tail_quotient m pre post d hm hw
  have hBig : realRank ((d₂ ++ pre) ++ [.induced d] ++ post) = p + 1 + m + 1 := by
    simp only [realRank_append] at hm ⊢
    omega
  have hSrc : (d₂ ++ pre) ++ tailPair d ++ post = d₂ ++ (pre ++ tailPair d ++ post) := by
    simp only [List.append_assoc]
  have hTarget : (d₂ ++ pre) ++ [.induced d] ++ post = d₂ ++ (pre ++ [.induced d] ++ post) := by
    simp only [List.append_assoc]
  have hB := exists_tail_quotient (p + 1 + m) (d₂ ++ pre) post d hBig hw
  rw [hSrc, hTarget, realRank_append, hp] at hB
  obtain ⟨T, hT, hF⟩ := hB
  have hFirst := (realRank_tailPair pre post d).trans hm
  refine ⟨hFirst, hp, hm, hp, T, Q, ContinuousLinearMap.id ℂ _, hT, fun f g φ => ?_⟩
  have hb : realRank pre + 1 < m + 1 := by
    have h : realRank [.induced d] = 2 := rfl
    simp only [realRank_append, h] at hm
    omega
  simpa only [ContinuousLinearMap.id_apply, LinearEquiv.symm_apply_apply] using
    smoothSectionVector_multiplier_first hFirst hp hm hb (tailSymbol d) T Q hF hQ f g φ

set_option maxHeartbeats 650000 in
private theorem parabolic_tail_second (m p : ℕ) (pre post d₁ : List RealBlock) (d : ComplexCharacterData)
    (hp : realRank (pre ++ [.induced d] ++ post) = p + 1) (hm : realRank d₁ = m + 1)
    (hw : d.weight ≠ 0) :
    SmoothParabolicQuotient m p d₁ (pre ++ tailPair d ++ post) d₁ (pre ++ [.induced d] ++ post) := by
  obtain ⟨Q, _, hQ⟩ := exists_tail_quotient p pre post d hp hw
  have hBig : realRank (pre ++ [.induced d] ++ (post ++ d₁)) = p + 1 + m + 1 := by
    simp only [realRank_append] at hp ⊢
    omega
  have hSrc : pre ++ tailPair d ++ (post ++ d₁) = (pre ++ tailPair d ++ post) ++ d₁ := by
    simp only [List.append_assoc]
  have hTarget : pre ++ [.induced d] ++ (post ++ d₁) = (pre ++ [.induced d] ++ post) ++ d₁ := by
    simp only [List.append_assoc]
  have hB := exists_tail_quotient (p + 1 + m) pre (post ++ d₁) d hBig hw
  rw [hSrc, hTarget] at hB
  obtain ⟨T, hT, hF⟩ := hB
  have hSecond := (realRank_tailPair pre post d).trans hp
  refine ⟨hm, hSecond, hm, hp, T, ContinuousLinearMap.id ℂ _, Q, hT, fun f g φ => ?_⟩
  have hb : realRank pre + 1 < p + 1 := by
    have h : realRank [.induced d] = 2 := rfl
    simp only [realRank_append, h] at hp
    omega
  simpa only [ContinuousLinearMap.id_apply, LinearEquiv.symm_apply_apply] using
    smoothSectionVector_multiplier_second hm hSecond hp hb (tailSymbol d) T Q hF hQ f g φ

set_option maxHeartbeats 650000 in
private theorem parabolic_quotient_of_eq {m p : ℕ} {d₁ d₂ e₁ e₂ : List RealBlock}
    (hd₁ : realRank d₁ = m + 1) (hd₂ : realRank d₂ = p + 1)
    (he₁ : realRank e₁ = m + 1) (he₂ : realRank e₂ = p + 1)
    (h₁ : S (m + 1) d₁ = S (m + 1) e₁) (h₂ : S (p + 1) d₂ = S (p + 1) e₂)
    (h : S (p + 1 + m + 1) (d₂ ++ d₁) = S (p + 1 + m + 1) (e₂ ++ e₁)) :
    SmoothParabolicQuotient m p d₁ d₂ e₁ e₂ := by
  obtain ⟨Q₁, _, _, hQ₁⟩ := SmoothStandardQuotient.exists_preserving_function_of_eq h₁
  obtain ⟨Q₂, _, _, hQ₂⟩ := SmoothStandardQuotient.exists_preserving_function_of_eq h₂
  obtain ⟨T, hG, hSurj, hT⟩ := SmoothStandardQuotient.exists_preserving_function_of_eq h
  refine ⟨hd₁, hd₂, he₁, he₂, T, Q₁, Q₂, ⟨hG, hSurj⟩, fun f g φ => ?_⟩
  let f' := (derivativeEquiv e₁).symm (Q₁ (derivativeEquiv d₁ f))
  let g' := (derivativeEquiv e₂).symm (Q₂ (derivativeEquiv d₂ g))
  have hf' : f'.val = f.val := by
    simpa only [LinearEquiv.symm_apply_apply] using hQ₁ (derivativeEquiv d₁ f)
  have hg' : g'.val = g.val := by
    simpa only [LinearEquiv.symm_apply_apply] using hQ₂ (derivativeEquiv d₂ g)
  apply (derivativeEquiv (e₂ ++ e₁)).symm.injective
  apply Subtype.ext
  rw [hT]
  funext u
  have hF := reconstruct_translate_smoothSectionVector hd₁ hd₂ f g φ 1 u
  have hF' := reconstruct_translate_smoothSectionVector he₁ he₂ f' g' φ 1 u
  simp only [map_one, Module.End.one_apply, mul_one] at hF hF'
  exact hF.trans (by rw [← hf', ← hg', ← hF'])

private theorem ascendingExpand_induced (d : ComplexCharacterData) :
    ascendingExpand [.induced d] =
      if d.weight = 0 then [.character (highChar d), .character (lowChar d)] else tailPair d := by
  simp only [ascendingExpand, ascendingCharacters, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change ((if d.weight = 0 then [highChar d, lowChar d] else [lowChar d, highChar d]).map
    RealBlock.character) = _
  split_ifs <;> rfl

private theorem standardModule_ascendingSingleton_zero (k : ℕ) (pre post : List RealBlock)
    (d : ComplexCharacterData) (hw : d.weight = 0) :
    S k (pre ++ ascendingExpand [.induced d] ++ post) = S k (pre ++ [.induced d] ++ post) := by
  have he : ascendingExpand [.induced d] = realBlockExpand (.induced d) := by
    have hp : upperParity d = (1 : Fin 2) := by
      change RealGammaReflection.positionParity d.weight.natAbs = _
      rw [hw, Int.natAbs_zero]
      rfl
    rw [ascendingExpand_induced]
    simp only [hw, hp, ite_true, realBlockExpand, RealInducedCharacter.ca, RealInducedCharacter.cb,
      RealInducedCharacter.aExp, RealInducedCharacter.bExp, Int.natAbs_zero,
      Nat.cast_zero, zero_div, add_zero, sub_zero]
  rw [he]
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    (realStandardModule_append_expand k pre post (.induced d)).symm

private theorem ascendingSingleton_first (m p : ℕ) (d₂ pre post : List RealBlock) (b : RealBlock)
    (hm : realRank (pre ++ [b] ++ post) = m + 1) (hp : realRank d₂ = p + 1) :
    SmoothParabolicQuotient m p (pre ++ ascendingExpand [b] ++ post) d₂ (pre ++ [b] ++ post) d₂ := by
  cases b with
  | character c => exact SmoothParabolicQuotient.refl hm hp
  | induced d =>
    by_cases hw : d.weight = 0
    · have hr : realRank (pre ++ ascendingExpand [.induced d] ++ post) = m + 1 := by
        simpa only [realRank_append, realRank_ascendingExpand] using hm
      apply parabolic_quotient_of_eq hr hp hm hp (standardModule_ascendingSingleton_zero _ pre post d hw) rfl
      simpa only [List.append_assoc] using standardModule_ascendingSingleton_zero (p + 1 + m + 1)
        (d₂ ++ pre) post d hw
    · rw [ascendingExpand_induced, ite_eq_right hw]
      exact parabolic_tail_first m p pre post d₂ d hm hp hw

private theorem ascendingSingleton_second (m p : ℕ) (d₁ pre post : List RealBlock) (b : RealBlock)
    (hm : realRank d₁ = m + 1) (hp : realRank (pre ++ [b] ++ post) = p + 1) :
    SmoothParabolicQuotient m p d₁ (pre ++ ascendingExpand [b] ++ post) d₁ (pre ++ [b] ++ post) := by
  cases b with
  | character c => exact SmoothParabolicQuotient.refl hm hp
  | induced d =>
    by_cases hw : d.weight = 0
    · have hr : realRank (pre ++ ascendingExpand [.induced d] ++ post) = p + 1 := by
        simpa only [realRank_append, realRank_ascendingExpand] using hp
      apply parabolic_quotient_of_eq hm hr hm hp rfl (standardModule_ascendingSingleton_zero _ pre post d hw)
      simpa only [List.append_assoc] using standardModule_ascendingSingleton_zero (p + 1 + m + 1)
        pre (post ++ d₁) d hw
    · rw [ascendingExpand_induced, ite_eq_right hw]
      exact parabolic_tail_second m p pre post d₁ d hp hm hw

private theorem ascendingExpand_cons_eq (b : RealBlock) (ds : List RealBlock) :
    ascendingExpand (b :: ds) = ascendingExpand [b] ++ ascendingExpand ds := by
  simp only [ascendingExpand, ascendingCharacters, List.flatMap_cons, List.flatMap_nil,
    List.map_append, List.append_nil]

private theorem ascendingExpand_rel (r : ℕ) (R : List RealBlock → List RealBlock → Prop)
    (hRefl : ∀ l, realRank l = r + 1 → R l l)
    (hTrans : ∀ {l s t}, R l s → R s t → R l t)
    (hSingle : ∀ pre post b, realRank (pre ++ [b] ++ post) = r + 1 →
      R (pre ++ ascendingExpand [b] ++ post) (pre ++ [b] ++ post)) :
    ∀ (ds pre post : List RealBlock), realRank (pre ++ ds ++ post) = r + 1 →
      R (pre ++ ascendingExpand ds ++ post) (pre ++ ds ++ post)
  | [], pre, post, h => hRefl _ h
  | b :: ds, pre, post, h => by
    let pre' := pre ++ ascendingExpand [b]
    have hr' : realRank (pre' ++ ds ++ post) = r + 1 := by
      simpa only [pre', realRank_append, realRank_ascendingExpand, realRank_cons, realRank_nil,
        add_zero, add_assoc] using h
    have h₀ := ascendingExpand_rel r R hRefl @hTrans hSingle ds pre' post hr'
    have h₁ := hSingle pre (ds ++ post) b
      (by simpa only [List.cons_append, List.append_assoc, List.nil_append] using h)
    have h := hTrans h₀ (by simpa only [pre', List.append_assoc] using h₁)
    rw [ascendingExpand_cons_eq b ds]
    simpa only [pre', List.append_assoc, List.cons_append, List.nil_append] using h

/-- The ascending character presentations of both Levi lists give a compact-section-compatible
continuous quotient of the ambient genuine smooth standard module. -/
def RealAscendingParabolicQuotientStatement : Prop :=
  ∀ (m p : ℕ) (d₁ d₂ : List RealBlock), realRank d₁ = m + 1 → realRank d₂ = p + 1 →
    SmoothParabolicQuotient m p (ascendingExpand d₁) (ascendingExpand d₂) d₁ d₂

set_option maxHeartbeats 450000 in
theorem realAscendingParabolicQuotient : RealAscendingParabolicQuotientStatement := by
  intro m p d₁ d₂ hm hp
  have hp' := (realRank_ascendingExpand d₂).trans hp
  have h₁ : SmoothParabolicQuotient m p (ascendingExpand d₁) (ascendingExpand d₂) d₁ (ascendingExpand d₂) := by
    let R (x y : List RealBlock) := SmoothParabolicQuotient m p x (ascendingExpand d₂) y (ascendingExpand d₂)
    have h := ascendingExpand_rel m R (fun _ h => SmoothParabolicQuotient.refl h hp')
      (fun h h' => h.trans h') (fun pre post b h => ascendingSingleton_first m p (ascendingExpand d₂) pre post b h hp')
    simpa only [R, List.nil_append, List.append_nil] using h d₁ [] [] (by simpa using hm)
  have h₂ : SmoothParabolicQuotient m p d₁ (ascendingExpand d₂) d₁ d₂ := by
    let R (x y : List RealBlock) := SmoothParabolicQuotient m p d₁ x d₁ y
    have h := ascendingExpand_rel p R (fun _ h => SmoothParabolicQuotient.refl hm h)
      (fun h h' => h.trans h') (fun pre post b h => ascendingSingleton_second m p d₁ pre post b hm h)
    simpa only [R, List.nil_append, List.append_nil] using h d₂ [] [] (by simpa using hp)
  exact h₁.trans h₂

/-- A nonzero Whittaker evaluation is detected by some compact transverse section
with two smooth Levi inputs. -/
def HasParabolicTraceDetection (m p : ℕ) (d₁ d₂ : List RealBlock) : Prop :=
  ∀ (hm : realRank d₁ = m + 1) (hp : realRank d₂ = p + 1) (a : ℝˣ)
    (L : D (p + 1 + m + 1) (d₂ ++ d₁) →L[ℂ] ℂ),
    IsSmoothWhittakerEvaluation (r := p + 1 + m) (d₂ ++ d₁) a L → L ≠ 0 →
    ∃ (f : S (m + 1) d₁) (g : S (p + 1) d₂)
      (φ : 𝓓((⊤ : Opens (Matrix (Fin (m + 1)) (Fin (p + 1)) ℝ)), ℂ)),
      L (smoothSectionVector hm hp f g φ) ≠ 0

set_option maxHeartbeats 650000 in
/-- Detection for character lists implies detection for arbitrary real block lists at the same
ranks, by pulling back the functional through the compact-section-compatible quotient. -/
theorem hasParabolicTraceDetection_of_characters {m p : ℕ} {d₁ d₂ : List RealBlock}
    (hChar : ∀ c₁ c₂ : List RealBlock, IsCharacterList c₁ → IsCharacterList c₂ →
      HasParabolicTraceDetection m p c₁ c₂) : HasParabolicTraceDetection m p d₁ d₂ := by
  intro hm hp a L hL hne
  let c₁ := ascendingExpand d₁
  let c₂ := ascendingExpand d₂
  obtain ⟨hc₁, hc₂, _, _, T, Q₁, Q₂, hT, hSec⟩ := realAscendingParabolicQuotient m p d₁ d₂ hm hp
  have hChar' (d : List RealBlock) : IsCharacterList (ascendingExpand d) := by
    intro b hb
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    exact ⟨c, rfl⟩
  have hL' : IsSmoothWhittakerEvaluation (r := p + 1 + m) (c₂ ++ c₁) a (L.comp T) := by
    intro u v
    change L (T (act (p + 1 + m + 1) (c₂ ++ c₁) u.val v)) = realWhittakerCharacter a u.val * L (T v)
    rw [hT.1]
    exact hL u (T v)
  have hne' : L.comp T ≠ 0 := by
    intro hZero
    apply hne
    apply ContinuousLinearMap.ext
    have he := (denseRange_compactFiniteEquiv (r := p + 1 + m) (d₂ ++ d₁)).equalizer
      L.continuous (ContinuousLinearMap.continuous (0 : D (p + 1 + m + 1) (d₂ ++ d₁) →L[ℂ] ℂ))
      (funext fun f => by
        obtain ⟨f', hf'⟩ := hT.2 f
        change L (compactFiniteEquiv (d₂ ++ d₁) f).val = 0
        rw [← hf', ← ContinuousLinearMap.comp_apply, hZero]
        rfl)
    exact congrFun he
  obtain ⟨f, g, φ, hv⟩ := hChar c₁ c₂ (hChar' d₁) (hChar' d₂) hc₁ hc₂ a (L.comp T) hL' hne'
  refine ⟨(derivativeEquiv d₁).symm (Q₁ (derivativeEquiv c₁ f)),
    (derivativeEquiv d₂).symm (Q₂ (derivativeEquiv c₂ g)), φ, ?_⟩
  rw [← hSec]
  exact hv

end Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection
