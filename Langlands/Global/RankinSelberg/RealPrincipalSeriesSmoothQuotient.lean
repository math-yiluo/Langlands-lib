import Langlands.Global.RankinSelberg.RealPrincipalSeriesQuotient
import Langlands.Global.RankinSelberg.RealBlockSmoothExtension
import Langlands.Representation.Archimedean.SmoothRealGroupIntertwining

/-! # Continuous ascending quotients of the real smooth standard models -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach

open DerivativeSmoothVectors RealPrincipalSeries

attribute [local instance 100] LieRing.ofAssociativeRing

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

/-- A continuous equivariant map on the genuine smooth models that is
surjective on the original compact-finite vectors. -/
def SmoothStandardQuotient (r : ℕ) (ds es : List RealBlock) : Prop :=
  let I := matrixModel ℝ (r + 1)
  let R₁ := representation (n := r + 1) ds
  let R₂ := representation (n := r + 1) es
  ∃ T : DerivativeSmoothVectors I R₁ →L[ℂ] DerivativeSmoothVectors I R₂,
    (∀ g v, T (DerivativeSmoothVectors.representation I R₁ g v) =
      DerivativeSmoothVectors.representation I R₂ g (T v)) ∧
    ∀ f : Automorphic.realStandardKFinite (r + 1) es,
      ∃ f' : Automorphic.realStandardKFinite (r + 1) ds,
        T (compactFiniteEquiv ds f').val = (compactFiniteEquiv es f).val

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "U" => Matrix.unitaryGroup (Fin (r + 1)) ℝ
local notation "I" => matrixModel ℝ (r + 1)
local notation:max "S" ds:max => realStandardModule (r + 1) ds
local notation:max "R" ds:max => representation (n := r + 1) ds
local notation:max "D" ds:max => DerivativeSmoothVectors I (R ds)
local notation:max "V" ds:max => Automorphic.realStandardKFinite (r + 1) ds
local notation:max "act" ds:max => DerivativeSmoothVectors.representation I (R ds)
local notation:max "coord" ds:max => derivativeCoordinates I (R ds)
local notation:max "dR" ds:max => operator I (R ds)

namespace SmoothStandardQuotient

protected theorem trans {ds es fs : List RealBlock}
    (h₁ : SmoothStandardQuotient r ds es) (h₂ : SmoothStandardQuotient r es fs) :
    SmoothStandardQuotient r ds fs := by
  obtain ⟨T, hT, hT₀⟩ := h₁
  obtain ⟨L, hL, hL₀⟩ := h₂
  refine ⟨L.comp T, fun g v => ?_, fun f => ?_⟩
  · simp only [ContinuousLinearMap.comp_apply, hT, hL]
  · obtain ⟨q, hq⟩ := hL₀ f
    obtain ⟨p, hp⟩ := hT₀ q
    exact ⟨p, by simp only [ContinuousLinearMap.comp_apply, hp, hq]⟩

protected theorem refl (r : ℕ) (ds : List RealBlock) : SmoothStandardQuotient r ds ds :=
  ⟨ContinuousLinearMap.id ℂ _, fun _ _ => rfl, fun f => ⟨f, rfl⟩⟩

set_option maxHeartbeats 500000 in
/-- Equal underlying standard spaces give a continuous identification of
all compact derivative coordinates and all translates. -/
theorem exists_preserving_function_of_eq {ds es : List RealBlock} (he : S ds = S es) :
    ∃ T : D ds →L[ℂ] D es,
      (∀ g v, T (act ds g v) = act es g (T v)) ∧
      (∀ f : V es, ∃ f' : V ds, T (compactFiniteEquiv ds f').val = (compactFiniteEquiv es f).val) ∧
      ∀ v, ((derivativeEquiv es).symm (T v)).val = ((derivativeEquiv ds).symm v).val := by
  let e := Submodule.inclusion he.le
  let T : D ds →ₗ[ℂ] D es := (derivativeEquiv es).toLinearMap.comp
    (e.comp (derivativeEquiv ds).symm.toLinearMap)
  have hT (f : S ds) : T (derivativeEquiv ds f) = derivativeEquiv es (e f) := by
    simp only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have hTd (X : M) (v : D ds) : T (dR ds X v) = dR es X (T v) := by
    obtain ⟨f, rfl⟩ := (derivativeEquiv ds).surjective v
    rw [← derivativeEquiv_differentiate, hT, hT, ← derivativeEquiv_differentiate]
    congr 1
  have hcoord (Xs : List M) (v : D ds) : (coord es (T v) Xs).val = (coord ds v Xs).val := by
    induction Xs using List.reverseRecOn generalizing v with
    | nil =>
      obtain ⟨f, rfl⟩ := (derivativeEquiv ds).surjective v
      simp only [hT, derivativeCoordinates_apply, iteratedLieDerivative_nil,
        toSmooth_derivativeEquiv, embed_val]
      ext k
      rfl
    | append_singleton Xs X ih =>
      rw [← derivativeCoordinates_operator, ← derivativeCoordinates_operator, ← hTd]
      exact ih (dR ds X v)
  have hc : Continuous T := by
    apply (isEmbedding_derivativeCoordinates I (R es)).isInducing.continuous_iff.mpr
    apply continuous_pi
    intro Xs
    apply continuous_induced_rng.mpr
    change Continuous (fun v => (coord es (T v) Xs).val)
    simp_rw [hcoord]
    exact continuous_subtype_val.comp (derivativeCLM I (R ds) Xs).continuous
  refine ⟨⟨T, hc⟩, fun g v => ?_, fun f => ?_, fun v => ?_⟩
  · obtain ⟨f, rfl⟩ := (derivativeEquiv ds).surjective v
    change T (act ds g (derivativeEquiv ds f)) = act es g (T (derivativeEquiv ds f))
    rw [← derivativeEquiv_translate, hT, hT, ← derivativeEquiv_translate]
    congr 1
  · let f₀ : V ds := ⟨f.val, he.symm ▸ f.property.1, f.property.2⟩
    refine ⟨f₀, ?_⟩
    simp only [compactFiniteEquiv_val]
    change T (derivativeEquiv ds _) = derivativeEquiv es _
    rw [hT]
    rfl
  · change ((derivativeEquiv es).symm (derivativeEquiv es (e ((derivativeEquiv ds).symm v)))).val = _
    rw [LinearEquiv.symm_apply_apply]
    rfl

protected theorem of_eq {ds es : List RealBlock} (he : S ds = S es) :
    SmoothStandardQuotient r ds es := by
  obtain ⟨T, hG, hpre, _⟩ := exists_preserving_function_of_eq he
  exact ⟨T, hG, hpre⟩

end SmoothStandardQuotient

private abbrev highParity (d : ComplexCharacterData) : Fin 2 :=
  RealGammaReflection.positionParity d.weight.natAbs

private abbrev low (d : ComplexCharacterData) : RealCharacterData := RealInducedCharacter.cb d 0
private abbrev high (d : ComplexCharacterData) : RealCharacterData := RealInducedCharacter.ca d (highParity d)

private theorem ascendingExpand_cons_eq (b : RealBlock) (ds : List RealBlock) :
    ascendingExpand (b :: ds) = ascendingExpand [b] ++ ascendingExpand ds := by
  simp only [ascendingExpand, ascendingCharacters, List.flatMap_cons, List.flatMap_nil,
    List.map_append, List.append_nil]

private theorem smoothStandardQuotient_of_tail (pre post : List RealBlock) (d : ComplexCharacterData)
    (hr : realRank (pre ++ [RealBlock.induced d] ++ post) = r + 1) (hw : d.weight ≠ 0) :
    SmoothStandardQuotient r (pre ++ [RealBlock.character (low d), RealBlock.character (high d)] ++ post)
      (pre ++ [RealBlock.induced d] ++ post) := by
  let w := d.weight.natAbs
  have hl : 0 < w := Int.natAbs_pos.mpr hw
  have hp : ((highParity d).val + (0 : Fin 2).val) % 2 = (w + 1) % 2 := by
    change ((RealGammaReflection.positionParity w).val + (0 : Fin 2).val) % 2 = _
    rw [RealGammaReflection.positionParity, Fin.val_add]
    change ((w % 2 + 1) % 2 + 0) % 2 = (w + 1) % 2
    omega
  let h := RealInducedCharacter.data_tail hr hl hp
  have hrec := RealInducedCharacter.isRecurrent_tail (pre := pre) (post := post) hl hp
  let ε := RealCharacterPair.pairParity (low d) (high d)
  let C := ((w + ε.toNat + 1 : ℕ) : ℝ) ^ w
  obtain ⟨T, hT, hLie, hK⟩ := exists_continuous_blockFrobMap h hrec w
    (C := C) (by dsimp [C]; positivity)
    (RealBlockFourierDecay.norm_tailMultiplier_le w ε (by simp))
  refine ⟨T, map_representation_real_of_compact_and_lie _ _
    (isContinuousRepresentation _) (isContinuousRepresentation _) T hLie hK, ?_⟩
  intro f
  obtain ⟨f', hf⟩ := RealInducedCharacter.tail_surjective hr hl hp f
  exact ⟨f', (hT f').trans (congrArg (fun v => (compactFiniteEquiv _ v).val) hf)⟩

private theorem smoothStandardQuotient_ascendingSingleton (pre post : List RealBlock)
    (b : RealBlock) (hr : realRank (pre ++ [b] ++ post) = r + 1) :
    SmoothStandardQuotient r (pre ++ ascendingExpand [b] ++ post) (pre ++ [b] ++ post) := by
  cases b with
  | character c => exact SmoothStandardQuotient.refl r _
  | induced d =>
    have he : ascendingExpand [RealBlock.induced d] =
        (if d.weight = 0 then [RealBlock.character (high d), RealBlock.character (low d)]
          else [RealBlock.character (low d), RealBlock.character (high d)]) := by
      simp only [ascendingExpand, ascendingCharacters, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      change ((if d.weight = 0 then [high d, low d] else [low d, high d]).map RealBlock.character) = _
      split_ifs <;> rfl
    by_cases hw : d.weight = 0
    · have he₀ : ascendingExpand [RealBlock.induced d] = realBlockExpand (.induced d) := by
        have hp : highParity d = (1 : Fin 2) := by
          change RealGammaReflection.positionParity d.weight.natAbs = _
          rw [hw, Int.natAbs_zero]
          rfl
        rw [he]
        simp only [hw, hp, ite_true, realBlockExpand, RealInducedCharacter.ca, RealInducedCharacter.cb,
          RealInducedCharacter.aExp, RealInducedCharacter.bExp, Int.natAbs_zero,
          Nat.cast_zero, zero_div, add_zero, sub_zero]
      rw [he₀]
      apply SmoothStandardQuotient.of_eq
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        (realStandardModule_append_expand (r + 1) pre post (.induced d)).symm
    · rw [he, ite_eq_right hw]
      exact smoothStandardQuotient_of_tail pre post d hr hw

private theorem smoothStandardQuotient_ascendingExpand_aux (r : ℕ) :
    ∀ (ds pre post : List RealBlock), realRank (pre ++ ds ++ post) = r + 1 →
      SmoothStandardQuotient r (pre ++ ascendingExpand ds ++ post) (pre ++ ds ++ post)
  | [], pre, post, _ => SmoothStandardQuotient.refl r _
  | b :: ds, pre, post, hr => by
    let pre' := pre ++ ascendingExpand [b]
    have hr' : realRank (pre' ++ ds ++ post) = r + 1 := by
      simpa only [pre', realRank_append, realRank_ascendingExpand, realRank_cons, realRank_nil,
        add_zero, add_assoc] using hr
    have h₀ := smoothStandardQuotient_ascendingExpand_aux r ds pre' post hr'
    have h₁ := smoothStandardQuotient_ascendingSingleton (r := r) pre (ds ++ post) b
      (by simpa only [List.cons_append, List.append_assoc, List.nil_append] using hr)
    have h := h₀.trans (by simpa only [pre', List.append_assoc] using h₁)
    rw [ascendingExpand_cons_eq b ds]
    simpa only [pre', List.append_assoc, List.cons_append,
      List.nil_append] using h

/-- The ascending character presentation has a continuous full-group
intertwiner onto every compact-finite vector of the original real standard module. -/
theorem smoothStandardQuotient_ascendingExpand (r : ℕ) (ds : List RealBlock)
    (hr : realRank ds = r + 1) : SmoothStandardQuotient r (ascendingExpand ds) ds := by
  simpa using smoothStandardQuotient_ascendingExpand_aux r ds [] [] (by simpa using hr)

/-- A continuous Whittaker evaluation of the original standard module
pulls back to the ascending character presentation, including all coefficients. -/
theorem exists_whittakerEvaluation_ascendingExpand (ds : List RealBlock) (hr : realRank ds = r + 1)
    (a : ℝˣ) (B : V ds →ₗ[ℂ] (G → ℂ)) (L : D ds →L[ℂ] ℂ)
    (hL : IsWhittakerStandardEvaluation ds a B L) :
    ∃ L' : D (ascendingExpand ds) →L[ℂ] ℂ,
      (∀ (u : GeneralLinear.upperUnipotent (r + 1) ℝ) v,
        L' (act (ascendingExpand ds) u.val v) = realWhittakerCharacter a u.val * L' v) ∧
      ∀ f : V ds, ∃ f' : V (ascendingExpand ds), ∀ g,
        L' (act (ascendingExpand ds) g (compactFiniteEquiv _ f').val) = B f g := by
  obtain ⟨T, hT, hpre⟩ := smoothStandardQuotient_ascendingExpand r ds hr
  refine ⟨L.comp T, fun u v => ?_, fun f => ?_⟩
  · change L (T (act (ascendingExpand ds) u.val v)) = realWhittakerCharacter a u.val * L (T v)
    exact (congrArg L (hT u.val v)).trans (hL.2 u (T v))
  · obtain ⟨f', hf'⟩ := hpre f
    refine ⟨f', fun g => ?_⟩
    change L (T (act (ascendingExpand ds) g (compactFiniteEquiv _ f').val)) = B f g
    rw [hT, hf']
    exact hL.1 f g

/-- Every rank-matched real standard module is reached continuously by its
ascending character presentation on the compact-finite vectors. -/
def RealPrincipalSeriesSmoothQuotientStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 →
    SmoothStandardQuotient r (ascendingExpand ds) ds

theorem realPrincipalSeriesSmoothQuotient : RealPrincipalSeriesSmoothQuotientStatement :=
  smoothStandardQuotient_ascendingExpand

end Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
