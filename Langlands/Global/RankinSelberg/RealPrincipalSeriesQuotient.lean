import Langlands.Global.RankinSelberg.RealPrincipalSeriesWhittakerReduction
import Langlands.Representation.Archimedean.RealInducedCharacterMaps
import Langlands.Representation.Archimedean.RealExponentDeformation
import Langlands.Representation.Archimedean.RealLinkedJacquetPairReduction

/-! # Ascending character quotients for real Rankin–Selberg coefficient spaces -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries

attribute [local instance 100] LieRing.ofAssociativeRing

private def highParity (d : ComplexCharacterData) : Fin 2 :=
  RealGammaReflection.positionParity d.weight.natAbs

private def low (d : ComplexCharacterData) : RealCharacterData :=
  RealInducedCharacter.cb d 0

private def high (d : ComplexCharacterData) : RealCharacterData :=
  RealInducedCharacter.ca d (highParity d)

private def ascendingPositions : RealBlock → List RealCharacterData
  | .character c => [c]
  | .induced d => if d.weight = 0 then [high d, low d] else [low d, high d]

/-- A character list in which nonzero-weight induction blocks are replaced by
their two position characters in ascending order. -/
def ascendingCharacters (ds : List RealBlock) : List RealCharacterData :=
  ds.flatMap ascendingPositions

/-- The ascending character-block presentation. -/
def ascendingExpand (ds : List RealBlock) : List RealBlock :=
  (ascendingCharacters ds).map RealBlock.character

private theorem ascendingExpand_cons (b : RealBlock) (ds : List RealBlock) :
    ascendingExpand (b :: ds) = (ascendingPositions b).map RealBlock.character ++ ascendingExpand ds := by
  simp only [ascendingExpand, ascendingCharacters, List.flatMap_cons, List.map_append]

private theorem ascendingPositions_perm (b : RealBlock) :
    ((ascendingPositions b).map RealBlock.character).Perm (expand [b]) := by
  cases b with
  | character c => exact List.Perm.refl _
  | induced d =>
    change ((if d.weight = 0 then [high d, low d] else [low d, high d]).map
      RealBlock.character).Perm [RealBlock.character (high d), RealBlock.character (low d)]
    split_ifs
    · exact List.Perm.refl _
    · exact List.Perm.swap _ _ _

/-- The ascending list permutes the positions used in the factor calculation. -/
theorem ascendingExpand_perm (ds : List RealBlock) : (ascendingExpand ds).Perm (expand ds) := by
  induction ds with
  | nil => exact List.Perm.refl _
  | cons b ds ih =>
    have he : expand (b :: ds) = expand [b] ++ expand ds := by
      change expand ([b] ++ ds) = expand [b] ++ expand ds
      simp only [expand, List.flatMap_append]
    rw [ascendingExpand_cons, he]
    exact (ascendingPositions_perm b).append ih

@[simp]
theorem realRank_ascendingExpand (ds : List RealBlock) : realRank (ascendingExpand ds) = realRank ds :=
  (realRank_perm (ascendingExpand_perm ds)).trans (realRank_expand ds)

private theorem realRank_ascendingPositions (b : RealBlock) :
    realRank ((ascendingPositions b).map RealBlock.character) = b.rank := by
  rw [realRank_perm (ascendingPositions_perm b), realRank_expand, realRank_cons]
  rfl

private theorem tail_parity_of_positions (d : ComplexCharacterData) :
    ((highParity d).val + (0 : Fin 2).val) % 2 = (d.weight.natAbs + 1) % 2 := by
  rw [highParity, RealGammaReflection.positionParity, Fin.val_add]
  change ((d.weight.natAbs % 2 + 1) % 2 + 0) % 2 = (d.weight.natAbs + 1) % 2
  omega

private theorem surjectiveIntertwiner_ascendingPositions (n : ℕ) (pre post : List RealBlock)
    (b : RealBlock) (hr : realRank (pre ++ b :: post) = n) :
    RealSurjectiveIntertwinerExists n (pre ++ (ascendingPositions b).map RealBlock.character ++ post)
      (pre ++ b :: post) := by
  cases b with
  | character c =>
    simpa [ascendingPositions] using
      (RealSurjectiveIntertwinerExists.refl n (pre ++ RealBlock.character c :: post))
  | induced d =>
    by_cases hw : d.weight = 0
    · have he : (ascendingPositions (.induced d)).map RealBlock.character =
          realBlockExpand (.induced d) := by
        simp only [ascendingPositions, realBlockExpand, hw, ite_true, List.map_cons, List.map_nil,
          high, low, RealInducedCharacter.ca, RealInducedCharacter.cb,
          RealInducedCharacter.aExp, RealInducedCharacter.bExp, highParity, Int.natAbs_zero,
          Nat.cast_zero, zero_div, add_zero, sub_zero]
        rfl
      rw [he]
      exact RealSurjectiveIntertwinerExists.of_eq
        (realStandardModule_append_expand n pre post (.induced d)).symm
    · simp only [ascendingPositions, hw, ite_false, List.map_cons, List.map_nil]
      have hr' : realRank (pre ++ [RealBlock.induced d] ++ post) = n := by simpa using hr
      have hp := tail_parity_of_positions d
      have hl := Int.natAbs_pos.mpr hw
      have h : RealSurjectiveIntertwinerExists n
          (pre ++ [RealBlock.character (RealInducedCharacter.cb d 0),
            RealBlock.character (RealInducedCharacter.ca d (highParity d))] ++ post)
          (pre ++ [RealBlock.induced d] ++ post) :=
        ⟨_, RealInducedCharacter.tail_surjective hr' hl hp,
          RealExponentDeformation.isRealStandardIntertwiner_of_modulo_bot
            (RealInducedCharacter.modulo_tail hr' hl hp)⟩
      simpa only [low, high, List.append_assoc, List.cons_append, List.nil_append] using h

private theorem surjectiveIntertwiner_ascendingExpand_aux (n : ℕ) :
    ∀ (ds pre post : List RealBlock), realRank (pre ++ ds ++ post) = n →
      RealSurjectiveIntertwinerExists n (pre ++ ascendingExpand ds ++ post) (pre ++ ds ++ post)
  | [], pre, post, _ => by
    simpa [ascendingExpand, ascendingCharacters] using
      (RealSurjectiveIntertwinerExists.refl n (pre ++ post))
  | b :: ds, pre, post, hr => by
    let pre' := pre ++ (ascendingPositions b).map RealBlock.character
    have hr' : realRank (pre' ++ ds ++ post) = n := by
      simpa only [pre', realRank_append, realRank_ascendingPositions, realRank_cons, add_assoc] using hr
    have h₀ := surjectiveIntertwiner_ascendingExpand_aux n ds pre' post hr'
    have h₁ := surjectiveIntertwiner_ascendingPositions n pre (ds ++ post) b
      (by simpa only [List.cons_append, List.append_assoc] using hr)
    have h := h₀.trans (by simpa only [pre', List.append_assoc] using h₁)
    simpa only [pre', ascendingExpand_cons, List.append_assoc, List.cons_append] using h

/-- The full ascending character principal series surjects onto the original
compact-finite real standard module. -/
theorem surjectiveIntertwiner_ascendingExpand (n : ℕ) (ds : List RealBlock)
    (hr : realRank ds = n) : RealSurjectiveIntertwinerExists n (ascendingExpand ds) ds := by
  simpa using surjectiveIntertwiner_ascendingExpand_aux n ds [] [] (by simpa using hr)

private theorem isUniform_pullback {r : ℕ} {ds es : List RealBlock} {a : ℝˣ}
    {T : Automorphic.realStandardKFinite (r + 1) es →ₗ[ℂ]
      Automorphic.realStandardKFinite (r + 1) ds}
    (hT : IsRealStandardIntertwiner (r + 1) (realStandardRep (r + 1) ds)
      (realStandardLie (r + 1) ds) es T)
    {B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)}
    (hB : IsRealUniformWhittakerIntertwiner r ds a B) :
    IsRealUniformWhittakerIntertwiner r es a (B.comp T) := by
  obtain ⟨⟨hN, hSmooth, hGrowth, hK, hLie⟩, N, hBound⟩ := hB
  refine ⟨⟨fun f => hN (T f), fun f => hSmooth (T f), fun f => hGrowth (T f), ?_, ?_⟩,
    N, fun f => hBound (T f)⟩
  · intro k f f' hf'
    let k₀ : Matrix.unitaryGroup (Fin (r + 1)) ℝ := ⟨k.val.val, k.property⟩
    have hk₀ : Unitary.toUnits k₀ = k.val := Units.ext rfl
    obtain ⟨hf, hF⟩ := hT.1 k f
    have he : f' = ⟨_, hf⟩ := Subtype.ext hf'
    change B (T f') = Whittaker.rightTranslation ℂ _ k.val (B (T f))
    rw [he, hF]
    exact hK k (T f) (realStandardRep (r + 1) ds k₀ (T f))
      ((realStandardRep_apply_coe _ ds k₀ (T f)).trans (by rw [hk₀]))
  · intro X f f' hf'
    obtain ⟨hf, hF⟩ := hT.2 X f
    have he : f' = ⟨_, hf⟩ := Subtype.ext hf'
    change B (T f') = rightDerivative (matrixModel ℝ (r + 1)) X (B (T f))
    rw [he, hF]
    exact hLie X (T f) _ (realStandardLie_one_tmul_apply_coe _ ds X (T f))

/-- Uniform Whittaker coefficients pull back along the ascending surjection,
preserving their values and the common height exponent. -/
theorem uniformModel_le_ascendingExpand (r : ℕ) (ds : List RealBlock)
    (hr : realRank ds = r + 1) (a : ℝˣ) :
    realUniformWhittakerModel r ds a ≤ realUniformWhittakerModel r (ascendingExpand ds) a := by
  obtain ⟨T, hsurj, hT⟩ := surjectiveIntertwiner_ascendingExpand (r + 1) ds hr
  refine iSup_le fun B => iSup_le fun hB => ?_
  exact le_iSup_of_le (B.comp T) (le_iSup_of_le (isUniform_pullback hT hB) (by
    rintro _ ⟨f, rfl⟩
    obtain ⟨g, rfl⟩ := hsurj f
    exact ⟨g, rfl⟩))

/-- The ascending principal-series presentation preserves both the algebraic
standard module quotient and the inclusion of uniform coefficient spaces. -/
def RealPrincipalSeriesQuotientStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 →
    RealSurjectiveIntertwinerExists (r + 1) (ascendingExpand ds) ds ∧
    ∀ a, realUniformWhittakerModel r ds a ≤ realUniformWhittakerModel r (ascendingExpand ds) a

theorem realPrincipalSeriesQuotient : RealPrincipalSeriesQuotientStatement :=
  fun r ds hr => ⟨surjectiveIntertwiner_ascendingExpand _ ds hr,
    uniformModel_le_ascendingExpand r ds hr⟩

end Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries
