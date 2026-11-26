import Langlands.Global.RankinSelberg.RealPrincipalSeriesWhittakerReduction
import Langlands.Global.RankinSelberg.RealCompactDifferences
import Langlands.Global.RankinSelberg.RealAscendingTailPolynomial
import Langlands.Global.RankinSelberg.RealOrdinaryGenerationPermutation
import Langlands.Global.RankinSelberg.RealWhittakerFiniteKernel
import Langlands.Global.RankinSelberg.RealWhittakerPolynomialKernel
import Langlands.Representation.Archimedean.RealInducedCharacterMaps
import Langlands.Representation.Archimedean.RealBlockFourierSupNorm
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

open RealCompactProbeBounds (CompactBound)
open RealCompactDifferences (CompactDifferenceBound iteratedDifference)

local notation "V" => Automorphic.realStandardKFinite
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℝ

/-- A standard quotient with a compact-equivariant linear section bounded on compact values. -/
def CompactlySplitStandardQuotient (n : ℕ) (ds es : List RealBlock) : Prop :=
  ∃ (T : V n ds →ₗ[ℂ] V n es) (J : V n es →ₗ[ℂ] V n ds),
    IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T ∧
    Function.LeftInverse T J ∧
    (∀ (k : K n) f, J (realStandardRep n es k f) = realStandardRep n ds k (J f)) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : V n es) (R : ℝ),
      CompactBound f R → CompactBound (J f) (C * R)

namespace CompactlySplitStandardQuotient

protected theorem surjective {n : ℕ} {ds es : List RealBlock}
    (h : CompactlySplitStandardQuotient n ds es) : RealSurjectiveIntertwinerExists n ds es := by
  obtain ⟨T, J, hT, hTJ, _, _⟩ := h
  exact ⟨T, hTJ.surjective, hT⟩

protected theorem refl (n : ℕ) (ds : List RealBlock) : CompactlySplitStandardQuotient n ds ds :=
  ⟨LinearMap.id, LinearMap.id, isRealStandardIntertwiner_id n ds, fun _ => rfl, fun _ _ => rfl,
    1, zero_le_one, fun f R h => by simpa only [LinearMap.id_apply, one_mul] using h⟩

protected theorem trans {n : ℕ} {ds es fs : List RealBlock}
    (h₁ : CompactlySplitStandardQuotient n ds es) (h₂ : CompactlySplitStandardQuotient n es fs) :
    CompactlySplitStandardQuotient n ds fs := by
  obtain ⟨T₁, J₁, hT₁, hTJ₁, hJ₁, C₁, hC₁, hB₁⟩ := h₁
  obtain ⟨T₂, J₂, hT₂, hTJ₂, hJ₂, C₂, hC₂, hB₂⟩ := h₂
  refine ⟨T₂.comp T₁, J₁.comp J₂, hT₁.comp_standard hT₂, ?_, ?_,
    C₁ * C₂, mul_nonneg hC₁ hC₂, fun f R h => ?_⟩
  · intro f
    simp only [LinearMap.comp_apply, hTJ₁ _, hTJ₂ _]
  · intro k f
    simp only [LinearMap.comp_apply, hJ₂, hJ₁]
  · simpa only [LinearMap.comp_apply, mul_assoc] using hB₁ (J₂ f) _ (hB₂ f R h)

/-- The identity on functions gives the section for equal standard modules. -/
protected theorem of_eq {n : ℕ} {ds es : List RealBlock}
    (h : realStandardModule n ds = realStandardModule n es) :
    CompactlySplitStandardQuotient n ds es := by
  have hK : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) =
      kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n) := by rw [h]
  obtain ⟨e, he⟩ := exists_linearEquiv_coe_eq hK
  have he' (f : V n es) : (e.symm f).val = f.val := by
    obtain ⟨v, rfl⟩ := e.surjective f
    rw [LinearEquiv.symm_apply_apply, he]
  refine ⟨e.toLinearMap, e.symm.toLinearMap, ⟨?_, ?_⟩, e.apply_symm_apply, ?_,
    1, zero_le_one, fun f R hf k => ?_⟩
  · intro k f
    refine ⟨rightTranslation_mem_kFiniteFunctions_realStandardModule n ds f.2 k.2, ?_⟩
    apply Subtype.ext
    rw [LinearEquiv.coe_coe, he, realStandardRep_apply_coe, he]
    have hk : Unitary.toUnits (⟨k.val.val, k.2⟩ : K n) = k.val := Units.ext rfl
    rw [hk]
  · intro X f
    refine ⟨rightDerivative_mem_kFiniteFunctions_realStandardModule n ds f.2 X, ?_⟩
    apply Subtype.ext
    rw [LinearEquiv.coe_coe, he, realStandardLie_one_tmul_apply_coe, he]
  · intro k f
    apply Subtype.ext
    rw [LinearEquiv.coe_coe, he', realStandardRep_apply_coe, realStandardRep_apply_coe, he']
  · change ‖(e.symm f).val (Unitary.toUnits k)‖ ≤ 1 * R
    rw [he', one_mul]
    exact hf k

end CompactlySplitStandardQuotient

private theorem ascendingPositions_weight_zero (d : ComplexCharacterData) (hw : d.weight = 0) :
    (ascendingPositions (.induced d)).map RealBlock.character = realBlockExpand (.induced d) := by
  simp only [ascendingPositions, realBlockExpand, hw, ite_true, List.map_cons, List.map_nil,
    high, low, RealInducedCharacter.ca, RealInducedCharacter.cb,
    RealInducedCharacter.aExp, RealInducedCharacter.bExp, highParity, Int.natAbs_zero,
    Nat.cast_zero, zero_div, add_zero, sub_zero]
  rfl

private theorem compactlySplitStandardQuotient_ascendingPositions (n : ℕ) (pre post : List RealBlock)
    (b : RealBlock) (hr : realRank (pre ++ b :: post) = n) :
    CompactlySplitStandardQuotient n (pre ++ (ascendingPositions b).map RealBlock.character ++ post)
      (pre ++ b :: post) := by
  cases b with
  | character c =>
    simpa [ascendingPositions] using
      (CompactlySplitStandardQuotient.refl n (pre ++ RealBlock.character c :: post))
  | induced d =>
    by_cases hw : d.weight = 0
    · rw [ascendingPositions_weight_zero d hw]
      exact CompactlySplitStandardQuotient.of_eq
        (realStandardModule_append_expand n pre post (.induced d)).symm
    · simp only [ascendingPositions, hw, ite_false, List.map_cons, List.map_nil]
      have hr' : realRank (pre ++ [RealBlock.induced d] ++ post) = n := by simpa using hr
      have hp := tail_parity_of_positions d
      have hl := Int.natAbs_pos.mpr hw
      let J := RealBlockFrobeniusMap.blockFrobMap (RealInducedCharacter.data_tailInv hr' hl hp)
      let μ (j : ℤ) := (RealBlockMultiplier.tailMultiplier d.weight.natAbs
        (RealCharacterPair.pairParity (low d) (high d)) ((-1) ^ (highParity d).val) j)⁻¹
      have hμ : Summable fun j => ‖μ j‖ ^ 2 :=
        RealBlockFourierSupNorm.summable_sq_inv_tailMultiplier hl _ (by simp)
      have h : CompactlySplitStandardQuotient n
          (pre ++ [RealBlock.character (RealInducedCharacter.cb d 0),
            RealBlock.character (RealInducedCharacter.ca d (highParity d))] ++ post)
          (pre ++ [RealBlock.induced d] ++ post) := by
        refine ⟨_, J, RealExponentDeformation.isRealStandardIntertwiner_of_modulo_bot
          (RealInducedCharacter.modulo_tail hr' hl hp), RealInducedCharacter.tail_tailInv hr' hl hp,
          RealBlockFrobeniusMap.blockFrobMap_rightTranslation _, Real.sqrt (∑' j, ‖μ j‖ ^ 2),
          Real.sqrt_nonneg _, fun f R hf k => ?_⟩
        apply RealBlockFourierSupNorm.norm_blockFrobMap_le
          (RealInducedCharacter.data_tailInv hr' hl hp) hμ f k.2
        intro g hg
        let u : K n := ⟨g.val, hg⟩
        have hu : Unitary.toUnits u = g := Units.ext rfl
        simpa only [hu] using hf u
      simpa only [low, high, List.append_assoc, List.cons_append, List.nil_append] using h

private theorem compactlySplitStandardQuotient_ascendingExpand_aux (n : ℕ) :
    ∀ (ds pre post : List RealBlock), realRank (pre ++ ds ++ post) = n →
      CompactlySplitStandardQuotient n (pre ++ ascendingExpand ds ++ post) (pre ++ ds ++ post)
  | [], pre, post, _ => by
    simpa [ascendingExpand, ascendingCharacters] using
      (CompactlySplitStandardQuotient.refl n (pre ++ post))
  | b :: ds, pre, post, hr => by
    let pre' := pre ++ (ascendingPositions b).map RealBlock.character
    have hr' : realRank (pre' ++ ds ++ post) = n := by
      simpa only [pre', realRank_append, realRank_ascendingPositions, realRank_cons, add_assoc] using hr
    have h₀ := compactlySplitStandardQuotient_ascendingExpand_aux n ds pre' post hr'
    have h₁ := compactlySplitStandardQuotient_ascendingPositions n pre (ds ++ post) b
      (by simpa only [List.cons_append, List.append_assoc] using hr)
    have h := h₀.trans (by simpa only [pre', List.append_assoc] using h₁)
    simpa only [pre', ascendingExpand_cons, List.append_assoc, List.cons_append] using h

/-- The ascending character presentation has a compact-equivariant bounded section on
compact-finite standard vectors. -/
theorem compactlySplitStandardQuotient_ascendingExpand (n : ℕ) (ds : List RealBlock)
    (hr : realRank ds = n) : CompactlySplitStandardQuotient n (ascendingExpand ds) ds := by
  simpa using compactlySplitStandardQuotient_ascendingExpand_aux n ds [] [] (by simpa using hr)

/-- The full ascending character principal series surjects onto the original
compact-finite real standard module. -/
theorem surjectiveIntertwiner_ascendingExpand (n : ℕ) (ds : List RealBlock)
    (hr : realRank ds = n) : RealSurjectiveIntertwinerExists n (ascendingExpand ds) ds :=
  (compactlySplitStandardQuotient_ascendingExpand n ds hr).surjective

/-- A compact-equivariant linear map with a compact value bound has the same bound
at every compact difference order. -/
theorem compactDifferenceBound_of_compactBound {n : ℕ} {ds es : List RealBlock}
    (J : V n es →ₗ[ℂ] V n ds)
    (hJ : ∀ (k : K n) f, J (realStandardRep n es k f) = realStandardRep n ds k (J f))
    {C : ℝ} (hB : ∀ (f : V n es) (R : ℝ), CompactBound f R → CompactBound (J f) (C * R))
    {m : ℕ} {f : V n es} {R : ℝ} (hf : CompactDifferenceBound m f R) :
    CompactDifferenceBound m (J f) (C * R) := by
  have hComm (ks : List (K n)) (v : V n es) :
      J (iteratedDifference ks v) = iteratedDifference ks (J v) := by
    induction ks with
    | nil => rfl
    | cons k ks ih =>
      change J (realStandardRep n es k (iteratedDifference ks v) - iteratedDifference ks v) =
        realStandardRep n ds k (iteratedDifference ks (J v)) - iteratedDifference ks (J v)
      rw [map_sub, hJ, ih]
  intro ks hks
  rw [← hComm, mul_assoc]
  exact hB _ _ (hf ks hks)

private theorem ascendingPositionModel_le (r : ℕ) (pre post : List RealBlock) (b : RealBlock)
    (hr : realRank (pre ++ b :: post) = r + 1) (a : ℝˣ) :
    realWhittakerModel r (pre ++ (ascendingPositions b).map RealBlock.character ++ post) a ≤
      realWhittakerModel r (pre ++ b :: post) a := by
  cases b with
  | character c => simp [ascendingPositions, List.append_assoc]
  | induced d =>
    by_cases hw : d.weight = 0
    · rw [ascendingPositions_weight_zero d hw]
      exact realWhittakerModel_le_of_surjective a
        (RealSurjectiveIntertwinerExists.of_eq (realStandardModule_append_expand (r + 1) pre post (.induced d)))
    · have hr' : realRank (pre ++ [RealBlock.induced d] ++ post) = r + 1 := by simpa using hr
      have hl := Int.natAbs_pos.mpr hw
      have hp := tail_parity_of_positions d
      have hData := RealInducedCharacter.data_tail hr' hl hp
      have hT := RealExponentDeformation.isRealStandardIntertwiner_of_modulo_bot
        (RealInducedCharacter.modulo_tail hr' hl hp)
      have hModel : realWhittakerModel r (pre ++ [.character (low d), .character (high d)] ++ post) a ≤
          realWhittakerModel r (pre ++ [.induced d] ++ post) a := by
        apply RealLocalWhittaker.model_le_of_vanishingKernel a _ (RealInducedCharacter.tail_surjective hr' hl hp) hT
        intro B hB
        exact RealLocalWhittaker.realWhittakerLeftPolynomialVanishing r _ (realRank pre)
          d.weight.natAbs hData.lt _ hT.isGKSubmodule_ker
          (fun f hf g => ascendingTailKernel_polynomial hr' hl hp f hf g) a B hB
      simpa only [ascendingPositions, hw, ite_false, List.map_cons, List.map_nil, List.append_assoc,
        List.cons_append, List.nil_append] using hModel

private theorem ascendingExpandModel_le_aux (r : ℕ) (a : ℝˣ) :
    ∀ (ds pre post : List RealBlock), realRank (pre ++ ds ++ post) = r + 1 →
      realWhittakerModel r (pre ++ ascendingExpand ds ++ post) a ≤
        realWhittakerModel r (pre ++ ds ++ post) a
  | [], pre, post, _ => by simp [ascendingExpand, ascendingCharacters]
  | b :: ds, pre, post, hr => by
    let pre' := pre ++ (ascendingPositions b).map RealBlock.character
    have hr' : realRank (pre' ++ ds ++ post) = r + 1 := by
      simpa only [pre', realRank_append, realRank_ascendingPositions, realRank_cons, add_assoc] using hr
    have h₀ := ascendingExpandModel_le_aux r a ds pre' post hr'
    have h₁ := ascendingPositionModel_le r pre (ds ++ post) b
      (by simpa only [List.cons_append, List.append_assoc] using hr) a
    have h := h₀.trans (by simpa only [pre', List.append_assoc] using h₁)
    simpa only [pre', ascendingExpand_cons, List.append_assoc, List.cons_append] using h

/-- For every rank-correct real block list, its ascending character expansion has exactly
the original Whittaker coefficient space. -/
def RealAscendingWhittakerModelEqualityStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 → ∀ a : ℝˣ,
    realWhittakerModel r (ascendingExpand ds) a = realWhittakerModel r ds a

theorem realAscendingWhittakerModels_eq : RealAscendingWhittakerModelEqualityStatement := by
  intro r ds hr a
  apply le_antisymm
  · simpa using ascendingExpandModel_le_aux r a ds [] [] (by simpa using hr)
  · exact realWhittakerModel_le_of_surjective a (surjectiveIntertwiner_ascendingExpand (r + 1) ds hr)

/-- Precomposition with a standard-module intertwiner preserves an exact Whittaker
coefficient map. -/
theorem isRealWhittakerIntertwiner_pullback {r : ℕ} {ds es : List RealBlock} {a : ℝˣ}
    {T : Automorphic.realStandardKFinite (r + 1) es →ₗ[ℂ]
      Automorphic.realStandardKFinite (r + 1) ds}
    (hT : IsRealStandardIntertwiner (r + 1) (realStandardRep (r + 1) ds)
      (realStandardLie (r + 1) ds) es T)
    {B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)}
    (hB : IsRealWhittakerIntertwiner r ds a B) :
    IsRealWhittakerIntertwiner r es a (B.comp T) := by
  obtain ⟨hN, hSmooth, hGrowth, hK, hLie⟩ := hB
  refine ⟨fun f => hN (T f), fun f => hSmooth (T f), fun f => hGrowth (T f), ?_, ?_⟩
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

private theorem isUniform_pullback {r : ℕ} {ds es : List RealBlock} {a : ℝˣ}
    {T : Automorphic.realStandardKFinite (r + 1) es →ₗ[ℂ]
      Automorphic.realStandardKFinite (r + 1) ds}
    (hT : IsRealStandardIntertwiner (r + 1) (realStandardRep (r + 1) ds)
      (realStandardLie (r + 1) ds) es T)
    {B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)}
    (hB : IsRealUniformWhittakerIntertwiner r ds a B) :
    IsRealUniformWhittakerIntertwiner r es a (B.comp T) := by
  obtain ⟨hExact, N, hBound⟩ := hB
  exact ⟨isRealWhittakerIntertwiner_pullback hT hExact, N, fun f => hBound (T f)⟩

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
