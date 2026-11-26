import Langlands.Global.RankinSelberg.RealLocalEqualGrowthStep
import Langlands.Global.RankinSelberg.RealPrincipalSeriesWhittakerReduction
import Langlands.Representation.Archimedean.RealInducedCharacterMaps

/-! # Uniform real Whittaker models of block lists inside character-list models

See the paired Markdown file.
-/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open scoped NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal RealPrincipalSeries

/-! ### Surjective exact intertwiners -/

/-- A surjective exact intertwiner from the compact-finite standard module of `ds'` onto that
of `ds` puts the uniform Whittaker model of `ds` inside that of `ds'`: every uniform Whittaker
map of `ds`, composed with the intertwiner, is a uniform Whittaker map of `ds'` with the same
range. -/
theorem realUniformWhittakerModel_le_of_intertwiner {r : ℕ} {ds ds' : List RealBlock} (a : ℝˣ)
    (q : Automorphic.realStandardKFinite (r + 1) ds' →ₗ[ℂ]
      Automorphic.realStandardKFinite (r + 1) ds)
    (hq : IsRealIntertwinerModulo (r + 1) ds' ds ⊥ q) (hs : Function.Surjective q) :
    realUniformWhittakerModel r ds a ≤ realUniformWhittakerModel r ds' a := by
  refine iSup_le fun B => iSup_le fun hB => ?_
  have hB' : IsRealUniformWhittakerIntertwiner r ds' a (B ∘ₗ q) := by
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, N, hN⟩ := hB
    refine ⟨⟨fun f => h1 (q f), fun f => h2 (q f), fun f => h3 (q f), ?_, ?_⟩, N,
      fun f => hN (q f)⟩
    · intro k f f' hf'
      obtain ⟨hf, hg, hqk⟩ := hq.1 k f
      have hf'eq : f' = ⟨_, hf⟩ := Subtype.ext hf'
      have hq' : q ⟨_, hf⟩ = ⟨_, hg⟩ := by
        rw [Submodule.mem_bot, sub_eq_zero] at hqk
        exact hqk
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hf'eq, hq']
      exact h4 k (q f) ⟨_, hg⟩ rfl
    · intro X f f' hf'
      obtain ⟨hf, hg, hqX⟩ := hq.2 X f
      have hf'eq : f' = ⟨_, hf⟩ := Subtype.ext hf'
      have hq' : q ⟨_, hf⟩ = ⟨_, hg⟩ := by
        rw [Submodule.mem_bot, sub_eq_zero] at hqX
        exact hqX
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hf'eq, hq']
      exact h5 X (q f) ⟨_, hg⟩ rfl
  have hrange : LinearMap.range B = LinearMap.range (B ∘ₗ q) := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hs, Submodule.map_top]
  rw [hrange]
  exact le_iSup_of_le (B ∘ₗ q) (le_iSup_of_le hB' le_rfl)

/-! ### Counting induced blocks of nonzero weight -/

/-- The number of induced blocks of nonzero weight in a real block list. -/
def nonzeroInducedCount : List RealBlock → ℕ
  | [] => 0
  | .character _ :: ds => nonzeroInducedCount ds
  | .induced d :: ds => (if d.weight = 0 then 0 else 1) + nonzeroInducedCount ds

theorem nonzeroInducedCount_append (ds es : List RealBlock) :
    nonzeroInducedCount (ds ++ es) = nonzeroInducedCount ds + nonzeroInducedCount es := by
  induction ds with
  | nil => simp [nonzeroInducedCount]
  | cons d ds ih =>
    cases d with
    | character c => simp only [List.cons_append, nonzeroInducedCount, ih]
    | induced e => simp only [List.cons_append, nonzeroInducedCount, ih]; omega

/-- Without induced blocks of nonzero weight, every induced block has weight zero. -/
theorem weight_eq_zero_of_nonzeroInducedCount_eq_zero :
    ∀ {ds : List RealBlock}, nonzeroInducedCount ds = 0 →
      ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt ds p = some d → d.weight = 0
  | [], _, _, _, h => by simp [realInducedBlockAt] at h
  | .character _ :: _, _, 0, _, h => by simp [realInducedBlockAt] at h
  | .character _ :: ds, hc, p + 1, d, h => by
    simp only [realInducedBlockAt] at h
    exact weight_eq_zero_of_nonzeroInducedCount_eq_zero (ds := ds) hc p d h
  | .induced e :: _, hc, 0, d, h => by
    simp only [realInducedBlockAt, Option.some.injEq] at h
    subst h
    simp only [nonzeroInducedCount] at hc
    by_contra hw
    simp [hw] at hc
  | .induced _ :: _, _, 1, _, h => by simp [realInducedBlockAt] at h
  | .induced e :: ds, hc, p + 2, d, h => by
    simp only [realInducedBlockAt] at h
    simp only [nonzeroInducedCount] at hc
    exact weight_eq_zero_of_nonzeroInducedCount_eq_zero (ds := ds) (by omega) p d h

/-- A block list with an induced block of nonzero weight splits around such a block. -/
theorem exists_split_of_nonzeroInducedCount_ne_zero :
    ∀ {ds : List RealBlock}, nonzeroInducedCount ds ≠ 0 →
      ∃ (pre post : List RealBlock) (d : ComplexCharacterData),
        ds = pre ++ [RealBlock.induced d] ++ post ∧ d.weight ≠ 0
  | [], h => absurd rfl h
  | .character c :: ds, h => by
    obtain ⟨pre, post, d, rfl, hd⟩ :=
      exists_split_of_nonzeroInducedCount_ne_zero (ds := ds) (by simpa [nonzeroInducedCount] using h)
    exact ⟨.character c :: pre, post, d, rfl, hd⟩
  | .induced e :: ds, h => by
    by_cases he : e.weight = 0
    · obtain ⟨pre, post, d, rfl, hd⟩ :=
        exists_split_of_nonzeroInducedCount_ne_zero (ds := ds)
          (by simpa [nonzeroInducedCount, he] using h)
      exact ⟨.induced e :: pre, post, d, rfl, hd⟩
    · exact ⟨[], ds, e, rfl, he⟩

/-! ### Expansion of the split lists -/

theorem expand_append' (ds es : List RealBlock) : expand (ds ++ es) = expand ds ++ expand es :=
  List.flatMap_append ..

theorem expand_induced_single (d : ComplexCharacterData) :
    expand [RealBlock.induced d] =
      [RealBlock.character (RealInducedCharacter.ca d
          (RealGammaReflection.positionParity d.weight.natAbs)),
        RealBlock.character (RealInducedCharacter.cb d 0)] :=
  rfl

theorem expand_character_pair (c c' : RealCharacterData) :
    expand [RealBlock.character c, RealBlock.character c'] =
      [RealBlock.character c, RealBlock.character c'] :=
  rfl

theorem positionParity_val (k : ℕ) : (RealGammaReflection.positionParity k).val = (k + 1) % 2 := by
  rw [RealGammaReflection.positionParity, Fin.val_add]
  change (k % 2 + 1) % 2 = (k + 1) % 2
  omega

/-! ### The inclusion -/

variable (r : ℕ) in
/-- The uniform Whittaker model of a block list lies in the uniform Whittaker model of a list
of real characters of the same rank which is a permutation of the expanded list. -/
def RealUniformCharacterListInclusionStatement : Prop :=
  ∀ (ds : List RealBlock), realRank ds = r + 1 → ∀ (a : ℝˣ),
    ∃ L : List RealBlock, IsRealCharacterList L ∧ L.Perm (expand ds) ∧ realRank L = r + 1 ∧
      realUniformWhittakerModel r ds a ≤ realUniformWhittakerModel r L a

theorem exists_characterList_model_le (r : ℕ) (a : ℝˣ) :
    ∀ (k : ℕ) (ds : List RealBlock), nonzeroInducedCount ds = k → realRank ds = r + 1 →
      ∃ L : List RealBlock, IsRealCharacterList L ∧ L.Perm (expand ds) ∧ realRank L = r + 1 ∧
        realUniformWhittakerModel r ds a ≤ realUniformWhittakerModel r L a := by
  intro k
  induction k with
  | zero =>
    intro ds hc hr
    refine ⟨expand ds, isRealCharacterList_expand ds, List.Perm.refl _,
      by rw [realRank_expand, hr], ?_⟩
    rw [realUniformWhittakerModel_expand_of_zero_weights r ds a
      (weight_eq_zero_of_nonzeroInducedCount_eq_zero hc)]
  | succ k ih =>
    intro ds hc hr
    obtain ⟨pre, post, d, rfl, hd⟩ :=
      exists_split_of_nonzeroInducedCount_ne_zero (ds := ds) (by rw [hc]; omega)
    have hl : 0 < d.weight.natAbs := Int.natAbs_pos.mpr hd
    have hs : ((RealGammaReflection.positionParity d.weight.natAbs).val + (0 : Fin 2).val) % 2 =
        (d.weight.natAbs + 1) % 2 := by
      rw [positionParity_val, Fin.val_zero, add_zero, Nat.mod_mod]
    have hr' := RealInducedCharacter.realRank_tail_mid (sb := 0)
      (sa := RealGammaReflection.positionParity d.weight.natAbs) hr
    have hc' : nonzeroInducedCount (pre ++ [RealBlock.character (RealInducedCharacter.cb d 0),
        RealBlock.character (RealInducedCharacter.ca d
          (RealGammaReflection.positionParity d.weight.natAbs))] ++ post) = k := by
      rw [nonzeroInducedCount_append, nonzeroInducedCount_append] at hc ⊢
      simp only [nonzeroInducedCount, hd, ite_false] at hc ⊢
      omega
    obtain ⟨L, hL, hperm, hrank, hle⟩ := ih _ hc' hr'
    refine ⟨L, hL, hperm.trans ?_, hrank, le_trans ?_ hle⟩
    · rw [expand_append', expand_append', expand_character_pair, expand_append', expand_append',
        expand_induced_single]
      exact List.Perm.append_right _ (List.Perm.append_left _ (List.Perm.swap _ _ _))
    · exact realUniformWhittakerModel_le_of_intertwiner a
        (RealBlockFrobeniusMap.blockFrobMap (RealInducedCharacter.data_tail hr hl hs))
        (RealInducedCharacter.modulo_tail hr hl hs)
        (RealInducedCharacter.tail_surjective hr hl hs)

theorem realUniformCharacterListInclusion (r : ℕ) : RealUniformCharacterListInclusionStatement r :=
  fun ds hr a => exists_characterList_model_le r a _ ds rfl hr

/-! ### The continuation targets from character-list growth -/

theorem determinant_perm {ds es : List RealBlock} (h : ds.Perm es) (a : ℝˣ) :
    RealJacquet.determinant ds a = RealJacquet.determinant es a :=
  (h.map _).prod_eq

/-- Equal character-list growth at every positive rank gives the positive equal-rank
continuation target. -/
theorem realLocalUniformPositiveEqualContinuation_of_equalCharacterGrowth
    (hG : ∀ r : ℕ, 0 < r → RealLocalEqualCharacterGrowthAtRank r) :
    RealLocalUniformPositiveEqualContinuationStatement := by
  intro r hr ds es hds hes a D W W' Φ hW hW'
  obtain ⟨L, hL, hLp, hLr, hLle⟩ := realUniformCharacterListInclusion r ds hds a
  obtain ⟨L', hL', hL'p, hL'r, hL'le⟩ := realUniformCharacterListInclusion r es hes (-a)
  have hE := (hG r hr L L' hL hL' hLr hL'r a D W W' Φ (hLle hW) (hL'le hW')).equalContinuation
  unfold EqualContinuation at hE
  rw [determinant_perm hLp, determinant_expand, realPairLFactor_perm hLp hL'p,
    realPairLFactor_perm (hLp.map _) (hL'p.map _)] at hE
  simp only [realPairEpsilon_perm hLp hL'p] at hE
  exact continuationPackage_of_expand ds es (-a) _ _ hE

/-- Unequal character-list growth at every pair of ranks gives the unequal-rank continuation
target. -/
theorem realLocalUniformUnequalContinuation_of_unequalCharacterGrowth
    (hG : ∀ (r t : ℕ) (h : t < r), RealLocalUnequalCharacterGrowthAtRanks r t h) :
    RealLocalUniformUnequalContinuationStatement := by
  intro r t h ds es hds hes a D W W' hW hW'
  obtain ⟨L, hL, hLp, hLr, hLle⟩ := realUniformCharacterListInclusion r ds hds a
  obtain ⟨L', hL', hL'p, hL'r, hL'le⟩ := realUniformCharacterListInclusion t es hes (-a)
  have hU := (hG r t h L L' hL hL' hLr hL'r a D W W' (hLle hW) (hL'le hW')).unequalContinuation
  unfold UnequalContinuation at hU
  rw [determinant_perm hLp, determinant_perm hL'p, determinant_expand, determinant_expand,
    realPairLFactor_perm hLp hL'p, realPairLFactor_perm (hLp.map _) (hL'p.map _)] at hU
  simp only [realPairEpsilon_perm hLp hL'p] at hU
  exact continuationPackage_of_expand ds es (-a) _ _ hU

end Langlands.Global.RankinSelbergGlobal.RealJacquet

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

/-- The positive equal-rank continuation target follows from the canonical range and canonical
evaluation premises, the matrix premise at every rank and adjacent character growth at every
rank. The principal-series inclusion premise of
`RealLocalUniformPositiveEqualContinuationPremisesStatement` is removed. -/
def RealLocalUniformPositiveEqualContinuationPremisesWithoutInclusionStatement : Prop :=
  RealUniformCanonicalRangePremise → RealCanonicalStandardEvaluationPremise →
    (∀ t : ℕ, RealMatrixCoefficientGrowthPremise t) →
    (∀ t : ℕ, RealJacquet.RealLocalAdjacentCharacterGrowthAtRank t) →
    RealLocalUniformPositiveEqualContinuationStatement

theorem realLocalUniformPositiveEqualContinuation_of_premisesWithoutInclusion :
    RealLocalUniformPositiveEqualContinuationPremisesWithoutInclusionStatement := by
  intro hRange hEval hMat hAdj
  refine RealJacquet.realLocalUniformPositiveEqualContinuation_of_equalCharacterGrowth ?_
  intro r hr
  obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
  exact realLocalEqualGrowthStep t hRange hEval (hMat t) (hAdj t)

end Langlands.Global.RankinSelbergGlobal.RealGodement
