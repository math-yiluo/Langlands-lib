import Langlands.Representation.Exponents.WeakCriticalTopLayerL2Statement
import Langlands.Representation.Exponents.WeakCriticalTopLayerExponents
import Langlands.Representation.Classification.ProductLeviTemperedExponentNecessityProof
import Langlands.Representation.Classification.ProductLeviSquareIntegrableSufficiencyStatement
import Langlands.Representation.Classification.TemperedOppositeJacquetScalarLayerAssembly

/-!
# Square-integrability of quotients of the maximal layer of a weakly critical exponent

The product-Levi square-integrability criterion implies the published statement
`GLWeaklyCriticalTopLayerL2Statement`. The weak prefix bounds come from the
published upper exponent bound for tempered representations of `GL_n`, read
along the flattened shape through the reversal of block labels. A vanishing proper prefix would give a
unitary exponent along a strictly finer standard pair, extending the critical
exponent, with nilpotence order at least that of the critical exponent.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open scoped BigOperators

universe uF uV uW

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}

/-- A character that is a power of one unit on an initial segment of one outer
block has absolute value the power of the corresponding prefix sum. -/
theorem norm_blockPrefix_character {B : BlockShape n} (D : BlockRefinement B)
    {ψ : (Fin (B.flatten D).length → F.Carrierˣ) →* ℂˣ} {s : Fin (B.flatten D).length → ℝ}
    (hs : T.IsRealPartOf ψ s) (j : Fin B.length) (i : Fin (D j).length) (u : F.Carrierˣ) :
    ‖(ψ (fun k => if B.flattenOuter D k = j ∧ k ≤ B.flattenBlockEquiv D ⟨j, i⟩
        then u else 1) : ℂ)‖ =
      T.normalizedAbs (u : F.Carrier) ^
        (∑ i' ∈ Finset.univ.filter (fun i' : Fin (D j).length => i' ≤ i),
          s (B.flattenBlockEquiv D ⟨j, i'⟩)) := by
  classical
  rw [hs, ← B.sum_filter_flattenOuter_le D s j i, B.flattenOuter_flattenBlockEquiv D,
    Real.rpow_sum_of_pos (T.normalizedAbs_pos u.ne_zero), Finset.prod_filter]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs with h
  · rfl
  · rw [Units.val_one, T.normalizedAbs_one, Real.one_rpow]

/-- If the restriction of `ψ` to the outer block scalars is unitary and the prefix
of block `j` up to `i` vanishes, then `ψ` is unitary on the block scalars of the
shape split after `i` inside block `j`. -/
theorem norm_comp_splitIndex_eq_one {B : BlockShape n} (D : BlockRefinement B)
    {ψ : (Fin (B.flatten D).length → F.Carrierˣ) →* ℂˣ} {s : Fin (B.flatten D).length → ℝ}
    (hs : T.IsRealPartOf ψ s) {χ : (Fin B.length → F.Carrierˣ) →* ℂˣ}
    (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1) (hres : ∀ c, ψ (c ∘ B.flattenOuter D) = χ c)
    (j : Fin B.length) (i : Fin (D j).length)
    (hzero : ∑ i' ∈ Finset.univ.filter (fun i' : Fin (D j).length => i' ≤ i),
      s (B.flattenBlockEquiv D ⟨j, i'⟩) = 0)
    (c : Fin (B.length + 1) → F.Carrierˣ) :
    ‖(ψ (c ∘ B.splitIndex D j i) : ℂ)‖ = 1 := by
  classical
  let j₀ : Fin (B.length + 1) := ⟨j.val, by omega⟩
  let j₁ : Fin (B.length + 1) := ⟨j.val + 1, by omega⟩
  let u : F.Carrierˣ := c j₀ * (c j₁)⁻¹
  let c' : Fin B.length → F.Carrierˣ := fun j' =>
    if j'.val < j.val then c ⟨j'.val, by omega⟩ else c ⟨j'.val + 1, by omega⟩
  have hdec : c ∘ B.splitIndex D j i = (c' ∘ B.flattenOuter D) *
      (fun k => if B.flattenOuter D k = j ∧ k ≤ B.flattenBlockEquiv D ⟨j, i⟩ then u else 1) := by
    funext k
    simp only [Function.comp_apply, Pi.mul_apply]
    by_cases hK : B.splitCut D j i < k
    · have hj : j ≤ B.flattenOuter D k := B.le_flattenOuter_of_lt D j i hK
      have hnl : ¬ (B.flattenOuter D k).val < j.val := not_lt.mpr hj
      have hcond : ¬ (B.flattenOuter D k = j ∧ k ≤ B.flattenBlockEquiv D ⟨j, i⟩) :=
        fun h => absurd h.2 (not_le.mpr hK)
      simp only [hcond, ite_false, mul_one, c', hnl]
      congr 1
      exact Fin.ext (B.splitIndex_val_of_lt D j i hK)
    · have hle : B.flattenOuter D k ≤ j := B.flattenOuter_le_of_not_lt D j i hK
      rcases hle.lt_or_eq with hlt | heq
      · have hcond : ¬ (B.flattenOuter D k = j ∧ k ≤ B.flattenBlockEquiv D ⟨j, i⟩) :=
          fun h => absurd h.1 hlt.ne
        have hlt' : (B.flattenOuter D k).val < j.val := hlt
        simp only [hcond, ite_false, mul_one, c', hlt', ite_true]
        congr 1
        exact Fin.ext (B.splitIndex_val_of_not_lt D j i hK)
      · have hcond : B.flattenOuter D k = j ∧ k ≤ B.flattenBlockEquiv D ⟨j, i⟩ :=
          ⟨heq, not_lt.mp hK⟩
        have hsplit : B.splitIndex D j i k = j₀ :=
          Fin.ext (by rw [B.splitIndex_val_of_not_lt D j i hK, heq])
        have hc' : c' (B.flattenOuter D k) = c j₁ := by
          simp only [c', heq, lt_irrefl, ite_false]
          rfl
        have hb : (if B.flattenOuter D k = j ∧ k ≤ B.flattenBlockEquiv D ⟨j, i⟩ then u else 1) =
            u := by
          simp only [hcond, and_self, ite_true]
        rw [hsplit, hc', hb]
        change c j₀ = c j₁ * (c j₀ * (c j₁)⁻¹)
        rw [mul_comm (c j₀) (c j₁)⁻¹, mul_inv_cancel_left]
  rw [hdec, map_mul, Units.val_mul, norm_mul, hres, hχ, one_mul,
    T.norm_blockPrefix_character D hs j i u, hzero, Real.rpow_zero]

/-- Every opposite Jacquet dual exponent of an irreducible tempered representation
of `GL_n` has norm at most one on block scalars with antitone absolute values.
This is the published upper bound `ScalarLayer.TemperedUpperExponentBound`
(proved from the product-Levi necessity theorem) read through the reversal of the
block labels. -/
theorem norm_le_one_of_isDualJacquetExponent_of_isTempered (hn : 0 < n)
    (C : BlockShape n) (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier))
    (hirr : Representation.IsIrreducible A.ρ) (htemp : T.IsTempered A.ρ)
    {ψ : (Fin C.length → F.Carrierˣ) →* ℂˣ} (hψ : T.IsDualJacquetExponent C A ψ)
    (b : Fin C.length → F.Carrierˣ)
    (hb : Antitone (fun i => T.normalizedAbs (b i : F.Carrier))) :
    ‖(ψ b : ℂ)‖ ≤ 1 := by
  let := T.topology
  have hA : IsAdmissible A.ρ := htemp.isAdmissible
  have hgen := ScalarLayer.isGeneralizedEigencharacter_of_isDualJacquetExponent T C A hirr hA hψ
  have hJexp := ScalarLayer.isJacquetExponent_reverse T C A hψ.1 hgen
  have h := ScalarLayer.temperedUpperExponentBound_of_productLeviNecessity
    glProductLeviTemperedExponentNecessity.{uF, uV} p F T n hn A A.ρ hirr htemp
    C.reverse _ hJexp (b ∘ Fin.rev) (fun i j hij => hb (Fin.rev_le_rev.mpr hij))
  have hb' : (b ∘ Fin.rev) ∘ Fin.rev = b := by
    funext k
    simp
  change ‖(ψ ((b ∘ Fin.rev) ∘ Fin.rev) : ℂ)‖ ≤ 1 at h
  rwa [hb'] at h

end PadicField.TopologicalData

/-- The product-Levi square-integrability criterion implies the published
top-layer criterion `GLWeaklyCriticalTopLayerL2Statement`. -/
theorem glWeaklyCriticalTopLayerL2_of
    (hsuff : GLProductLeviDualOppositeSquareIntegrableSufficiencyStatement.{uF, uW}) :
    GLWeaklyCriticalTopLayerL2Statement.{uF, uV, uW} := by
  intro p _ F T
  let := T.topology
  intro n hn B A hAirr hAtemp χ hcrit d hd hidx a S hSirr hSadm hSscalar q hq
  have hA : IsAdmissible A.ρ := hAtemp.isAdmissible
  have hpull : ∀ C : BlockShape n,
      (Exponents.ConjugateBlockPair.standard (R := F.Carrier) C).pullbackRep A = A := by
    intro C
    change Rep.of (A.ρ.comp (MulAut.conj (1 : GeneralLinear n F.Carrier)).toMonoidHom) =
      Rep.of A.ρ
    congr 1
    ext g v
    change A.ρ (1 * g * 1⁻¹) v = A.ρ g v
    simp
  obtain ⟨⟨-, hχunit⟩, hcritQ⟩ := hcrit
  have key := hsuff p F T n hn B S χ hSirr hSadm hSscalar hχunit
  intro Q mQ bQ μ hμ
  refine @key ?_ mQ bQ μ hμ
  intro D ψ s φ hψopen hφ heig hs j i
  obtain ⟨hres, hne, L, hLgen, hLne⟩ :=
    T.topLayer_flattened_dual hn B A hAirr hA χ a (d - 1) S hSscalar q hq D ψ φ hφ heig
  have hexp : T.IsDualJacquetExponent (B.flatten D) A ψ := ⟨hψopen, hne⟩
  -- Weak prefix bounds from the tempered bound along the flattened shape.
  have hzero : ∀ j', ∑ i' : Fin (D j').length, s (B.flattenBlockEquiv D ⟨j', i'⟩) = 0 := by
    intro j'
    have h := T.sum_fibre_eq_zero_of_unitary B D S.ρ hSscalar hχunit hφ heig hs j'
    rwa [BlockShape.sum_filter_flattenOuter] at h
  have hglob := ScalarLayer.prefix_nonpos_of_antitone_bound T hs
    (T.norm_le_one_of_isDualJacquetExponent_of_isTempered hn (B.flatten D) A hAirr hAtemp hexp)
  have hpre := ScalarLayer.blockPrefix_nonpos_of_global B D s hglob hzero j i
  refine ⟨hpre, fun hproper => lt_of_le_of_ne hpre fun hvan => ?_⟩
  -- A vanishing proper prefix gives a unitary exponent along the split shape.
  let ψ' : (Fin (B.splitShape D j i hproper).length → F.Carrierˣ) →* ℂˣ :=
    ψ.comp (MaximalConeAssembly.precomp (B.splitLabel D j i hproper))
  have hmono := B.splitLabel_monotone D j i hproper
  have hsize := B.splitShape_size_eq_sum_splitLabel D j i hproper
  have hexp' : T.IsDualJacquetExponent (B.splitShape D j i hproper) A ψ' :=
    T.isDualJacquetExponent_coarsen hmono hsize hexp (fun c => rfl)
  have hunit' : ∀ c, ‖(ψ' c : ℂ)‖ = 1 :=
    fun c => T.norm_comp_splitIndex_eq_one D hs hχunit hres j i hvan c
  have ht : ∃ t : F.Carrier, t ≠ 0 ∧ t ≠ 1 := by
    classical
    let : Infinite F.Carrier := Infinite.of_injective
      (algebraMap (Padic p) F.Carrier) (algebraMap (Padic p) F.Carrier).injective
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset F.Carrier)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    exact ⟨t, ht⟩
  have hstrict := B.standard_splitShape_strictlyRefines D j i hproper F.Carrier ht
  have hψ'merge : ∀ c : Fin B.length → F.Carrierˣ,
      ψ' (c ∘ B.splitMergeLabel D j i hproper) = χ c := by
    intro c
    change ψ ((c ∘ B.splitMergeLabel D j i hproper) ∘ B.splitLabel D j i hproper) = χ c
    rw [B.splitMergeLabel_comp_splitLabel D j i hproper c]
    exact hres c
  have hext : (Exponents.ConjugateBlockPair.standard (B.splitShape D j i hproper)).CharacterExtends
      (Exponents.ConjugateBlockPair.standard B) hstrict.1.2 ψ' χ := by
    refine (Exponents.ConjugateBlockPair.characterExtends_iff _ _ _ _ _).mpr ?_
    intro c b hb
    have hb' : b = c ∘ B.splitMergeLabel D j i hproper := by
      apply (Exponents.ConjugateBlockPair.standard
        (R := F.Carrier) (B.splitShape D j i hproper)).scalarMap_injective
      rw [hb]
      simp only [Exponents.ConjugateBlockPair.standard_scalarMap]
      exact (B.splitShape_blockScalar D j i hproper F.Carrier c).symm
    rw [hb']
    exact hψ'merge c
  -- Its nilpotence order is at least `d`.
  have hidx' : (d : ℕ∞) ≤
      T.dualJacquetExponentNilpotenceIndex (B.splitShape D j i hproper) A ψ' := by
    by_contra hlt
    push Not at hlt
    have hd' : ((d - 1 : ℕ) : ℕ∞) + 1 = (d : ℕ∞) := by
      rw [← Nat.cast_succ]
      congr 1
      omega
    rw [← hd', ENat.lt_add_one_iff (ENat.natCast_ne_top _)] at hlt
    rw [T.dualJacquetExponentNilpotenceIndex_le_iff] at hlt
    have hmem := hlt (T.dualJacquetCoarsen_mem_generalized hmono hsize A hLgen)
    rw [mem_commutativeCharacterSpace] at hmem
    have h1 := hmem (a ∘ B.splitMergeLabel D j i hproper)
    rw [hψ'merge a, ← T.dualJacquetCoarsen_defect_pow hmono hsize A,
      B.splitMergeLabel_comp_splitLabel D j i hproper a] at h1
    exact hLne (T.dualJacquetCoarsen_injective hmono hsize A (h1.trans (map_zero _).symm))
  -- Criticality bounds it strictly by `d`.
  have hcrit' := hcritQ (Exponents.ConjugateBlockPair.standard (B.splitShape D j i hproper))
    hstrict ψ'
    (by rw [hpull]; exact ⟨hexp', hunit'⟩) hext
  rw [hpull, hpull] at hcrit'
  change T.dualJacquetExponentNilpotenceIndex (B.splitShape D j i hproper) A ψ' <
    T.dualJacquetExponentNilpotenceIndex B A χ at hcrit'
  rw [hidx] at hcrit'
  exact absurd hcrit' (not_lt.mpr hidx')

end Langlands
