import Langlands.Global.RankinSelberg.RealExactCharacterWhittakerUniqueness
import Langlands.Global.RankinSelberg.RealGodementCanonicalNonzero
import Langlands.Global.RankinSelberg.RealUniformTailInclusion
import Langlands.Representation.Archimedean.RealInducedPairQuotientPresentation

/-! # Exact real Whittaker coefficients of the descending block inclusion -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries

open RealBlockPosition RealBlockFrobeniusMap RealBlockJacquet RealBlockMultiplier
open RealCharacterPair RealCharacterPairReducible RealInducedCharacter
open RealJacquet (expand_append' expand_induced_single positionParity_val)

local notation:max "V[" n "," ds "]" => Automorphic.realStandardKFinite n ds
local notation:max "Coeff[" r "," ds "]" =>
  V[r + 1, ds] →ₗ[ℂ] (Langlands.GeneralLinear (r + 1) ℝ → ℂ)

private theorem positionCharacter_singleExpand (pre post : List RealBlock) (b : RealBlock) :
    realPositionCharacter (pre ++ expand [b] ++ post) =
      realPositionCharacter (pre ++ [b] ++ post) := by
  funext p
  rw [List.append_assoc, List.append_assoc]
  refine realPositionCharacter_append_congr (A := expand [b] ++ post)
    (B := [b] ++ post) ?_ pre p
  intro j
  cases b with
  | character c => rfl
  | induced d =>
    rcases j with _ | _ | j
    · exact funext (realPositionCharacter_expand [.induced d] 0)
    · exact funext (realPositionCharacter_expand [.induced d] 1)
    · rfl

private theorem inducedBlockAt_singleExpand_of_ne (pre post : List RealBlock)
    (d : ComplexCharacterData) {p : ℕ} (hp : p ≠ realRank pre) :
    realInducedBlockAt (pre ++ expand [.induced d] ++ post) p =
      realInducedBlockAt (pre ++ [.induced d] ++ post) p := by
  by_cases h : p < realRank pre ∨ realRank pre + 2 ≤ p
  · exact realInducedBlockAt_of_not_mid (realRank_expand _) (by
      simpa only [realRank_expand, realRank_induced_single] using h)
  · have he : p = realRank pre + 1 := by omega
    subst p
    rw [realInducedBlockAt_mid pre (expand [.induced d]) post (j := 1) (by simp [RealBlock.rank]),
      realInducedBlockAt_mid pre [.induced d] post (j := 1) (by simp [RealBlock.rank])]
    rfl

private theorem realStandardKFinite_le_singleExpand (n : ℕ) (pre post : List RealBlock)
    (b : RealBlock) : V[n, pre ++ [b] ++ post] ≤ V[n, pre ++ expand [b] ++ post] := by
  cases b with
  | character c => exact le_rfl
  | induced d =>
    intro f hf
    refine ⟨(mem_realStandardModule_iff _ _ _).mpr ⟨?_, ?_⟩, hf.2⟩
    · rw [positionCharacter_singleExpand]
      exact hf.1.1
    · intro p e he j hj g
      by_cases hp : p = realRank pre
      · subst p
        rw [← add_zero (realRank pre),
          realInducedBlockAt_mid _ _ _ (j := 0) (by simp [RealBlock.rank])] at he
        cases he
      · exact hf.1.2 p e ((inducedBlockAt_singleExpand_of_ne pre post d hp).symm.trans he) j hj g

private theorem mem_singleBlock_of_lowModes {n : ℕ} {pre post : List RealBlock}
    {d : ComplexCharacterData} (hr : realRank (pre ++ [.induced d] ++ post) = n)
    (f : V[n, pre ++ expand [.induced d] ++ post])
    (hLow : ∀ j : ℤ, |j| < |d.weight| → ∀ k ∈ unitaryCompact ℝ n,
      blockFourierCoefficient n (realRank pre) j f k = 0) :
    f.val ∈ V[n, pre ++ [.induced d] ++ post] := by
  refine ⟨mem_realStandardModule_of_unitaryCompact hr ?_ ?_, f.2.2⟩
  · rw [← positionCharacter_singleExpand]
    exact f.2.1.1
  · intro p e he j hj k hk
    by_cases hp : p = realRank pre
    · rw [hp, ← add_zero (realRank pre),
        realInducedBlockAt_mid _ _ _ (j := 0) (by simp [RealBlock.rank])] at he
      change some d = some e at he
      cases Option.some.inj he
      simpa only [hp] using hLow j hj k hk
    · exact f.2.1.2 p e ((inducedBlockAt_singleExpand_of_ne pre post d hp).trans he) j hj k

/-- Inclusion of compact-finite standard functions restricts exact coefficient maps. -/
theorem isRealWhittakerIntertwiner_restrict {r : ℕ} {ds es : List RealBlock} {a : ℝˣ}
    (h : V[r + 1, ds] ≤ V[r + 1, es]) {B : Coeff[r, es]}
    (hB : IsRealWhittakerIntertwiner r es a B) :
    IsRealWhittakerIntertwiner r ds a (B.comp (Submodule.inclusion h)) :=
  ⟨fun f => hB.1 (Submodule.inclusion h f),
    fun f => hB.2.1 (Submodule.inclusion h f),
    fun f => hB.2.2.1 (Submodule.inclusion h f),
    fun k f f' hf => hB.2.2.2.1 k (Submodule.inclusion h f) (Submodule.inclusion h f') hf,
    fun X f f' hf => hB.2.2.2.2 X (Submodule.inclusion h f) (Submodule.inclusion h f') hf⟩

private theorem restrict_singleBlock_ne_zero {r : ℕ} {pre post : List RealBlock}
    {d : ComplexCharacterData} (hr : realRank (pre ++ [.induced d] ++ post) = r + 1)
    {a : ℝˣ} {B : Coeff[r, pre ++ expand [.induced d] ++ post]}
    (hB : IsRealWhittakerIntertwiner r (pre ++ expand [.induced d] ++ post) a B) (hB₀ : B ≠ 0) :
    B.comp (Submodule.inclusion (realStandardKFinite_le_singleExpand (r + 1) pre post (.induced d)))
      ≠ 0 := by
  intro hZero
  apply hB₀
  have hVan (f : V[r + 1, pre ++ expand [.induced d] ++ post])
      (hf : f.val ∈ V[r + 1, pre ++ [.induced d] ++ post]) : B f = 0 := by
    have h := LinearMap.congr_fun hZero ⟨f.val, hf⟩
    have he : Submodule.inclusion
        (realStandardKFinite_le_singleExpand (r + 1) pre post (.induced d)) ⟨f.val, hf⟩ = f :=
      Subtype.ext rfl
    rw [LinearMap.comp_apply, he, LinearMap.zero_apply] at h
    exact h
  by_cases hw : d.weight = 0
  · apply LinearMap.ext
    intro f
    exact hVan f (mem_singleBlock_of_lowModes hr f fun j hj => by
      rw [hw, abs_zero] at hj
      exact (not_lt_of_ge (abs_nonneg j) hj).elim)
  let sa := RealGammaReflection.positionParity d.weight.natAbs
  let lo := cb d 0
  let hi := ca d sa
  let k := d.weight.natAbs
  have hl : 0 < k := Int.natAbs_pos.mpr hw
  have hsign : (sa.val + (0 : Fin 2).val) % 2 = (k + 1) % 2 := by
    simp [sa, k, positionParity_val]
  have hpar := tail_parity (d := d) hsign
  have hParity := pairParity_eq lo hi
  have hRank : realRank (pre ++ .character lo :: .character hi :: post) = r + 1 := by
    rw [← mid_pair]
    exact realRank_tail_mid hr
  have hUp := data_tail hr hl hsign
  have hData : IsBlockFrobData (r + 1) (pre ++ expand [.induced d] ++ post)
      (pre ++ cd lo hi ++ post) (realRank pre) (pairParity lo hi) (sigma0 lo hi)
      (binomialMultiplier k (pairParity lo hi)) := by
    rw [mid_pair]
    exact data_q0 (ℓ := k) hRank
  have hInv : IsBlockFrobData (r + 1) (pre ++ cd lo hi ++ post)
      (pre ++ expand [.induced d] ++ post) (realRank pre) (pairParity lo hi) (sigma0 lo hi)⁻¹
      (fun j => (binomialMultiplier k (pairParity lo hi) j)⁻¹) := by
    rw [mid_pair]
    exact data_B (ℓ := k) hRank
  have hRec : IsRecurrent
      (GramFormula.realPositionExponent (pre ++ expand [.induced d] ++ post) (realRank pre) -
        GramFormula.realPositionExponent (pre ++ expand [.induced d] ++ post) (realRank pre + 1) + 1)
      (pairParity lo hi) (binomialMultiplier k (pairParity lo hi)) := by
    change IsRecurrent (GramFormula.realPositionExponent (pre ++ dc lo hi ++ post) (realRank pre) -
      GramFormula.realPositionExponent (pre ++ dc lo hi ++ post) (realRank pre + 1) + 1) _ _
    rw [exponent_swp_zero, exponent_swp_one, show hi.exponent - lo.exponent = (k : ℂ) from aExp_sub_bExp d]
    exact isRecurrent_binomialMultiplier hl hParity hpar
  let Q := blockFrobMap hData
  have hQ := RealExponentDeformation.isRealStandardIntertwiner_of_modulo_bot
    (isRealIntertwinerModulo_blockFrobMap hData hRec ⊥)
  have hPoly (f : V[r + 1, pre ++ cd lo hi ++ post]) (hf : f ∈ Q.range)
      (g : Langlands.GeneralLinear (r + 1) ℝ) :
      ∃ q : Polynomial ℂ, q.degree < k ∧ ∀ t : ℝ,
        f.val (lowerRootElement (r + 1) (realRank pre) hData.lt t * g) = q.eval (t : ℂ) := by
    have hRange := RealInducedPairQuotientPresentation.ker_tail_eq_range hl hParity hpar
      (neg_one_pow_sq_fin sa) hData hInv hUp
    have hk : f ∈ LinearMap.ker (blockFrobMap hUp) := hRange.symm ▸ hf
    exact ascendingTailKernel_polynomial hr hl hsign f hk g
  apply RealLocalWhittaker.eq_zero_of_leftPolynomial_range hQ (realRank pre) k hData.lt hPoly hB
  intro f hf
  apply LinearMap.mem_ker.mpr
  apply hVan f
  apply mem_singleBlock_of_lowModes hr f
  intro j hj x hx
  by_cases hJ : Even (j - pairParity lo hi)
  · have hj' : |j| < (k : ℤ) := by simpa only [k, Int.abs_eq_natAbs d.weight] using hj
    have hNonzero := (binomialMultiplier_ne_zero_iff hl hParity hpar hJ).mpr hj'
    have hCoeff := blockFourierCoefficient_blockFrobMap hData f hx j
    rw [show blockFrobMap hData f = 0 from LinearMap.mem_ker.mp hf,
      ZeroMemClass.coe_zero, blockFourierCoefficient_zero] at hCoeff
    exact (mul_eq_zero.mp hCoeff.symm).resolve_left hNonzero
  · exact blockFourierCoefficient_eq_zero_of_not_even hData.lt hData.par f hJ x

private theorem expand_cons_eq (b : RealBlock) (ds : List RealBlock) :
    expand (b :: ds) = expand [b] ++ expand ds := expand_append' [b] ds

private theorem realStandardKFinite_le_expand_middle (n : ℕ) (ds pre post : List RealBlock) :
    V[n, pre ++ ds ++ post] ≤ V[n, pre ++ expand ds ++ post] := by
  induction ds generalizing pre with
  | nil => exact le_rfl
  | cons b ds ih =>
    have hHead := realStandardKFinite_le_singleExpand n pre (ds ++ post) b
    have hTail := ih (pre ++ expand [b])
    simp only [expand_cons_eq b ds, List.append_assoc, List.cons_append]
      at hHead hTail ⊢
    exact hHead.trans hTail

private theorem restrict_single_ne_zero {r : ℕ} {pre post : List RealBlock}
    (b : RealBlock) (hr : realRank (pre ++ [b] ++ post) = r + 1)
    {a : ℝˣ} {B : Coeff[r, pre ++ expand [b] ++ post]}
    (hB : IsRealWhittakerIntertwiner r (pre ++ expand [b] ++ post) a B) (hB₀ : B ≠ 0) :
    B.comp (Submodule.inclusion (realStandardKFinite_le_singleExpand (r + 1) pre post b)) ≠ 0 := by
  cases b with
  | character c => exact hB₀
  | induced d => exact restrict_singleBlock_ne_zero hr hB hB₀

private def RestrictionDetects (r : ℕ) (a : ℝˣ) (ds es : List RealBlock) : Prop :=
  ∀ (h : V[r + 1, ds] ≤ V[r + 1, es]) (B : Coeff[r, es]),
    IsRealWhittakerIntertwiner r es a B → B ≠ 0 →
      B.comp (Submodule.inclusion h) ≠ 0

private theorem restrict_expand_ne_zero_aux (r : ℕ) (a : ℝˣ)
    (ds : List RealBlock) : ∀ (pre post : List RealBlock),
    realRank (pre ++ ds ++ post) = r + 1 →
      RestrictionDetects r a (pre ++ ds ++ post) (pre ++ expand ds ++ post) := by
  induction ds with
  | nil => intro pre post hr h B hB hB₀; exact hB₀
  | cons b ds ih =>
    intro pre post hr
    have hRank : realRank ((pre ++ expand [b]) ++ ds ++ post) = r + 1 := by
      simpa only [realRank_append, realRank_expand, realRank_cons, realRank_nil, add_zero,
        add_assoc] using hr
    have hind := ih (pre ++ expand [b]) post hRank
    have hMid := realStandardKFinite_le_expand_middle (r + 1) ds (pre ++ expand [b]) post
    have hAssoc : (pre ++ expand [b]) ++ ds ++ post = pre ++ expand [b] ++ (ds ++ post) :=
      List.append_assoc _ _ _
    have hExpand : pre ++ expand (b :: ds) ++ post = (pre ++ expand [b]) ++ expand ds ++ post := by
      simp only [expand_cons_eq b ds, List.append_assoc]
    have hSource : pre ++ (b :: ds) ++ post = pre ++ [b] ++ (ds ++ post) := by
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [hAssoc] at hMid hind
    rw [hExpand, hSource]
    intro h B hB hB₀
    have hMidB := isRealWhittakerIntertwiner_restrict hMid hB
    have hMidNe := hind hMid B hB hB₀
    have hRank' : realRank (pre ++ [b] ++ (ds ++ post)) = r + 1 := by rwa [← hSource]
    have hStep := restrict_single_ne_zero (r := r) (pre := pre) (post := ds ++ post)
      (a := a) (B := B.comp (Submodule.inclusion hMid)) b hRank' hMidB hMidNe
    intro hZero
    apply hStep
    have hComp : (B.comp (Submodule.inclusion hMid)).comp
        (Submodule.inclusion (realStandardKFinite_le_singleExpand (r + 1) pre (ds ++ post) b)) =
        B.comp (Submodule.inclusion h) :=
      LinearMap.ext fun f => congrArg B (Subtype.ext rfl)
    exact hComp.trans hZero

/-- A nonzero exact coefficient map of the descending expansion remains nonzero after
restriction to the original compact-finite standard module. -/
theorem restrict_expand_ne_zero (r : ℕ) (ds : List RealBlock) (hr : realRank ds = r + 1)
    (a : ℝˣ) (h : V[r + 1, ds] ≤ V[r + 1, expand ds]) (B : Coeff[r, expand ds])
    (hB : IsRealWhittakerIntertwiner r (expand ds) a B) (hB₀ : B ≠ 0) :
    B.comp (Submodule.inclusion h) ≠ 0 := by
  have hDetect : RestrictionDetects r a ds (expand ds) := by
    simpa only [List.nil_append, List.append_nil] using
      restrict_expand_ne_zero_aux r a ds [] [] (by simpa using hr)
  exact hDetect h B hB hB₀

/-- The original exact Whittaker model is the range of any nonzero exact map of the
descending character expansion restricted to the original standard module. -/
def RealDescendingWhittakerRangeStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 → ∀ (a : ℝˣ) (es : List RealBlock),
    expand ds = es → ∀ (h : V[r + 1, ds] ≤ V[r + 1, es]) (C : Coeff[r, es]),
      IsRealWhittakerIntertwiner r es a C → C ≠ 0 →
        realWhittakerModel r ds a = (C.comp (Submodule.inclusion h)).range

theorem realDescendingWhittakerRange : RealDescendingWhittakerRangeStatement := by
  intro r ds hr a es he
  subst es
  intro h C hC hC₀
  let C' := C.comp (Submodule.inclusion h)
  have hC' := isRealWhittakerIntertwiner_restrict h hC
  have hC'₀ : C' ≠ 0 := restrict_expand_ne_zero r ds hr a h C hC hC₀
  obtain ⟨T, hTs, hT⟩ := surjectiveIntertwiner_ascendingExpand (r + 1) ds hr
  have hCT := isRealWhittakerIntertwiner_pullback hT hC'
  have hCT₀ : C'.comp T ≠ 0 := by
    intro hz
    apply hC'₀
    apply LinearMap.ext
    intro f
    obtain ⟨v, rfl⟩ := hTs f
    exact LinearMap.congr_fun hz v
  have hMult := realExactCharacterWhittakerUniqueness r (ascendingCharacters ds)
    ((realRank_ascendingExpand ds).trans hr) a
  refine le_antisymm (iSup_le fun B => iSup_le fun hB => ?_)
    (le_iSup_of_le C' (le_iSup_of_le hC' le_rfl))
  have hBT := isRealWhittakerIntertwiner_pullback hT hB
  obtain ⟨c, hc⟩ := hMult (B.comp T) (C'.comp T) hBT hCT hCT₀
  rintro _ ⟨f, rfl⟩
  obtain ⟨v, rfl⟩ := hTs f
  use c • T v
  rw [map_smul]
  exact (LinearMap.congr_fun hc v).symm

open RealGodement RealGodementProfiles in
/-- The canonical Jacquet continuation on the descending position exponents gives
every exact block coefficient by restriction of its source. -/
theorem realWhittakerModel_eq_range_descendingCanonical (r : ℕ) (ds : List RealBlock)
    (hr : realRank ds = r + 1) (a : ℝˣ) (p : Fin (r + 1) → Fin 2) (z : Fin (r + 1) → ℂ)
    (he : expand ds = characterList p z)
    (h : V[r + 1, ds] ≤ V[r + 1, characterList p z]) :
    realWhittakerModel r ds (-a) =
      ((canonicalJacquetMap a p z).comp (Submodule.inclusion h)).range :=
  realDescendingWhittakerRange r ds hr (-a) _ he h _
    (realGodementCanonicalModel r a p z).1 (canonicalJacquetMap_ne_zero r a p z)

end Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries
