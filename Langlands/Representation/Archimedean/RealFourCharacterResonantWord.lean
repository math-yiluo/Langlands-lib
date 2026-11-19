import Langlands.Representation.Archimedean.RealFourCharacterLongestWord
import Langlands.Representation.Archimedean.RealResonantHighInverse
import Langlands.Representation.Archimedean.RealInducedSwapRegularization

/-! # Specialization of the four-character reversal at two resonances -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealFourCharacterResonantWord

open Langlands.LocalFactor.Archimedean RealBlockMultiplier RealBlockFrobeniusMap
  RealBlockFourierFinite RealBlockJacquet RealCharacterPair RealCharacterPairReducible
  RealCanonicalCharacterBraid RealFourCharacterLongestWord RealResonantHighInverse
  RealBlockMultiplierAnalytic RealKTypeCount
open RealInducedSwapRegularization (blockFrobMap_eq_smul_of_eq_on_parity)
open Filter Topology

abbrev resonantWeight (ε : ℤ) (r : ℕ) : ℕ := ε.toNat + 2 * r + 1

private theorem crossingData {a b : RealCharacterData} {pre post : List RealBlock}
    {μ : ℤ → ℂ} (hn : realRank (pre ++ .character b :: .character a :: post) = 4)
    (hs : IsSymmetric (pairParity a b) ((-1 : ℂ) ^ (pairParity a b).natAbs) μ) :
    IsBlockFrobData 4 (pre ++ .character a :: .character b :: post)
      (pre ++ .character b :: .character a :: post) (realRank pre) (pairParity a b)
      ((-1 : ℂ) ^ (pairParity a b).natAbs) μ := by
  have hs' : IsSymmetric (pairParity b a) (sigma0 b a) μ := by
    simpa only [sigma0, RealInducedSwapGeneric.pairParity_comm b a] using hs
  simpa only [dc, sigma0, RealInducedSwapGeneric.pairParity_comm b a,
    List.append_assoc, List.cons_append, List.nil_append] using
    data_swap (c := b) (d := a) (pre := pre) (post := post) hn hs'

variable {x y u v : RealCharacterData}

/-- Fourier data for the first, normalized crossing. -/
theorem highInverseData (r : ℕ) (z : ℂ) :
    IsBlockFrobData 4 (characters x y u v) (characters x u y v) 1 (pairParity y u)
      ((-1 : ℂ) ^ (pairParity y u).natAbs) (highInverse (pairParity y u) r z) :=
  crossingData (pre := [.character x]) (post := [.character v]) rfl
    (highInverse_symmetric (pairParity_eq y u) r z)

/-- Fourier data for the second crossing, with parameter `A + z`. -/
theorem leftData (A : ℕ) (z : ℂ) :
    IsBlockFrobData 4 (characters x u y v) (characters u x y v) 0 (pairParity x u)
      ((-1 : ℂ) ^ (pairParity x u).natAbs) (genericMultiplier ((A : ℂ) + z) (pairParity x u)) :=
  crossingData (pre := []) (post := [.character y, .character v]) rfl
    (isSymmetric_genericMultiplier _ (pairParity_eq x u))

/-- Fourier data for the third crossing, with parameter `B + z`. -/
theorem rightData (B : ℕ) (z : ℂ) :
    IsBlockFrobData 4 (characters u x y v) (characters u x v y) 2 (pairParity y v)
      ((-1 : ℂ) ^ (pairParity y v).natAbs) (genericMultiplier ((B : ℂ) + z) (pairParity y v)) :=
  crossingData (pre := [.character u, .character x]) (post := []) rfl
    (isSymmetric_genericMultiplier _ (pairParity_eq y v))

/-- Fourier data for the fourth crossing, regularized at the inner pole. -/
theorem shiftedTailData (s : ℕ) (z : ℂ) :
    IsBlockFrobData 4 (characters u x v y) (characters u v x y) 1 (pairParity x v)
      ((-1 : ℂ) ^ (pairParity x v).natAbs) (shiftedTail (pairParity x v) s z) :=
  crossingData (pre := [.character u]) (post := [.character y]) rfl
    (shiftedTail_symmetric (pairParity_eq x v) s z)

/-- The inverse of the canonical tail multiplier, viewed as a crossing in the
opposite direction. The totalized inverse vanishes on low modes. -/
theorem inverseTailData (r : ℕ) :
    IsBlockFrobData 4 (characters x y u v) (characters x u y v) 1 (pairParity y u)
      ((-1 : ℂ) ^ (pairParity y u).natAbs)
      (fun j => ((Choice.tail r : Choice (pairParity y u)).multiplier j)⁻¹) := by
  apply crossingData (pre := [.character x]) (post := [.character v]) rfl
  simpa only [← inv_pow, inv_neg, inv_one] using
    ((Choice.tail r : Choice (pairParity y u)).symmetric (pairParity_eq y u)).inv

/-- The six-crossing word with the first and fourth factors analytically normalized. -/
def normalizedWord (r s A B : ℕ) (cxy : Choice (pairParity x y)) (cuv : Choice (pairParity u v))
    (z : ℂ) : Four x y u v →ₗ[ℂ] Four v u y x :=
  swap2 cxy ∘ₗ swap0 cuv ∘ₗ blockFrobMap (shiftedTailData s z) ∘ₗ
    blockFrobMap (rightData B z) ∘ₗ blockFrobMap (leftData A z) ∘ₗ
    blockFrobMap (highInverseData r z)

private theorem generic_analytic (A : ℕ) (hA : 0 < A) {ε : ℤ} (hε : ε = 0 ∨ ε = 1) (j : ℤ) :
    AnalyticAt ℂ (fun z => genericMultiplier ((A : ℂ) + z) ε j) 0 :=
  (RealGenericMultiplierDegeneration.analyticAt_genericMultiplier_pos hA hε j).comp_of_eq
    (analyticAt_const.add analyticAt_id) (add_zero _)

private theorem normalizedWord_analytic (r s : ℕ) {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (cxy : Choice (pairParity x y)) (cuv : Choice (pairParity u v)) (f : Four x y u v) :
    IsWeaklyAnalyticAt (fun z => normalizedWord r s A B cxy cuv z f) 0 := by
  obtain ⟨N, hf⟩ := exists_mem_layer_degreeLE (realStandardModule_le_principalSeries _ _) f
  have ha₁ := weaklyAnalyticAt_blockFrobMap (highInverseData (x := x) (v := v) r)
    (fun _ => hf) (IsWeaklyAnalyticAt.const f 0) (analyticAt_highInverse (pairParity_eq y u) r)
  have hm₁ z := mem_layer_blockFrobMap (highInverseData (x := x) (v := v) r z) hf
  have ha₂ := weaklyAnalyticAt_blockFrobMap (leftData (x := x) (v := v) A) hm₁ ha₁
    (generic_analytic A hA (pairParity_eq x u))
  have hm₂ z := mem_layer_blockFrobMap (leftData (x := x) (v := v) A z) (hm₁ z)
  have ha₃ := weaklyAnalyticAt_blockFrobMap (rightData (x := x) (u := u) B) hm₂ ha₂
    (generic_analytic B hB (pairParity_eq y v))
  have hm₃ z := mem_layer_blockFrobMap (rightData (x := x) (u := u) B z) (hm₂ z)
  have ha₄ := weaklyAnalyticAt_blockFrobMap (shiftedTailData (u := u) (y := y) s) hm₃ ha₃
    (fun j => analyticAt_shiftedTail (pairParity x v) j s)
  exact (ha₄.map (swap0 cuv)).map (swap2 cxy)

private theorem highInverse_apply_of_ne (r : ℕ) {z : ℂ} (hz : z ≠ 0) (f : Four x y u v)
    (hf : ∀ j : ℤ, Even (j - pairParity y u) →
      |j| ≤ (resonantWeight (pairParity y u) r : ℤ) →
      ∀ k ∈ unitaryCompact ℝ 4, blockFourierCoefficient 4 1 j f k = 0)
    (cyu : Choice (pairParity y u))
    (hcyu : cyu.multiplier = genericMultiplier
      ((resonantWeight (pairParity y u) r : ℂ) + z) (pairParity y u)) :
    blockFrobMap (highInverseData r z) f = z⁻¹ • swap1 cyu f := by
  have hdata : IsBlockFrobData 4 (characters x y u v) (characters x u y v) 1
      (pairParity y u) ((-1 : ℂ) ^ (pairParity y u).natAbs) cyu.multiplier :=
    data (n := 4) (pre := [.character x]) (post := [.character v]) rfl cyu
  refine eq_of_blockFourierCoefficient_eq (p := 1) (by decide) fun j k hk => ?_
  change blockFourierCoefficient 4 1 j (blockFrobMap (highInverseData r z) f) k =
    blockFourierCoefficient 4 1 j (z⁻¹ • blockFrobMap hdata f) k
  rw [blockFourierCoefficient_blockFrobMap (highInverseData r z) _ hk,
    blockFourierCoefficient_smul, blockFourierCoefficient_blockFrobMap hdata _ hk]
  by_cases hj : Even (j - pairParity y u)
  · by_cases hcut : (resonantWeight (pairParity y u) r : ℤ) < |j|
    · rw [highInverse_of_ne (pairParity_eq y u) rfl hz hj hcut, hcyu, mul_assoc]
    · rw [hf j hj (le_of_not_gt hcut) k hk, mul_zero, mul_zero, mul_zero]
  · rw [blockFourierCoefficient_eq_zero_of_not_even hdata.lt hdata.par f hj k,
      mul_zero, mul_zero, mul_zero]

private theorem shiftDenum {q z : ℂ} (hq : q.im = 0) (hz : z.im ≠ 0) (ε : ℤ) (i : ℕ) :
    (ε : ℂ) + 2 * i + 1 + (q + z) ≠ 0 := by
  intro he
  apply hz
  simpa [Complex.add_im, Complex.mul_im, hq] using congrArg Complex.im he

private theorem normalizedWord_of_im_ne_zero
    (hPoly : ∀ N a b, RealGenericCharacterBraidReduction.PolynomialBraid N a b)
    (r s A B : ℕ) (cxy : Choice (pairParity x y)) (cuv : Choice (pairParity u v))
    (hxyu : (A : ℂ) = cxy.parameter + (resonantWeight (pairParity y u) r : ℂ))
    (hxyv : -(resonantWeight (pairParity x v) s : ℂ) = cxy.parameter + (B : ℂ))
    (hxuv : -(resonantWeight (pairParity x v) s : ℂ) = (A : ℂ) + cuv.parameter)
    (hyuv : (B : ℂ) = (resonantWeight (pairParity y u) r : ℂ) + cuv.parameter)
    (f : Four x y u v) (hf : ∀ j : ℤ, Even (j - pairParity y u) →
      |j| ≤ (resonantWeight (pairParity y u) r : ℤ) →
      ∀ k ∈ unitaryCompact ℝ 4, blockFourierCoefficient 4 1 j f k = 0)
    (hkill : swap2 cuv (swap0 cxy f) = 0) {z : ℂ} (hz : z.im ≠ 0) :
    normalizedWord r s A B cxy cuv z f = 0 := by
  have hz0 : z ≠ 0 := by
    intro he
    rw [he, Complex.zero_im] at hz
    exact hz rfl
  let cxu : Choice (pairParity x u) := .generic ((A : ℂ) + z) (shiftDenum (by simp) hz _)
  let cyv : Choice (pairParity y v) := .generic ((B : ℂ) + z) (shiftDenum (by simp) hz _)
  let cyu : Choice (pairParity y u) := .generic ((resonantWeight (pairParity y u) r : ℂ) + z)
    (shiftDenum (by simp) hz _)
  let cxv : Choice (pairParity x v) := .generic (-(resonantWeight (pairParity x v) s : ℂ) + z)
    (shiftDenum (by simp) hz _)
  have hstart := highInverse_apply_of_ne r hz0 f hf cyu rfl
  have h₄ : blockFrobMap (shiftedTailData (u := u) (y := y) (x := x) (v := v) s z) =
      z • swap1 cxv :=
    blockFrobMap_eq_smul_of_eq_on_parity _
      (data (n := 4) (pre := [.character u]) (post := [.character y]) rfl cxv) fun j _ =>
      shiftedTail_of_ne (pairParity_eq x v) rfl hz0 j
  have h₂ : blockFrobMap (leftData (x := x) (u := u) (y := y) (v := v) A z) = swap0 cxu := rfl
  have h₃ : blockFrobMap (rightData (u := u) (x := x) (y := y) (v := v) B z) = swap2 cyv := rfl
  have heq := longestWord hPoly cxy cxu cxv cyu cyv cuv
    (by
      change (A : ℂ) + z = cxy.parameter + ((resonantWeight (pairParity y u) r : ℂ) + z)
      linear_combination hxyu)
    (by
      change -(resonantWeight (pairParity x v) s : ℂ) + z = cxy.parameter + ((B : ℂ) + z)
      linear_combination hxyv)
    (by
      change -(resonantWeight (pairParity x v) s : ℂ) + z = ((A : ℂ) + z) + cuv.parameter
      linear_combination hxuv)
    (by
      change (B : ℂ) + z = ((resonantWeight (pairParity y u) r : ℂ) + z) + cuv.parameter
      linear_combination hyuv) f
  simp only [normalizedWord, LinearMap.comp_apply, hstart, h₄, h₂, h₃, LinearMap.smul_apply,
    map_smul, smul_smul, inv_mul_cancel₀ hz0, one_smul, heq, hkill, map_zero]

private theorem value_zero_of_im_ne_zero {ds : List RealBlock} (F : ℂ → KF 4 ds)
    (ha : IsWeaklyAnalyticAt F 0) (hz : ∀ z, z.im ≠ 0 → F z = 0) : F 0 = 0 := by
  apply restrict_injective (realStandardModule_le_principalSeries _ _)
  rw [map_zero]
  funext k
  let ev : KF 4 ds →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : Matrix.unitaryGroup (Fin 4) ℝ => ℂ) k).comp
      (restrictLinear 4 ∘ₗ (KF 4 ds).subtype)
  change ev (F 0) = 0
  have hline : ContinuousAt (fun t : ℝ => (t : ℂ) * Complex.I) 0 :=
    Complex.continuous_ofReal.continuousAt.mul continuousAt_const
  have hlim : Tendsto (fun t : ℝ => ev (F ((t : ℂ) * Complex.I))) (𝓝[≠] 0) (𝓝 (ev (F 0))) := by
    have hh := (ha ev).continuousAt.comp_of_eq hline (by simp : ((0 : ℝ) : ℂ) * Complex.I = 0)
    simpa only [ContinuousWithinAt, Function.comp_def, Complex.ofReal_zero, zero_mul] using
      hh.continuousWithinAt (s := ({0} : Set ℝ)ᶜ)
  have hzero : (fun t : ℝ => ev (F ((t : ℂ) * Complex.I))) =ᶠ[𝓝[≠] 0] fun _ => (0 : ℂ) := by
    filter_upwards [eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := {0}ᶜ)] with t ht
    have ht0 : t ≠ 0 := ht
    rw [hz _ (by simpa [Complex.mul_im] using ht0), map_zero]
  exact tendsto_nhds_unique_of_eventuallyEq hlim tendsto_const_nhds hzero

/-- Specialization at zero gives the inverse outer canonical tail, two
generic crossings, the inner canonical tail and the two fixed crossings.
If the opposite word starts by killing the source, this composite is zero. -/
theorem specializedWord_eq_zero
    (hPoly : ∀ N a b, RealGenericCharacterBraidReduction.PolynomialBraid N a b)
    (r s : ℕ) {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (cxy : Choice (pairParity x y)) (cuv : Choice (pairParity u v))
    (hxyu : (A : ℂ) = cxy.parameter + (resonantWeight (pairParity y u) r : ℂ))
    (hxyv : -(resonantWeight (pairParity x v) s : ℂ) = cxy.parameter + (B : ℂ))
    (hxuv : -(resonantWeight (pairParity x v) s : ℂ) = (A : ℂ) + cuv.parameter)
    (hyuv : (B : ℂ) = (resonantWeight (pairParity y u) r : ℂ) + cuv.parameter)
    (f : Four x y u v) (hf : ∀ j : ℤ, Even (j - pairParity y u) →
      |j| ≤ (resonantWeight (pairParity y u) r : ℤ) →
      ∀ k ∈ unitaryCompact ℝ 4, blockFourierCoefficient 4 1 j f k = 0)
    (hkill : swap2 cuv (swap0 cxy f) = 0) :
    swap2 cxy (swap0 cuv (swap1 (.tail s)
      (blockFrobMap (rightData B 0) (blockFrobMap (leftData A 0)
        (blockFrobMap (inverseTailData r) f))))) = 0 := by
  have hz := value_zero_of_im_ne_zero (fun z => normalizedWord r s A B cxy cuv z f)
    (normalizedWord_analytic r s hA hB cxy cuv f)
    (fun _ hz => normalizedWord_of_im_ne_zero hPoly r s A B cxy cuv hxyu hxyv hxuv hyuv f hf hkill hz)
  have h₁ : blockFrobMap (highInverseData (x := x) (y := y) (u := u) (v := v) r 0) =
      (-(residue (pairParity y u) r)⁻¹) • blockFrobMap (inverseTailData r) :=
    blockFrobMap_eq_smul_of_eq_on_parity _ _ fun _ hj => highInverse_zero (pairParity_eq y u) rfl hj
  have h₄ : blockFrobMap (shiftedTailData (u := u) (y := y) (x := x) (v := v) s 0) =
      residue (pairParity x v) s • swap1 (.tail s) :=
    blockFrobMap_eq_smul_of_eq_on_parity _
      (data (n := 4) (pre := [.character u]) (post := [.character y]) rfl (.tail s)) fun j _ =>
      shiftedTail_zero (pairParity_eq x v) rfl j
  simp only [normalizedWord, LinearMap.comp_apply, h₁, h₄, LinearMap.smul_apply, map_smul,
    smul_smul] at hz
  have hne : -(residue (pairParity y u) r)⁻¹ * residue (pairParity x v) s ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (residue_ne_zero (pairParity_eq y u) r)))
      (residue_ne_zero (pairParity_eq x v) s)
  exact (smul_eq_zero.mp hz).resolve_left hne

end Langlands.Archimedean.RealFourCharacterResonantWord

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealBlockFrobeniusMap RealBlockFourierFinite
  RealCharacterPair RealCanonicalCharacterBraid RealFourCharacterLongestWord
  RealFourCharacterResonantWord

/-- An analytic specialization of the reversal annihilates a vector in the
outer high window when the two disjoint initial crossings annihilate it. -/
def RealFourCharacterResonantWordStatement : Prop :=
  (∀ N a b, RealGenericCharacterBraidReduction.PolynomialBraid N a b) →
    ∀ (x y u v : RealCharacterData) (r s A B : ℕ), 0 < A → 0 < B →
      ∀ (cxy : Choice (pairParity x y)) (cuv : Choice (pairParity u v)),
        (A : ℂ) = cxy.parameter + (resonantWeight (pairParity y u) r : ℂ) →
        -(resonantWeight (pairParity x v) s : ℂ) = cxy.parameter + (B : ℂ) →
        -(resonantWeight (pairParity x v) s : ℂ) = (A : ℂ) + cuv.parameter →
        (B : ℂ) = (resonantWeight (pairParity y u) r : ℂ) + cuv.parameter →
        ∀ f : Four x y u v,
          (∀ j : ℤ, Even (j - pairParity y u) →
            |j| ≤ (resonantWeight (pairParity y u) r : ℤ) →
            ∀ k ∈ unitaryCompact ℝ 4, blockFourierCoefficient 4 1 j f k = 0) →
          RealFourCharacterLongestWord.swap2 cuv (RealFourCharacterLongestWord.swap0 cxy f) = 0 →
          RealFourCharacterLongestWord.swap2 cxy (RealFourCharacterLongestWord.swap0 cuv
            (RealFourCharacterLongestWord.swap1 (.tail s)
              (blockFrobMap (rightData B 0) (blockFrobMap (leftData A 0)
                (blockFrobMap (inverseTailData r) f))))) = 0

theorem realFourCharacterResonantWord : RealFourCharacterResonantWordStatement :=
  fun hPoly _ _ _ _ r s _ _ hA hB => specializedWord_eq_zero hPoly r s hA hB

end Langlands.Archimedean
