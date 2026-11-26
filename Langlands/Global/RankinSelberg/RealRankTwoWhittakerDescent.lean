import Langlands.Global.RankinSelberg.RealPrincipalSeriesQuotient
import Langlands.Global.RankinSelberg.RealWhittakerFiniteKernel
import Langlands.Global.RankinSelberg.RealWhittakerUniformGrowth
import Langlands.Representation.Archimedean.RealInducedPairKernelRecovery
import Langlands.Representation.Archimedean.RealRankOneStandardModule
import Langlands.Representation.Archimedean.RealSmallOrthogonalHaar

/-! # Ascending character descent for real rank two -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries

open RealBlockJacquet RealBlockFrobeniusMap RealBlockFourierFinite RealBlockMultiplier
open RealSmallOrthogonalHaar

local notation "H" => Langlands.GeneralLinear 2 ℝ
local notation "K" => unitaryCompact ℝ 2
local notation "V" ds:max => Automorphic.realStandardKFinite 2 ds

private theorem finiteDimensional_of_bounded_modes {ds : List RealBlock} (A : Submodule ℂ (V ds)) (l : ℕ)
    (hA : ∀ (f : A) (j : ℤ), (l : ℤ) ≤ |j| → ∀ k ∈ K,
      blockFourierCoefficient 2 0 j f.val.val k = 0) :
    FiniteDimensional ℂ A := by
  let J := Finset.Ioo (-(l : ℤ)) (l : ℤ)
  let P : A →ₗ[ℂ] (J → ℂ) :=
    { toFun := fun f j => blockFourierCoefficient 2 0 j f.val.val 1
      map_add' := fun f g => funext fun j =>
        blockFourierCoefficient_add 0 j f.val.property.1.1.1.continuous g.val.property.1.1.1.continuous 1
      map_smul' := fun c f => funext fun j => blockFourierCoefficient_smul 0 j c f.val.val 1 }
  let _ : FiniteDimensional ℂ (J → ℂ) := inferInstance
  refine FiniteDimensional.of_injective P ?_
  suffices hZero : ∀ f : A, P f = 0 → f = 0 by
    intro f g hfg
    exact sub_eq_zero.mp (hZero (f - g) ((P.map_sub f g).trans (sub_eq_zero.mpr hfg)))
  intro f hf
  apply Subtype.ext
  change f.val = 0
  apply eq_of_blockFourierCoefficient_eq (p := 0) (by decide)
  have hOne (j : ℤ) : blockFourierCoefficient 2 0 j f.val.val 1 = 0 := by
    by_cases hj : |j| < (l : ℤ)
    · have hj' : j ∈ J := Finset.mem_Ioo.mpr (abs_lt.mp hj)
      exact congrFun hf ⟨j, hj'⟩
    · exact hA f j (le_of_not_gt hj) 1 (unitaryCompact ℝ 2).one_mem
  intro j k hk
  rw [ZeroMemClass.coe_zero, blockFourierCoefficient_zero_fun]
  let u : Matrix.unitaryGroup (Fin 2) ℝ := ⟨k.val, hk⟩
  have hu : Unitary.toUnits u = k := Units.ext rfl
  obtain ⟨θ, hθ | hθ⟩ := orthogonal_two_cases u
  · rw [← hu, hθ, toUnits_rotation]
    have hRot := blockFourierCoefficient_blockRotation_mul (N := 2) (p := 0)
      (by decide) f.val.val j θ 1
    simpa only [mul_one, hOne, mul_zero] using hRot
  · rw [← hu, hθ, map_mul, toUnits_rotation, blockFourierCoefficient_blockRotation_mul (by decide)]
    have hRef := blockFourierCoefficient_signReflection_mul_of_mem (N := 2) (p := 0) (by decide)
      (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one ds) f.val.property.1.1
      (0 : Fin 2) (Or.inl rfl) j 1
    have hRef' : blockFourierCoefficient 2 0 j f.val.val (Unitary.toUnits reflectTwo) = 0 := by
      simpa only [mul_one, hOne, mul_zero] using hRef
    rw [hRef', mul_zero]

private def highParityTwo (d : ComplexCharacterData) : Fin 2 :=
  RealGammaReflection.positionParity d.weight.natAbs

private theorem highParityTwo_spec (d : ComplexCharacterData) :
    ((highParityTwo d).val + (0 : Fin 2).val) % 2 = (d.weight.natAbs + 1) % 2 := by
  rw [highParityTwo, RealGammaReflection.positionParity, Fin.val_add]
  change ((d.weight.natAbs % 2 + 1) % 2 + 0) % 2 = (d.weight.natAbs + 1) % 2
  omega

open RealInducedCharacter (ca cb data_tail tail_parity modulo_tail tail_surjective)

private theorem finiteDimensional_induced_tail_kernel (d : ComplexCharacterData) (hw : d.weight ≠ 0) :
    FiniteDimensional ℂ (LinearMap.ker (blockFrobMap
      (data_tail (pre := []) (post := []) (by rfl : realRank ([] ++ [.induced d] ++ []) = 2)
        (Int.natAbs_pos.mpr hw) (highParityTwo_spec d)))) := by
  let l := d.weight.natAbs
  have hl : 0 < l := Int.natAbs_pos.mpr hw
  have hp := tail_parity (highParityTwo_spec d)
  let T := blockFrobMap (data_tail (pre := []) (post := [])
    (by rfl : realRank ([] ++ [.induced d] ++ []) = 2) hl (highParityTwo_spec d))
  change FiniteDimensional ℂ (LinearMap.ker T)
  refine finiteDimensional_of_bounded_modes (LinearMap.ker T) l ?_
  intro f j hj k hk
  have hcut := (RealInducedPairKernelRecovery.blockFrobMap_eq_zero_iff_tail
    (data_tail (pre := []) (post := []) (by rfl : realRank ([] ++ [.induced d] ++ []) = 2)
      hl (highParityTwo_spec d)) l hp (fun j hj' =>
        tailMultiplier_ne_zero_iff hl (RealCharacterPair.pairParity_eq _ _) hp
          (RealCharacterPairReducible.neg_one_pow_sq_fin (highParityTwo d)) hj') f.val).mp
    (LinearMap.mem_ker.mp f.property)
  exact hcut k hk j hj

private theorem realWhittakerModel_eq_of_standard_eq {r : ℕ} {ds es : List RealBlock} (a : ℝˣ)
    (h : realStandardModule (r + 1) ds = realStandardModule (r + 1) es) :
    realWhittakerModel r ds a = realWhittakerModel r es a := by
  unfold realWhittakerModel IsRealWhittakerIntertwiner Automorphic.realStandardKFinite
  rw [h]

private theorem induced_ascending_descent (a : ℝˣ) (d : ComplexCharacterData) :
    realWhittakerModel 1 (ascendingExpand [.induced d]) a ≤ realWhittakerModel 1 [.induced d] a := by
  by_cases hw : d.weight = 0
  · have he : ascendingExpand [.induced d] = realBlockExpand (.induced d) := by
      change ((if d.weight = 0 then [ca d (highParityTwo d), cb d 0]
        else [cb d 0, ca d (highParityTwo d)]) ++ []).map RealBlock.character = _
      simp [realBlockExpand, hw, ca, cb, RealInducedCharacter.aExp, RealInducedCharacter.bExp,
        highParityTwo, RealGammaReflection.positionParity]
    apply (realWhittakerModel_eq_of_standard_eq a ?_).le
    rw [he]
    simpa only [List.nil_append, List.append_nil] using
      (realStandardModule_append_expand 2 [] [] (.induced d)).symm
  · have he : ascendingExpand [.induced d] = [.character (cb d 0), .character (ca d (highParityTwo d))] := by
      change ((if d.weight = 0 then [ca d (highParityTwo d), cb d 0]
        else [cb d 0, ca d (highParityTwo d)]) ++ []).map RealBlock.character = _
      simp [hw]
    rw [he]
    have hr : realRank ([] ++ [.induced d] ++ []) = 2 := rfl
    have hl := Int.natAbs_pos.mpr hw
    have hp := highParityTwo_spec d
    let T := blockFrobMap (data_tail (pre := []) (post := []) hr hl hp)
    exact RealLocalWhittaker.model_le_of_finiteKernel (r := 1) (by decide) a T
      (tail_surjective hr hl hp)
      (RealExponentDeformation.isRealStandardIntertwiner_of_modulo_bot (modulo_tail hr hl hp))
      (finiteDimensional_induced_tail_kernel d hw)

private theorem realRank_eq_zero_iff_nil (ds : List RealBlock) : realRank ds = 0 → ds = [] := by
  cases ds with
  | nil => simp
  | cons d ds =>
    cases d <;> simp [realRank_cons, RealBlock.rank]

/-- For every real block presentation of `GL₂`, the ascending character quotient induces
an equality of the exact coefficient spaces. -/
def RealRankTwoWhittakerDescentStatement : Prop :=
  ∀ (ds : List RealBlock), realRank ds = 2 → ∀ a : ℝˣ,
    realWhittakerModel 1 (ascendingExpand ds) a = realWhittakerModel 1 ds a

theorem realRankTwoWhittakerDescent : RealRankTwoWhittakerDescentStatement := by
  intro ds hr a
  apply le_antisymm
  · cases ds with
    | nil => simp [realRank] at hr
    | cons d ds =>
      cases d with
      | character c =>
        have ht : realRank ds = 1 := by
          rw [realRank_cons, RealBlock.rank] at hr
          omega
        obtain ⟨e, rfl⟩ := RealRankOneStandardModule.eq_singleton_of_realRank_eq_one ds ht
        rfl
      | induced d =>
        have ht : realRank ds = 0 := by
          rw [realRank_cons, RealBlock.rank] at hr
          omega
        rw [realRank_eq_zero_iff_nil ds ht]
        exact induced_ascending_descent a d
  · rw [realWhittakerModels_eq 1 ds hr a,
      realWhittakerModels_eq 1 (ascendingExpand ds) ((realRank_ascendingExpand ds).trans hr) a]
    exact uniformModel_le_ascendingExpand 1 ds hr a

end Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries
