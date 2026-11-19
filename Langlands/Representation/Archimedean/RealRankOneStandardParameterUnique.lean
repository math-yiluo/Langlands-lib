import Langlands.Representation.Archimedean.RealRankZeroStandardModule
import Langlands.Representation.Archimedean.RealRankOneStandardModule
import Langlands.Representation.Archimedean.RealSubquotientEval
import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientReduction

/-! # Real standard parameter uniqueness in ranks zero and one

In rank one the Lie action on the scalar direction reads the exponent and the compact
sign action reads the parity. See the paired Markdown.
-/

noncomputable section
open scoped TensorProduct
set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean RealJacquetFrobenius
open RealRankOneStandardModule (KF G characterVector evalEquiv)

private theorem realCharacterData_eq_of_parity_exponent {c d : RealCharacterData}
    (hp : c.parity = d.parity) (ht : c.exponent = d.exponent) : c = d := by
  have hc : c.character = d.character := by
    apply ContinuousMonoidHom.ext
    intro x
    apply Units.ext
    rw [c.character_eq, d.character_eq, hp, ht]
  cases c
  cases d
  cases hp
  cases ht
  cases hc
  rfl

private theorem posChar_rank_one (d : RealCharacterData) :
    posChar (fun _ : Fin 1 => d.exponent) (fun _ => d.parity) =
      realPositionCharacter [.character d] := by
  have hd : charData d.parity d.exponent = d :=
    realCharacterData_eq_of_parity_exponent rfl rfl
  change realPositionCharacter ((List.ofFn (chars (fun _ : Fin 1 => d.exponent)
    (fun _ => d.parity))).map RealBlock.character) = _
  simp [List.ofFn_succ, chars, expo, hd]

private theorem lie_one_rank_one (d : RealCharacterData) (f : KF d) :
    realStandardLie 1 [.character d] (1 ⊗ₜ (1 : Matrix (Fin 1) (Fin 1) ℝ)) f =
      d.exponent • f := by
  apply (evalEquiv d).injective
  change ((realStandardLie 1 [.character d] (1 ⊗ₜ (1 : Matrix (Fin 1) (Fin 1) ℝ)) f :
    KF d) : G → ℂ) 1 = d.exponent * (f : G → ℂ) 1
  rw [realStandardLie_one_tmul_apply_coe]
  have hf : (f : G → ℂ) ∈ principalSeries ℝ 1
      (posChar (fun _ : Fin 1 => d.exponent) (fun _ => d.parity)) := by
    rw [posChar_rank_one]
    exact f.2.1.1
  have h : (1 : Matrix (Fin 1) (Fin 1) ℝ).IsUpperTriangular := by
    intro i j hij
    exact Matrix.one_apply_ne (ne_of_gt hij)
  simpa using RealSubquotient.rightDerivative_upper_apply_one hf h

private theorem det_signReflection_rank_one :
    Matrix.GeneralLinearGroup.det (Unitary.toUnits (signReflection 1 (0 : Fin 1))) = -1 := by
  apply Units.ext
  change Matrix.det (Matrix.diagonal fun i : Fin 1 => if i = 0 then (-1 : ℝ) else 1) = -1
  simp

private theorem rep_sign_rank_one (d : RealCharacterData) (f : KF d) :
    realStandardRep 1 [.character d] (signReflection 1 (0 : Fin 1)) f =
      (-1 : ℂ) ^ d.parity.val • f := by
  apply (evalEquiv d).injective
  change ((realStandardRep 1 [.character d] (signReflection 1 (0 : Fin 1)) f : KF d) :
    G → ℂ) 1 = (-1 : ℂ) ^ d.parity.val * (f : G → ℂ) 1
  rw [realStandardRep_apply_coe]
  change (f : G → ℂ) (1 * Unitary.toUnits (signReflection 1 (0 : Fin 1))) = _
  rw [one_mul, RealRankOneStandardModule.eval_formula d f.2.1.1, characterVector,
    det_signReflection_rank_one, d.character_eq]
  simp

private theorem parity_sign_injective :
    Function.Injective (fun e : Fin 2 => (-1 : ℂ) ^ e.val) := by
  intro e e' he
  fin_cases e <;> fin_cases e' <;> first | rfl | norm_num at he

private theorem singleton_character_eq_of_intertwiner {c d : RealCharacterData}
    {T : KF c →ₗ[ℂ] KF d}
    (hT : IsRealStandardIntertwiner 1 (realStandardRep 1 [.character d])
      (realStandardLie 1 [.character d]) [.character c] T)
    (hTi : Function.Injective T) : c = d := by
  let f : KF c := (evalEquiv c).symm 1
  have hf : f ≠ 0 := by simp [f]
  have hTf : T f ≠ 0 := fun h => hf (hTi (h.trans (map_zero T).symm))
  have hl := hT.map_realStandardLie (1 ⊗ₜ (1 : Matrix (Fin 1) (Fin 1) ℝ)) f
  rw [lie_one_rank_one, lie_one_rank_one, map_smul] at hl
  have hk := hT.map_realStandardRep (signReflection 1 (0 : Fin 1)) f
  rw [rep_sign_rank_one, rep_sign_rank_one, map_smul] at hk
  exact realCharacterData_eq_of_parity_exponent
    (parity_sign_injective (smul_left_injective ℂ hTf hk)) (smul_left_injective ℂ hTf hl)

/-- Injective intertwiners between the real standard modules of rank at most one
identify the parameter lists up to permutation. -/
def RealRankAtMostOneStandardParameterUniqueStatement : Prop :=
  ∀ (n : ℕ), n ≤ 1 → ∀ (ds es : List RealBlock), realRank ds = n → realRank es = n →
    ∀ T : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
        kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n),
      IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T →
      Function.Injective T → ds.Perm es

/-- Real standard parameter uniqueness in ranks zero and one. -/
theorem realRankAtMostOneStandardParameterUnique : RealRankAtMostOneStandardParameterUniqueStatement := by
  intro n hn ds es hd he T hT hTi
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl
  · obtain rfl := RealRankZeroStandardModule.eq_nil_of_realRank_eq_zero ds hd
    obtain rfl := RealRankZeroStandardModule.eq_nil_of_realRank_eq_zero es he
    exact List.Perm.nil
  · obtain ⟨c, rfl⟩ := RealRankOneStandardModule.eq_singleton_of_realRank_eq_one ds hd
    obtain ⟨d, rfl⟩ := RealRankOneStandardModule.eq_singleton_of_realRank_eq_one es he
    obtain rfl := singleton_character_eq_of_intertwiner hT hTi
    exact List.Perm.refl _

end Langlands.Archimedean
