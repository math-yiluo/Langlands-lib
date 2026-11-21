import Langlands.Representation.Archimedean.ComplexUnitaryBlockPositivity
import Langlands.Representation.Archimedean.ComplexUnitaryBlockSwaps

/-! The strict exponent bound from the signature test for each Hermitian pair. -/

noncomputable section

open scoped Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean ComplexUnitary ComplexBlock

universe uV

private theorem posWeight_hermitianData (ds : List ComplexCharacterData) :
    posWeight (ds.map hermitianData) = posWeight ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    funext k
    cases k with
    | zero => exact hermitianData_weight d
    | succ k => exact congrFun ih k

private theorem testVector_ne_zero {n : ℕ} (ds : List ComplexCharacterData)
    (ij : Option (Fin n × Fin n)) (h : ∀ i j, ij = some (i, j) → i ≠ j) :
    testVector ds ij ≠ 0 := by
  intro hz
  have hv := testVector_apply ds ij 1
  rw [hz, compactTest_one ds ij h] at hv
  exact zero_ne_one hv

/-- The real parts of the exponents in the standard parameter of a unitary generic
complex module lie strictly between `-1/2` and `1/2`. -/
theorem complexUnitaryGenericExponentBound :
    ComplexUnitaryGenericExponentBoundStatement.{uV} := by
  intro n V _ _ ρ π ds _ hI _ _ hU hds x hx
  have hn := hds.1
  obtain ⟨hIds, hUds⟩ :=
    complexStandard_irreducible_unitarizable_of_parameter hI hU hds (List.Perm.refl ds)
  have hdual := perm_hermitianData_of_irreducible_unitarizable ds hn hIds hUds
  obtain ⟨bs, hbs⟩ := exists_parameterBlocks ds hdual
  let grouped := bs.flatMap ParameterBlock.data
  have hlen : grouped.length = n := hbs.symm.length_eq.trans hn
  obtain ⟨hIgrouped, hUgrouped⟩ :=
    complexStandard_irreducible_unitarizable_of_parameter hI hU hds hbs.symm
  obtain ⟨S, hS, c, hc, hSv⟩ := exists_blockSwaps [] bs hlen
  change ∀ ij r, BlockTest ij 0 bs r →
    S (testVector grouped ij) = (c * (r : ℂ)) • testVector (grouped.map hermitianData) ij at hSv
  have hcompact (ij : Option (Fin n × Fin n)) (r : ℝ) (ht : BlockTest ij 0 bs r)
      (k : Matrix.unitaryGroup (Fin n) ℂ) :
      (S (testVector grouped ij) : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits k) =
        (c * (r : ℂ)) * (testVector grouped ij : Langlands.GeneralLinear n ℂ → ℂ)
          (Unitary.toUnits k) := by
    rw [hSv ij r ht]
    change (c * (r : ℂ)) * (testVector (grouped.map hermitianData) ij :
      Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits k) = _
    rw [testVector_apply, testVector_apply,
      compactTest_eq_of_posWeight_eq (posWeight_hermitianData grouped) ij k]
  obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp (hbs.mem_iff.mp hx)
  cases b with
  | single d hd =>
    obtain rfl : x = d := by simpa [ParameterBlock.data] using hxb
    rw [hd, abs_zero]
    norm_num
  | pair d hd =>
    obtain ⟨before, after, hsplit⟩ := List.append_of_mem hb
    let p := (before.flatMap ParameterBlock.data).length
    have hp : p + 2 ≤ n := by
      change (bs.flatMap ParameterBlock.data).length = n at hlen
      simp only [hsplit, List.flatMap_append, List.flatMap_cons, ParameterBlock.data,
        List.length_append, List.length_cons, List.length_nil] at hlen
      dsimp [p]
      omega
    let i := pos p hp 0
    let j := pos p hp 1
    have hij : i ≠ j := fun h => (by decide : (0 : Fin 2) ≠ 1) (pos_injective p hp h)
    have htest : BlockTest (some (i, j)) 0 bs (pairRatio d) := by
      rw [hsplit]
      exact blockTest_selected before after 0 d hd i j
        (by simp [i, pos_val, p]) (by simp [i, j, pos_val])
    have hr : 0 < pairRatio d :=
      relativeMultiplier_pos grouped hlen hIgrouped hUgrouped S hS
        (testVector_ne_zero grouped none (by simp))
        (testVector_ne_zero grouped (some (i, j)) (by
          intro a b h
          cases h
          exact hij))
        hc
        (fun k => by
          simpa only [Complex.ofReal_one, mul_one] using! hcompact none 1 (blockTest_base bs 0) k)
        (hcompact (some (i, j)) (pairRatio d) htest)
    have hden : 0 < 1 + 2 * d.exponent.re := by linarith only [hd]
    have hnum : 0 < 1 - 2 * d.exponent.re := (div_pos_iff_of_pos_right hden).mp hr
    have hbound : d.exponent.re < (1 / 2 : ℝ) := by linarith only [hnum]
    have hx' : x = d ∨ x = hermitianData d := by simpa [ParameterBlock.data] using hxb
    rcases hx' with rfl | rfl
    · simpa only [abs_of_pos hd] using hbound
    · simpa only [hermitianData_re, abs_neg, abs_of_pos hd] using hbound

end Langlands.Archimedean
