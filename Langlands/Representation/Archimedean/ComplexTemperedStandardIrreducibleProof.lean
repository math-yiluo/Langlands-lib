import Langlands.Representation.Archimedean.ComplexMinorProductCyclic
import Langlands.Representation.Archimedean.ComplexSphericalFace
import Langlands.Representation.Archimedean.SphericalCyclic
import Langlands.Representation.Archimedean.ComplexTemperedSortedReduction
import Langlands.Representation.Archimedean.ComplexLowestKTypeMultOne

/-!
# Irreducibility of tempered complex standard modules

`complexTemperedStandardIrreducible : ComplexTemperedStandardIrreducibleStatement`: for every
list `ds` of `n` complex characters whose exponents have equal real parts, the
`(𝔤𝔩_n(ℂ), U(n))`-module of `U(n)`-finite functions of the standard module of `ds` is
irreducible.

The proof is by strong induction on `n`. After sorting the weights `l_0 ≤ ⋯ ≤ l_{n-1}`
(the characters are pairwise unlinked, `complexStandardIrreducible_of_perm`), write the
character at position `i` as `z ↦ z^{l_i} χ'_i(z)` with `χ'_i(z) = |z|^{2 t_i - l_i}` of weight
`0` (`untwist`). The weights are `l_i = minorWeight c d i` for `d = l_0` and
`c_{n-1-i} = l_i - l_{i-1}` (`exists_minorWeight_eq`). Let `T` be the spherical vector of the
standard module of the characters `χ'_i` (`exists_spherical`). Its exponents `t_i - l_i/2` have
nonincreasing real parts. If all weights are equal these real parts are equal and `T` is cyclic
by the spherical core (`SphericalCyclic.fixed_cyclic`); otherwise they are not all equal and `T`
is cyclic by `complexSphericalFaceCyclic`, which uses the induction hypothesis. The product
lemma `complexMinorProductCyclic` then gives a cyclic vector `f₀ = minorMonomial c d · T` whose
restriction to `U(n)` is the minor monomial, and `complexTemperedIrreducible_of_minorMonomial`
concludes. See the Markdown file.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

-- As in `ComplexTemperedSortedReduction`: the charts on units need reduction through the
-- normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean ComplexStrictLanglandsQuotient

namespace ComplexTemperedIrreducible

/-! ## Removing the weights -/

/-- The character `z ↦ |z|^{2 t - l}` of weight `0` and exponent `t - l/2`, for a character `d` of
weight `l` and exponent `t`. -/
def untwistOne (d : ComplexCharacterData) : ComplexCharacterData :=
  characterOfParams 0 (d.exponent - (d.weight : ℂ) / 2)

/-- The list of the characters `untwistOne d`. -/
def untwist (ds : List ComplexCharacterData) : List ComplexCharacterData :=
  ds.map untwistOne

theorem length_untwist (ds : List ComplexCharacterData) : (untwist ds).length = ds.length :=
  List.length_map _

theorem weight_untwist {ds : List ComplexCharacterData} :
    ∀ d ∈ untwist ds, d.weight = 0 := by
  intro d hd
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hd
  rfl

/-- `χ_d(z) = z^l · χ_{untwistOne d}(z)`. -/
theorem character_untwistOne (d : ComplexCharacterData) (z : ℂˣ) :
    (d.character z : ℂ) = (z : ℂ) ^ d.weight * ((untwistOne d).character z : ℂ) := by
  rw [d.character_eq, (untwistOne d).character_eq]
  have hr : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 z.ne_zero)
  have hw : (untwistOne d).weight = 0 := rfl
  have he : 2 * (untwistOne d).exponent = 2 * d.exponent - ((d.weight : ℤ) : ℂ) := by
    change 2 * (d.exponent - (d.weight : ℂ) / 2) = _
    ring
  rw [hw, he, zpow_zero, one_mul, Complex.cpow_sub _ _ hr, Complex.cpow_intCast, div_zpow]
  have hrl : ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ d.weight ≠ 0 := zpow_ne_zero _ hr
  field_simp

/-- The position characters of `ds` are those of `untwist ds` multiplied by `z^{l_i}`. -/
theorem positionCharacter_untwist : ∀ (ds : List ComplexCharacterData) (l : ℕ), l < ds.length →
    ∀ z : ℂˣ, complexPositionCharacter ds l z =
      (z : ℂ) ^ complexPositionWeight ds l * complexPositionCharacter (untwist ds) l z
  | [], _, hl, _ => absurd hl (Nat.not_lt_zero _)
  | d :: _, 0, _, z => character_untwistOne d z
  | _ :: ds, l + 1, hl, z =>
      positionCharacter_untwist ds l (by simpa using hl) z

theorem positionWeight_eq : ∀ (ds : List ComplexCharacterData) (l : ℕ) (hl : l < ds.length),
    complexPositionWeight ds l = (ds[l]).weight
  | [], _, hl => absurd hl (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: ds, l + 1, hl => positionWeight_eq ds l (by simpa using hl)

/-! ## The weights as minor weights -/

/-- The sets `{j : n - (j + 1) ≤ i}` grow by one element at each step. -/
theorem filter_succ (n i : ℕ) (hi : i + 1 < n) :
    Finset.univ.filter (fun j : Fin n => n - (j + 1) ≤ i + 1) =
      insert ⟨n - 2 - i, by omega⟩ (Finset.univ.filter (fun j : Fin n => n - (j + 1) ≤ i)) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  have := j.isLt
  omega

theorem not_mem_filter (n i : ℕ) (hi : i + 1 < n) :
    (⟨n - 2 - i, by omega⟩ : Fin n) ∉
      Finset.univ.filter (fun j : Fin n => n - (j + 1) ≤ i) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

theorem filter_zero (n : ℕ) (hn : 0 < n) :
    Finset.univ.filter (fun j : Fin n => n - (j + 1) ≤ 0) = {⟨n - 1, by omega⟩} := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
  have := j.isLt
  omega

/-- Nondecreasing weights `w 0 ≤ w 1 ≤ ⋯ ≤ w (n-1)` are the minor weights of `d = w 0` and
`c_j = w (n-1-j) - w (n-2-j)` (and `c_{n-1} = 0`). -/
theorem exists_minorWeight_eq (n : ℕ) (w : ℕ → ℤ) (hw : ∀ i, i + 1 < n → w i ≤ w (i + 1)) :
    ∃ (c : Fin n → ℕ) (d : ℤ), ∀ i : Fin n, ComplexMinorProduct.minorWeight c d i = w i := by
  refine ⟨fun j => (w (n - 1 - j) - w (n - 1 - j - 1)).toNat, w 0, ?_⟩
  suffices h : ∀ i : ℕ, ∀ hi : i < n,
      ComplexMinorProduct.minorWeight (fun j : Fin n => (w (n - 1 - j) - w (n - 1 - j - 1)).toNat)
        (w 0) ⟨i, hi⟩ = w i from fun i => h i i.isLt
  intro i
  induction i with
  | zero =>
    intro hi
    rw [ComplexMinorProduct.minorWeight]
    simp only
    rw [filter_zero n hi, Finset.sum_singleton]
    simp only
    have h0 : n - 1 - (n - 1) = 0 := by omega
    rw [h0, Nat.zero_sub, sub_self, Int.toNat_zero, Nat.cast_zero, add_zero]
  | succ i ih =>
    intro hi
    have h := ih (by omega)
    rw [ComplexMinorProduct.minorWeight] at h ⊢
    simp only at h ⊢
    rw [filter_succ n i hi, Finset.sum_insert (not_mem_filter n i hi), ← add_assoc,
      add_comm (w 0), add_assoc, h]
    simp only
    have h1 : n - 1 - (n - 2 - i) = i + 1 := by omega
    have h2 : i + 1 - 1 = i := by omega
    rw [h1, h2, Int.toNat_of_nonneg (sub_nonneg.2 (hw i hi))]
    ring

/-! ## The sorted case -/

variable {n : ℕ}

/-- **Sorted case.** If the tempered standard modules of all sizes `b < n` are irreducible, the
standard module of `n` characters with exponents of equal real part and nondecreasing weights is
irreducible. -/
theorem irreducible_of_sorted (hU : ∀ b < n, ComplexBlockFunctionalSized.TemperedIrreducibleAt b)
    (ds : List ComplexCharacterData) (hlen : ds.length = n)
    (htemp : ∀ d ∈ ds, ∀ e ∈ ds, d.exponent.re = e.exponent.re)
    (hsort : ds.Pairwise (fun d e => d.weight ≤ e.weight)) :
    IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds) := by
  set ds' := untwist ds with hds'
  have hlen' : ds'.length = n := (length_untwist ds).trans hlen
  have hw' : ∀ d ∈ ds', d.weight = 0 := weight_untwist
  -- the weights as minor weights
  have hmono : ∀ i, i + 1 < n → complexPositionWeight ds i ≤ complexPositionWeight ds (i + 1) := by
    intro i hi
    rw [positionWeight_eq ds i (by omega), positionWeight_eq ds (i + 1) (by omega)]
    exact List.pairwise_iff_getElem.mp hsort i (i + 1) (by omega) (by omega) (by omega)
  obtain ⟨c, d, hcd⟩ := exists_minorWeight_eq n (complexPositionWeight ds) hmono
  have hchar : ∀ (i : Fin n) (z : ℂˣ), complexPositionCharacter ds i z =
      (z : ℂ) ^ ComplexMinorProduct.minorWeight c d i * complexPositionCharacter ds' i z := by
    intro i z
    rw [hcd i]
    exact positionCharacter_untwist ds i (by rw [hlen]; exact i.isLt) z
  -- the spherical vector of `ds'`
  obtain ⟨T, hT, hT1⟩ := ComplexSphericalLieGroup.exists_spherical (n := n) hw'
  have hTK : ∀ κ : Matrix.unitaryGroup (Fin n) ℂ,
      (T : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ) = 1 := by
    intro κ
    have h := congrArg (fun f => kFiniteEval (complexStandardModule n ds') 1 f) (hT κ)
    simp only [kFiniteEval_apply] at h hT1
    rw [← hT1, ← h, ComplexPermutation.complexStandardRep_apply_apply, one_mul]
  have hT0 : T ≠ 0 := by
    rintro rfl
    rw [map_zero] at hT1
    exact zero_ne_one hT1
  -- cyclicity of `T`
  have hcyc : ∀ W : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds')
      (unitaryCompact ℂ n)),
      (∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ w ∈ W, complexStandardRep n ds' k w ∈ W) →
      (∀ (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, complexStandardLie n ds' Z w ∈ W) →
      T ∈ W → W = ⊤ := by
    by_cases hall : ∀ d ∈ ds, ∀ e ∈ ds, d.weight = e.weight
    · have htemp' : ∀ d ∈ ds', ∀ e ∈ ds', d.exponent.re = e.exponent.re := by
        intro d' hd' e' he'
        obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hd'
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
        change (d.exponent - (d.weight : ℂ) / 2).re = (e.exponent - (e.weight : ℂ) / 2).re
        rw [hall d hd e he, Complex.sub_re, Complex.sub_re, htemp d hd e he]
      exact fun W _ hWL hTW => SphericalCyclic.fixed_cyclic hlen' hw' htemp' hT hT0 W hWL hTW
    · have hord : ds'.Pairwise (fun d e => e.exponent.re ≤ d.exponent.re) := by
        rw [hds', untwist, List.pairwise_map]
        refine List.Pairwise.imp_of_mem ?_ hsort
        intro d e hd he hde
        change (e.exponent - (e.weight : ℂ) / 2).re ≤ (d.exponent - (d.weight : ℂ) / 2).re
        rw [Complex.sub_re, Complex.sub_re, htemp e he d hd]
        have h2 : ((e.weight : ℂ) / 2).re = (e.weight : ℝ) / 2 := by simp
        have h3 : ((d.weight : ℂ) / 2).re = (d.weight : ℝ) / 2 := by simp
        rw [h2, h3]
        have : (d.weight : ℝ) ≤ e.weight := Int.cast_le.2 hde
        linarith
      have hne : ∃ d ∈ ds', ∃ d' ∈ ds', d.exponent.re ≠ d'.exponent.re := by
        push Not at hall
        obtain ⟨d, hd, e, he, hde⟩ := hall
        refine ⟨untwistOne d, List.mem_map_of_mem hd, untwistOne e, List.mem_map_of_mem he, ?_⟩
        change (d.exponent - (d.weight : ℂ) / 2).re ≠ (e.exponent - (e.weight : ℂ) / 2).re
        rw [Complex.sub_re, Complex.sub_re, htemp d hd e he]
        have h2 : ((e.weight : ℂ) / 2).re = (e.weight : ℝ) / 2 := by simp
        have h3 : ((d.weight : ℂ) / 2).re = (d.weight : ℝ) / 2 := by simp
        rw [h2, h3]
        intro h
        apply hde
        have : (d.weight : ℝ) = e.weight := by linarith
        exact_mod_cast this
      exact fun W hWK hWL hTW =>
        complexSphericalFaceCyclic n ds' hlen' hU hw' hord hne T hTK W hWK hWL hTW
  -- the product with the minor monomial
  obtain ⟨f₀, hf₀, hf₀cyc⟩ := complexMinorProductCyclic n ds ds' c d hchar T hT hcyc
  have hmin : ∀ κ : Matrix.unitaryGroup (Fin n) ℂ,
      (f₀ : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits κ) =
        ComplexLowestKType.minorMonomial c d (κ : Matrix (Fin n) (Fin n) ℂ) := by
    intro κ
    rw [hf₀, hTK, mul_one]
    rfl
  refine complexTemperedIrreducible_of_minorMonomial n ds hlen htemp c d f₀ ?_ hmin hf₀cyc
  intro h0
  have h := hmin (ComplexMinorProduct.revUnitary n)
  rw [h0] at h
  exact ComplexMinorProduct.minorMonomial_revUnitary_ne_zero c d h.symm

/-- Every tempered standard module of size `n` is irreducible, by strong induction on `n`. -/
theorem temperedIrreducibleAt : ∀ n : ℕ, ComplexBlockFunctionalSized.TemperedIrreducibleAt n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ds hlen htemp
    set ds' := ds.mergeSort (fun d e => decide (d.weight ≤ e.weight)) with hds'
    have hperm : ds'.Perm ds := List.mergeSort_perm _ _
    have hmem : ∀ d, d ∈ ds' ↔ d ∈ ds := fun d => hperm.mem_iff
    have htemp' : ∀ d ∈ ds', ∀ e ∈ ds', d.exponent.re = e.exponent.re :=
      fun d hd e he => htemp d ((hmem d).1 hd) e ((hmem e).1 he)
    have hlen' : ds'.length = n := hperm.length_eq.trans hlen
    have hsort : ds'.Pairwise (fun d e => d.weight ≤ e.weight) := by
      have := List.pairwise_mergeSort (le := fun d e : ComplexCharacterData =>
          decide (d.weight ≤ e.weight))
        (fun a b c hab hbc => by
          simp only [decide_eq_true_eq] at hab hbc ⊢
          exact hab.trans hbc)
        (fun a b => by
          rcases le_total a.weight b.weight with h | h
          · simp [h]
          · simp [h])
        ds
      exact this.imp fun h => by simpa using h
    exact complexStandardIrreducible_of_perm n ds ds' hlen' hperm
      (ComplexTemperedSorted.isComplexUnlinked_of_re_eq htemp')
      (irreducible_of_sorted ih ds' hlen' htemp' hsort)

end ComplexTemperedIrreducible

/-- **Tempered complex standard modules are irreducible.** For every list `ds` of `n` complex
characters whose exponents have equal real parts, the `(𝔤𝔩_n(ℂ), U(n))`-module of `U(n)`-finite
functions of the standard module of `ds` is irreducible. -/
theorem complexTemperedStandardIrreducible : ComplexTemperedStandardIrreducibleStatement :=
  fun n => ComplexTemperedIrreducible.temperedIrreducibleAt n

end Langlands.Archimedean
