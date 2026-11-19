import Langlands.Group.GL.MonomialPatterns
import Langlands.Group.GL.UnipotentDoubleCoset
import Langlands.Representation.Finite.CharacterCoinduction
import Langlands.Representation.Finite.MackeyPairing
import Langlands.Representation.Whittaker.CompatibleMonomialFixedProof
import Langlands.Representation.Whittaker.EntrywiseCharacter
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-! # The finite Gelfand–Graev representation and its endomorphisms -/

noncomputable section

namespace Langlands.FiniteGeneralLinear

open GeneralLinear Whittaker FiniteRep Geometric HarmonicAnalysis Module Representation

variable {k : Type*} [Field k] [Finite k]

/-- Induction of the entrywise Whittaker character from the upper-unipotent subgroup. -/
def gelfandGraev (ψ : AddChar k ℂ) (n : ℕ) : FDRep ℂ (GeneralLinear n k) :=
  induceRep (upperUnipotent n k) (characterFDRep _ (entrywiseCharacter ψ n))

section Discrete

local instance finiteFieldTopology (K : Type*) [Finite K] : TopologicalSpace K := ⊥
local instance finiteFieldDiscrete (K : Type*) [Finite K] : DiscreteTopology K := ⟨rfl⟩
local instance finiteFieldTopologicalRing (K : Type*) [Field K] [Finite K] : IsTopologicalRing K where
  continuous_add := continuous_of_discreteTopology
  continuous_mul := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

private def unitaryCharacter (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) : UnitaryAdditiveCharacter k :=
  UnitaryAdditiveCharacter.ofComplex ψ continuous_of_discreteTopology hψ fun x => by
    apply Complex.norm_eq_one_of_pow_eq_one (n := Nat.card k) _ Nat.card_pos.ne'
    rw [← ψ.map_nsmul_eq_pow, card_nsmul_eq_zero', ψ.map_zero_eq_one]

private theorem compatible_iff_standard (ψ : UnitaryAdditiveCharacter k) (n : ℕ)
    (s : GeneralLinear (n + 1) k) :
    IsCharacterCompatible (upperUnipotent (n + 1) k) (standardCharacter ψ n) s ↔
      IsCharacterCompatibleRepresentative ψ n s := by
  let U := upperUnipotent (n + 1) k
  change (∀ x : orbitStabilizer U U s, standardCharacter ψ n x.val =
    standardCharacter ψ n (stabilizerToInducing U U s x)) ↔ _
  constructor
  · intro h u v huv
    have hv : s⁻¹ * v.val * s = u.val := by rw [← huv]; group
    let x : orbitStabilizer U U s := ⟨v, by
      change s⁻¹ * v.val * s⁻¹⁻¹ ∈ U
      rw [inv_inv, hv]
      exact u.property⟩
    have hxu : stabilizerToInducing U U s x = u := by
      apply Subtype.ext
      rw [stabilizerToInducing_apply]
      exact hv
    have he := h x
    rw [hxu] at he
    exact he.symm
  · intro h x
    symm
    apply h
    rw [stabilizerToInducing_apply]
    group

private theorem compatible_monomial_iff_pattern (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (n : ℕ)
    (w : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → kˣ) :
    IsCharacterCompatible (upperUnipotent (n + 1) k) (entrywiseCharacter ψ (n + 1))
      (monomialRepresentative w d) ↔ IsMonomialPattern w d := by
  let φ := unitaryCharacter ψ hψ
  change IsCharacterCompatible (upperUnipotent (n + 1) k) (entrywiseCharacter φ.complex (n + 1))
    (monomialRepresentative w d) ↔ _
  rw [entrywiseCharacter_eq_standardCharacter, compatible_iff_standard, monomialRepresentative,
    monomial_compatible_iff_root_coefficients]
  constructor
  · intro h i j hij hw
    have hc := h i j hij hw
    by_cases ha : i.val + 1 = j.val <;> by_cases hb : (w i).val + 1 = (w j).val
    · rw [ite_eq_left ha, ite_eq_left hb] at hc
      exact ⟨iff_of_true ha hb, fun _ => Units.ext ((mul_inv_eq_one₀ (Units.ne_zero _)).mp hc.symm)⟩
    · exact False.elim (one_ne_zero (by simpa only [ite_eq_left ha, ite_eq_right hb] using hc))
    · exact False.elim (mul_ne_zero (Units.ne_zero (d i)) (inv_ne_zero (Units.ne_zero (d j)))
        (by simpa only [ite_eq_right ha, ite_eq_left hb] using hc.symm))
    · exact ⟨iff_of_false ha hb, fun h => (ha h).elim⟩
  · intro h i j hij hw
    obtain ⟨heq, hd⟩ := h i j hij hw
    by_cases ha : i.val + 1 = j.val
    · simp only [ite_eq_left ha, ite_eq_left (heq.mp ha), hd ha, mul_inv_cancel₀ (Units.ne_zero (d j))]
    · simp only [ite_eq_right ha, ite_eq_right (mt heq.mpr ha)]

/-- The character-compatible unipotent double cosets in monomial coordinates are precisely the
labelled block patterns. -/
def compatibleMonomialEquiv (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (n : ℕ) :
    {p : Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → kˣ) //
      IsCharacterCompatible (upperUnipotent (n + 1) k) (entrywiseCharacter ψ (n + 1))
        (monomialRepresentative p.1 p.2)} ≃ MonomialPattern (n + 1) kˣ :=
  Equiv.subtypeEquivRight (fun p => compatible_monomial_iff_pattern ψ hψ n p.1 p.2)

private theorem weylTranspose_fixed (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) {n : ℕ}
    (w : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → kˣ)
    (h : IsCharacterCompatible (upperUnipotent (n + 1) k) (entrywiseCharacter ψ (n + 1))
      (monomialRepresentative w d)) :
    weylTransposeHomeomorph n k (monomialRepresentative w d) = monomialRepresentative w d := by
  let φ := unitaryCharacter ψ hψ
  change IsCharacterCompatible _ (entrywiseCharacter φ.complex (n + 1)) _ at h
  rw [entrywiseCharacter_eq_standardCharacter, compatible_iff_standard] at h
  exact weylTransposeHomeomorph_monomial_eq_of_compatible φ w d h

private theorem coinduced_end_mul_comm (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (n : ℕ)
    (S T : CharacterCoindEnd (upperUnipotent (n + 1) k) (entrywiseCharacter ψ (n + 1))) :
    S * T = T * S := by
  let : Fintype (GeneralLinear (n + 1) k) := Fintype.ofFinite _
  apply characterCoindEnd_mul_comm_of_anti
    (a := (weylTransposeHomeomorph n k).toEquiv)
    (ha := weylTransposeHomeomorph_mul n k)
    (aH := weylTransposeUnipotent n k)
    (haH := weylTransposeUnipotent_val n k)
    (r := fun p : Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → kˣ) => monomialRepresentative p.1 p.2)
  · intro u
    apply Units.ext
    simp only [entrywiseCharacter_apply_sum]
    congr 1
    exact weylTransposeUnipotent_superdiagonalSum n k u
  · exact monomialDoubleCoset_bijective.2
  · intro p hp
    exact weylTranspose_fixed ψ hψ p.1 p.2 hp

end Discrete

/-- The endomorphisms of the finite Gelfand–Graev representation commute. -/
theorem gelfandGraev_end_mul_comm (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (n : ℕ)
    (S T : IntertwiningMap (gelfandGraev ψ (n + 1)).ρ (gelfandGraev ψ (n + 1)).ρ) : S * T = T * S := by
  let U := upperUnipotent (n + 1) k
  let χ := entrywiseCharacter ψ (n + 1)
  let V := characterFDRep U χ
  let e : (Representation.Equiv (gelfandGraev ψ (n + 1)).ρ (characterCoind U χ)) :=
    (induceRepEquiv U V).symm.trans (indCoindEquiv U V)
  let S' := e.toIntertwiningMap.comp (S.comp e.symm.toIntertwiningMap)
  let T' := e.toIntertwiningMap.comp (T.comp e.symm.toIntertwiningMap)
  have h := coinduced_end_mul_comm ψ hψ n S' T'
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have hv := DFunLike.congr_fun h (e v)
  exact e.injective (by simpa [S', T'] using hv)

/-- The endomorphism dimension is the number of compatible monomial double cosets. -/
theorem gelfandGraev_end_finrank (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (n : ℕ) :
    finrank ℂ (IntertwiningMap (gelfandGraev ψ (n + 1)).ρ (gelfandGraev ψ (n + 1)).ρ) =
      Nat.card kˣ * Nat.card k ^ n := by
  classical
  let : Fintype (GeneralLinear (n + 1) k) := Fintype.ofFinite _
  let U := upperUnipotent (n + 1) k
  let χ := entrywiseCharacter ψ (n + 1)
  let V := characterFDRep U χ
  let D := Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → kˣ)
  let : Fintype D := Fintype.ofFinite _
  let r (p : D) : GeneralLinear (n + 1) k := monomialRepresentative p.1 p.2
  change finrank ℂ (IntertwiningMap (induceRep U V).ρ (induceRep U V).ρ) = _
  rw [finrank_intertwiningMap_induceRep U U V V r monomialDoubleCoset_bijective]
  have ht (p : D) : mackeyTerm U U V V (r p) = if IsCharacterCompatible U χ (r p) then 1 else 0 :=
    finrank_intertwiningMap_character U χ (r p)
  simp_rw [ht]
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
    ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Nat.card_congr (compatibleMonomialEquiv ψ hψ n),
    MonomialPattern.card_succ, ← Nat.card_eq_card_units_add_one]

end Langlands.FiniteGeneralLinear
