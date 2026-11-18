import Langlands.Representation.Finite.VirtualCharacterProof
import Mathlib.SetTheory.Cardinal.Finite

/-! Finite irreducible character expansions with actual constituent multiplicities. -/

noncomputable section

open Module Representation
open scoped BigOperators

namespace Langlands.FiniteRep

variable {G : Type*} [Group G]

private def linearPair [Fintype G] (f : G → ℂ) : (G → ℂ) →ₗ[ℂ] ℂ where
  toFun := VirtualCharacter.pairing f
  map_add' := map_add _
  map_smul' c g := by
    change (Fintype.card G : ℂ)⁻¹ * ∑ x : G, f x⁻¹ * (c * g x) =
      c * ((Fintype.card G : ℂ)⁻¹ * ∑ x : G, f x⁻¹ * g x)
    simp only [mul_left_comm (f _), ← Finset.mul_sum]
    ring

open Classical in
private theorem linearPair_irreducible [Fintype G] (a b : IrreducibleClass G) :
    linearPair (VirtualCharacter.rep b).character (VirtualCharacter.rep a).character =
      if b = a then (1 : ℂ) else 0 := by
  classical
  change VirtualCharacter.pairing (VirtualCharacter.rep b).character
    (VirtualCharacter.rep a).character = _
  rw [← VirtualCharacter.character_val b, ← VirtualCharacter.character_val a]
  exact VirtualCharacter.pairing_irreducible a b

/-- A finite group has finitely many irreducible complex characters. -/
instance finite_irreducibleClass [Finite G] : Finite (IrreducibleClass G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hi : LinearIndependent ℂ (fun a : IrreducibleClass G => (VirtualCharacter.rep a).character) := by
    rw [linearIndependent_iff']
    intro s c hs b hb
    have h := congrArg (linearPair (VirtualCharacter.rep b).character) hs
    simp only [map_sum, map_smul, map_zero, linearPair_irreducible, smul_eq_mul] at h
    simp_rw [mul_ite, mul_one, mul_zero] at h
    have he : (∑ a ∈ s, if b = a then c a else 0) = c b := by
      rw [Finset.sum_eq_single b]
      · simp
      · intro a _ ha
        simp [Ne.symm ha]
      · simp [hb]
    exact he.symm.trans h
  exact Cardinal.lt_aleph0_iff_finite.mp (hi.cardinalMk_le_finrank.trans_lt Cardinal.natCast_lt_aleph0)

/-- The dimension of intertwiners from a simple representation into a finite-dimensional one. -/
def constituentMultiplicity (V : FDRep ℂ G) (a : IrreducibleClass G) : ℕ :=
  finrank ℂ (IntertwiningMap (VirtualCharacter.rep a).ρ V.ρ)

private theorem linearPair_character [Fintype G] (V W : FDRep ℂ G) :
    linearPair V.character W.character = (finrank ℂ (IntertwiningMap V.ρ W.ρ) : ℂ) :=
  FiniteCharacter.card_inv_mul_sum_eq_finrank V.ρ W.ρ

/-- Character reciprocity makes intertwining dimensions symmetric. -/
theorem finrank_intertwiningMap_symm [Fintype G] (V W : FDRep ℂ G) :
    finrank ℂ (IntertwiningMap V.ρ W.ρ) = finrank ℂ (IntertwiningMap W.ρ V.ρ) := by
  apply Nat.cast_injective (R := ℂ)
  rw [← FiniteCharacter.card_inv_mul_sum_eq_finrank, ← FiniteCharacter.card_inv_mul_sum_eq_finrank]
  congr 1
  apply Fintype.sum_equiv (Equiv.inv G)
  intro g
  simp [mul_comm]

/-- Every character is the sum of its irreducible characters with their intertwining multiplicities. -/
theorem character_eq_sum_constituentMultiplicity [Fintype G] [Fintype (IrreducibleClass G)]
    (V : FDRep ℂ G) :
    V.character = ∑ a : IrreducibleClass G, constituentMultiplicity V a • (VirtualCharacter.rep a).character := by
  classical
  obtain ⟨c, hc⟩ := VirtualCharacter.irreducibleExpansion_surjective (G := G) (ofClass (classOf V))
  rw [irreducibleExpansion, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype c (fun (a : IrreducibleClass G) (z : ℤ) => z • ofClass a.1)
      (fun _ => zero_smul _ _)] at hc
  have hx := congrArg (virtualCharacter (k := ℂ) (G := G)) hc
  simp only [map_sum, map_zsmul, virtualCharacter_ofClass, character_classOf,
    VirtualCharacter.character_val] at hx
  have hcoeff (b : IrreducibleClass G) : (c b : ℂ) = (constituentMultiplicity V b : ℂ) := by
    have h := congrArg (linearPair (VirtualCharacter.rep b).character) hx
    simp only [map_sum, map_zsmul, linearPair_irreducible] at h
    rw [linearPair_character] at h
    rw [Fintype.sum_eq_single b] at h
    · simpa [constituentMultiplicity, zsmul_eq_mul] using h
    · intro a ha
      simp [Ne.symm ha]
  funext g
  rw [← hx]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  change c a • (VirtualCharacter.rep a).character g =
    constituentMultiplicity V a • (VirtualCharacter.rep a).character g
  rw [zsmul_eq_mul, nsmul_eq_mul, hcoeff]

/-- The intertwining dimension is the dot product of constituent multiplicities. -/
theorem finrank_intertwiningMap_eq_sum_constituentMultiplicity [Fintype G]
    [Fintype (IrreducibleClass G)] (V W : FDRep ℂ G) :
    finrank ℂ (IntertwiningMap V.ρ W.ρ) =
      ∑ a : IrreducibleClass G, constituentMultiplicity V a * constituentMultiplicity W a := by
  apply Nat.cast_injective (R := ℂ)
  rw [Nat.cast_sum]
  have h := congrArg (linearPair V.character) (character_eq_sum_constituentMultiplicity W)
  simp only [map_sum, map_nsmul, linearPair_character] at h
  simp only [nsmul_eq_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro a _
  rw [Nat.cast_mul, finrank_intertwiningMap_symm V (VirtualCharacter.rep a)]
  exact mul_comm _ _

/-- A finite-dimensional representation with endomorphism dimension one is irreducible. -/
theorem isIrreducible_of_finrank_intertwiningMap_self [Fintype G] (V : FDRep ℂ G)
    (h : finrank ℂ (IntertwiningMap V.ρ V.ρ) = 1) : IsIrreducible V.ρ := by
  apply (FiniteCharacter.normOne V.ρ).mp
  rw [FiniteCharacter.card_inv_mul_sum_eq_finrank, h, Nat.cast_one]

end Langlands.FiniteRep
