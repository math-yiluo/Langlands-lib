import Langlands.Representation.FiniteGeneralLinear.FiniteCharacterMultiplicity
import Langlands.Representation.FiniteGeneralLinear.FiniteProductCharacters

/-! Irreducible external tensor products for finite groups. -/

noncomputable section

open Module Representation
open scoped BigOperators

namespace Langlands.FiniteRep

section Regular

variable {H : Type*} [Group H] [Fintype H]

private instance regularFinite : Module.Finite ℂ (MonoidAlgebra ℂ H) :=
  Module.Finite.equiv ((Finsupp.linearEquivFunOnFinite ℂ ℂ H).symm.trans
    (MonoidAlgebra.coeffLinearEquiv ℂ).symm)

/-- A finite-dimensional model of the complex left regular representation. -/
def regularRep (H : Type*) [Group H] [Fintype H] : FDRep ℂ H :=
  ofRepresentation (Representation.leftRegular ℂ H)

open Classical in
/-- The trace of the regular action counts fixed basis elements. -/
theorem character_regularRep (g : H) : (regularRep H).character g =
    if g = 1 then (Fintype.card H : ℂ) else 0 := by
  classical
  have h := congrFun (Representation.char_iso (modelEquiv (Representation.leftRegular ℂ H))) g
  change (Representation.leftRegular ℂ H).character g = (regularRep H).character g at h
  rw [← h]
  let b : Basis H ℂ (MonoidAlgebra ℂ H) :=
    (Finsupp.basisSingleOne : Basis H ℂ (H →₀ ℂ)).map (MonoidAlgebra.coeffLinearEquiv ℂ).symm
  rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, b, Basis.map_apply,
    Finsupp.coe_basisSingleOne, Basis.map_repr, LinearEquiv.symm_symm]
  change (∑ x : H, ((Representation.leftRegular ℂ H) g (MonoidAlgebra.single x 1)).coeff x) = _
  simp only [Representation.ofMulAction_single, smul_eq_mul]
  change (∑ x : H, Finsupp.single (g * x) (1 : ℂ) x) = _
  simp only [Finsupp.single_apply, mul_eq_right]
  by_cases hg : g = 1 <;> simp [hg]

end Regular

section Product

variable {ι : Type} [Fintype ι] {G : ι → Type*} [∀ i, Group (G i)] [∀ i, Fintype (G i)]

/-- An external tensor of irreducibles is irreducible, by the product formula for endomorphisms. -/
theorem isIrreducible_externalRep (V : ∀ i, FDRep ℂ (G i))
    (hV : ∀ i, IsIrreducible (V i).ρ) : IsIrreducible (externalRep V).ρ := by
  classical
  apply isIrreducible_of_finrank_intertwiningMap_self
  rw [finrank_intertwiningMap_externalRep]
  apply Finset.prod_eq_one
  intro i _
  let : IsIrreducible (V i).ρ := hV i
  exact IsIrreducible.finrank_intertwiningMap_self (V i).ρ

/-- The regular character of a product is the product of the regular characters. -/
private theorem character_external_regular [DecidableEq ι] (g : ∀ i, G i) :
    (externalRep (fun i => regularRep (G i))).character g = (regularRep (∀ i, G i)).character g := by
  classical
  rw [character_externalRep, character_regularRep]
  simp_rw [character_regularRep]
  by_cases hg : g = 1
  · subst g
    simp [Fintype.card_pi, Nat.cast_prod]
  · obtain ⟨i, hi⟩ : ∃ i, g i ≠ 1 := by
      by_contra! h
      exact hg (funext h)
    rw [ite_eq_right hg]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

/-- Every irreducible representation of a product of finite groups is an external tensor
of irreducible representations of the individual groups. -/
theorem exists_externalRep_equiv (W : FDRep ℂ (∀ i, G i)) (hW : IsIrreducible W.ρ) :
    ∃ a : ∀ i, IrreducibleClass (G i),
      Nonempty (Representation.Equiv W.ρ (externalRep (fun i => VirtualCharacter.rep (a i))).ρ) := by
  classical
  let : ∀ i, Fintype (IrreducibleClass (G i)) := fun i => Fintype.ofFinite _
  let A := externalRep (fun i => regularRep (G i))
  let T (a : ∀ i, IrreducibleClass (G i)) := externalRep (fun i => VirtualCharacter.rep (a i))
  let c (a : ∀ i, IrreducibleClass (G i)) :=
    ∏ i, constituentMultiplicity (regularRep (G i)) (a i)
  have hA : A.character = ∑ a : ∀ i, IrreducibleClass (G i), c a • (T a).character := by
    funext g
    let s (i : ι) (a : IrreducibleClass (G i)) :=
      (constituentMultiplicity (regularRep (G i)) a : ℂ) * (VirtualCharacter.rep a).character (g i)
    calc
      A.character g = ∏ i, (regularRep (G i)).character (g i) := character_externalRep _ _
      _ = ∏ i, ∑ a, s i a := by
        apply Finset.prod_congr rfl
        intro i _
        have h := congrFun (character_eq_sum_constituentMultiplicity (regularRep (G i))) (g i)
        simpa only [Finset.sum_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, s] using h
      _ = ∑ a : ∀ i, IrreducibleClass (G i), ∏ i, s i (a i) := Fintype.prod_sum s
      _ = _ := by
        simp only [Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro a _
        change (∏ i, s i (a i)) = c a • (T a).character g
        rw [character_externalRep]
        simp only [c, s, Finset.prod_mul_distrib, nsmul_eq_mul, Nat.cast_prod]
  by_contra h
  have hz (a : ∀ i, IrreducibleClass (G i)) :
      VirtualCharacter.pairing W.character (T a).character = 0 :=
    (FiniteCharacter.orthogonality W.ρ (T a).ρ hW
      (isIrreducible_externalRep _ (fun i => VirtualCharacter.isIrreducible_rep (a i)))).2
        (fun he => h ⟨a, he⟩)
  have hp := congrArg (VirtualCharacter.pairing W.character) hA
  simp only [map_sum, map_nsmul, hz, nsmul_zero, Finset.sum_const_zero] at hp
  change ((Fintype.card (∀ i, G i) : ℂ)⁻¹ * ∑ g, W.character g⁻¹ * A.character g) = 0 at hp
  simp only [A, character_external_regular, character_regularRep] at hp
  rw [Fintype.sum_eq_single (1 : ∀ i, G i)] at hp
  · have hn : (Fintype.card (∀ i, G i) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hnW : finrank ℂ W ≠ 0 := by
      intro he
      have : Subsingleton W := Module.finrank_zero_iff.mp he
      obtain ⟨x, hx⟩ := FiniteIndexRestriction.exists_ne_zero W.ρ hW
      exact hx (Subsingleton.elim _ _)
    have hχ : W.character 1 = (finrank ℂ W : ℂ) := Representation.char_one W.ρ
    simp only [inv_one, hχ] at hp
    have he := (mul_eq_zero.mp hp).resolve_left (inv_ne_zero hn)
    exact (Nat.cast_ne_zero.mpr hnW) ((mul_eq_zero.mp he).resolve_right hn)
  · intro g hg
    simp [hg]

/-- A nonzero intertwining dimension between two external irreducible tensors forces an
equivalence in each coordinate. -/
theorem factors_equiv_of_intertwiningMap_externalRep_ne_zero
    (V W : ∀ i, FDRep ℂ (G i)) (hV : ∀ i, IsIrreducible (V i).ρ) (hW : ∀ i, IsIrreducible (W i).ρ)
    (h : finrank ℂ (IntertwiningMap (externalRep V).ρ (externalRep W).ρ) ≠ 0) :
    ∀ i, Nonempty (Representation.Equiv (V i).ρ (W i).ρ) := by
  classical
  rw [finrank_intertwiningMap_externalRep] at h
  intro i
  by_contra he
  have hz := (FiniteCharacter.orthogonality (V i).ρ (W i).ρ (hV i) (hW i)).2 he
  rw [FiniteCharacter.card_inv_mul_sum_eq_finrank, Nat.cast_eq_zero] at hz
  exact h (Finset.prod_eq_zero (Finset.mem_univ i) hz)

end Product

end Langlands.FiniteRep
