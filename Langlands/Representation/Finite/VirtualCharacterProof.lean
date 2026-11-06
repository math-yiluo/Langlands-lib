import Langlands.Representation.Finite.BrauerStatement
import Langlands.Representation.Finite.CharacterTheoryProof

/-!
# Faithfulness of virtual characters and the irreducible basis

Proofs of `Langlands.FiniteRep.FiniteVirtualCharacterFaithfulnessStatement` and
`Langlands.FiniteRep.FiniteIrreducibleBasisStatement`.
-/

noncomputable section

namespace Langlands.FiniteRep.VirtualCharacter

open Module

universe uG

variable {G : Type uG} [Group G] [Fintype G]

section Faithfulness

/-- Representations with equal characters have equal isomorphism classes. -/
theorem classOf_eq_of_character_eq {V W : FDRep ℂ G} (h : V.character = W.character) :
    classOf V = classOf W :=
  (classOf_eq_iff V W).mpr
    ⟨isoOfEquiv ((FiniteCharacter.isomorphism (G := G) (V := V) (W := W) V.ρ W.ρ).mp h).some⟩

theorem eq_of_character_eq {a b : RepClass ℂ G} (h : character a = character b) : a = b := by
  induction a using Quotient.inductionOn with | h V =>
  induction b using Quotient.inductionOn with | h W =>
  exact classOf_eq_of_character_eq h

theorem faithfulness : FiniteVirtualCharacterFaithfulnessStatement G := by
  change Function.Injective (virtualCharacter (k := ℂ) (G := G))
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨a, b, rfl⟩ := virtualRep_exists_difference x
  rw [map_sub, virtualCharacter_ofClass, virtualCharacter_ofClass, sub_eq_zero] at hx
  rw [eq_of_character_eq hx, sub_self]

end Faithfulness

section Pairing

/-- The normalized character pairing `|G|⁻¹ ∑ f(g⁻¹) h(g)`, additive in `h`. -/
def pairing (f : G → ℂ) : (G → ℂ) →+ ℂ where
  toFun h := (Fintype.card G : ℂ)⁻¹ * ∑ g : G, f g⁻¹ * h g
  map_zero' := by simp
  map_add' h₁ h₂ := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- A chosen irreducible representative of an irreducible class. -/
def rep (a : IrreducibleClass G) : FDRep ℂ G := a.2.choose

omit [Fintype G] in
theorem classOf_rep (a : IrreducibleClass G) : classOf (rep a) = a.1 := a.2.choose_spec.1

omit [Fintype G] in
theorem isIrreducible_rep (a : IrreducibleClass G) : Representation.IsIrreducible (rep a).ρ :=
  a.2.choose_spec.2

omit [Fintype G] in
theorem character_val (a : IrreducibleClass G) : character a.1 = (rep a).character := by
  rw [← character_classOf, classOf_rep]

open Classical in
/-- Orthonormality of the characters of irreducible classes. -/
theorem pairing_irreducible (a b : IrreducibleClass G) :
    pairing (character b.1) (character a.1) = if b = a then 1 else 0 := by
  have ho := FiniteCharacter.orthogonality (G := G) (V := rep b) (W := rep a) (rep b).ρ (rep a).ρ
    (isIrreducible_rep b) (isIrreducible_rep a)
  have hiff : b = a ↔ Nonempty (Representation.Equiv (rep b).ρ (rep a).ρ) := by
    have h1 : b = a ↔ classOf (rep b) = classOf (rep a) := by
      rw [classOf_rep, classOf_rep]
      exact Subtype.ext_iff
    rw [h1, classOf_eq_iff]
    exact ⟨fun ⟨e⟩ => ⟨equivOfIso e⟩, fun ⟨e⟩ => ⟨isoOfEquiv e⟩⟩
  change (Fintype.card G : ℂ)⁻¹ * ∑ g : G, character b.1 g⁻¹ * character a.1 g = _
  rw [character_val b, character_val a]
  split_ifs with h
  · exact ho.1 (hiff.mp h)
  · exact ho.2 (mt hiff.mpr h)

end Pairing

section Basis

theorem irreducibleExpansion_injective : Function.Injective (irreducibleExpansion G) := by
  classical
  have hli : LinearIndependent ℤ (fun a : IrreducibleClass G => character a.1) := by
    rw [linearIndependent_iff']
    intro s c hs b hb
    have h := congrArg (pairing (character b.1)) hs
    rw [map_zero, map_sum] at h
    simp only [map_zsmul, pairing_irreducible] at h
    simp only [smul_ite, smul_zero, Finset.sum_ite_eq, hb, ite_true, zsmul_eq_mul, mul_one,
      Int.cast_eq_zero] at h
    exact h
  have hli' : LinearIndependent ℤ (fun a : IrreducibleClass G => ofClass (k := ℂ) a.1) := by
    apply LinearIndependent.of_comp (virtualCharacter (k := ℂ) (G := G))
    simpa only [Function.comp_def, virtualCharacter_ofClass] using hli
  exact hli'

/-- Irreducibility is invariant under equivalence, by the norm-one criterion. -/
theorem isIrreducible_of_equiv {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : Representation.Equiv ρ σ)
    (h : Representation.IsIrreducible ρ) : Representation.IsIrreducible σ := by
  rw [← FiniteCharacter.normOne (G := G) (V := W) σ, ← Representation.char_iso e]
  exact (FiniteCharacter.normOne (G := G) (V := V) ρ).mpr h

/-- Every actual class lies in the span of the irreducible classes, by strong induction on
the dimension, splitting off an irreducible subrepresentation. -/
theorem ofClass_mem_range (n : ℕ) :
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ G V), finrank ℂ V = n →
      ofClass (classOfRepresentation ρ) ∈ LinearMap.range (irreducibleExpansion G) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ ρ hn
  have : NeZero (Nat.card G : ℂ) := FiniteCharacter.neZero_card
  by_cases h0 : finrank ℂ V = 0
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0
    have hz : classOfRepresentation ρ = 0 :=
      (classOfRepresentation_congr (σ := (zeroRep (k := ℂ) (G := G)).ρ)
        (Representation.Equiv.mk (LinearEquiv.ofSubsingleton _ _) fun g =>
          LinearMap.ext fun _ => Subsingleton.elim _ _)).trans (classOfRepresentation_rho _)
    rw [hz, map_zero]
    exact Submodule.zero_mem _
  obtain ⟨T, hT⟩ := FiniteCharacter.exists_isAtom ρ h0
  have hirr : T.toRepresentation.IsIrreducible :=
    FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom T hT
  obtain ⟨C, hC⟩ := exists_isCompl T
  have hsplit : classOfRepresentation ρ =
      classOfRepresentation T.toRepresentation + classOfRepresentation C.toRepresentation :=
    (classOfRepresentation_congr (FiniteCharacter.prodEquivOfIsCompl hC).symm).trans
      (classOfRepresentation_prod _ _)
  rw [hsplit, map_add]
  refine Submodule.add_mem _ ?_ ?_
  · let a : IrreducibleClass G := ⟨classOfRepresentation T.toRepresentation,
      ofRepresentation T.toRepresentation, rfl,
      isIrreducible_of_equiv (modelEquiv T.toRepresentation) hirr⟩
    refine LinearMap.mem_range.mpr ⟨Finsupp.single a 1, ?_⟩
    rw [irreducibleExpansion_single, one_smul]
  · have hdim : finrank ℂ C.toSubmodule < n := by
      have h1 := Submodule.finrank_add_eq_of_isCompl (FiniteCharacter.isCompl_toSubmodule hC)
      have h2 : finrank ℂ T.toSubmodule ≠ 0 := by
        rw [Ne, Submodule.finrank_eq_zero]
        exact FiniteCharacter.toSubmodule_ne_bot hT.1
      omega
    exact ih _ hdim C.toRepresentation rfl

theorem irreducibleExpansion_surjective : Function.Surjective (irreducibleExpansion G) := by
  intro x
  obtain ⟨a, b, rfl⟩ := virtualRep_exists_difference x
  have hmem (a : RepClass ℂ G) : ofClass a ∈ LinearMap.range (irreducibleExpansion G) := by
    induction a using Quotient.inductionOn with | h V =>
    have h := ofClass_mem_range (G := G) _ V.ρ rfl
    rw [classOfRepresentation_rho] at h
    exact h
  exact LinearMap.mem_range.mp (Submodule.sub_mem _ (hmem a) (hmem b))

theorem irreducibleBasis : FiniteIrreducibleBasisStatement G :=
  ⟨irreducibleExpansion_injective, irreducibleExpansion_surjective⟩

end Basis

/-- The faithfulness and irreducible-basis conjuncts of Henniart's finite Brauer input. -/
theorem faithfulnessAndBasis (G : Type uG) [Group G] [Fintype G] :
    FiniteVirtualCharacterFaithfulnessStatement G ∧ FiniteIrreducibleBasisStatement G :=
  ⟨faithfulness, irreducibleBasis⟩

end Langlands.FiniteRep.VirtualCharacter
