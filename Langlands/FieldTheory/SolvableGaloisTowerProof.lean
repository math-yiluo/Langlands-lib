import Langlands.FieldTheory.SolvableGaloisTowerStatement
import Mathlib.GroupTheory.QuotientGroup.Simple
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Order.Atoms.Finite

namespace Langlands.FieldTheory

universe u v

open IntermediateField

private theorem exists_prime_quotient (G : Type*) [Group G] [Finite G]
    [Nontrivial G] [Group.IsSolvable G] :
    ∃ H : Subgroup G, ∃ _ : H.Normal,
      IsCyclic (G ⧸ H) ∧ Nat.Prime (Nat.card (G ⧸ H)) := by
  let A := Abelianization G
  have : Nontrivial A := QuotientGroup.nontrivial_iff.mpr
    (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := G)).ne
  have : Finite A := inferInstanceAs (Finite (Abelianization G))
  have : Finite (Subgroup A) := Finite.of_injective
    (fun H : Subgroup A => (H : Set A)) SetLike.coe_injective
  obtain ⟨M, hM⟩ := IsCoatomic.exists_coatom (α := Subgroup A)
  have : IsSimpleGroup (A ⧸ M) := CommGroup.isSimpleGroup_iff_isCoatom.mpr hM
  let f : G →* A ⧸ M := (QuotientGroup.mk' M).comp Abelianization.of
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective M).comp (QuotientGroup.mk'_surjective (commutator G))
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  refine ⟨f.ker, inferInstance, e.isCyclic.mpr inferInstance, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact IsSimpleGroup.prime_card

private def PrimeStep {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (A B : IntermediateField K L) : Prop :=
  ∃ h : A ≤ B,
    letI : Algebra A B := (IntermediateField.inclusion h).toAlgebra
    FiniteDimensional A B ∧ IsGalois A B ∧ IsCyclic (B ≃ₐ[A] B) ∧
      Nat.Prime (Module.finrank A B)

private theorem exists_prime_step (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Group.IsSolvable Gal(L/K)] (A : IntermediateField K L) (hA : A ≠ ⊤) :
    ∃ B : IntermediateField K L, A < B ∧ PrimeStep A B := by
  have hn : A.fixingSubgroup ≠ ⊥ := by
    intro h
    have := congrArg IntermediateField.fixedField h
    exact hA (by simpa only [IsGalois.fixedField_fixingSubgroup, fixedField_bot] using this)
  have : Nontrivial A.fixingSubgroup := A.fixingSubgroup.nontrivial_iff_ne_bot.mpr hn
  have : Nontrivial Gal(L/A) := A.fixingSubgroupEquiv.symm.toEquiv.nontrivial
  have : Group.IsSolvable Gal(L/A) := Group.isSolvable_of_surjective
    (f := A.fixingSubgroupEquiv.toMonoidHom) A.fixingSubgroupEquiv.surjective
  obtain ⟨H, hH, hcyc, hp⟩ := exists_prime_quotient Gal(L/A)
  let F := IntermediateField.fixedField H
  have : IsCyclic Gal(F/A) := (IsGalois.normalAutEquivQuotient H).isCyclic.mp hcyc
  have hprime : Nat.Prime (Module.finrank A F) := by
    rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_congr
      (IsGalois.normalAutEquivQuotient H).toEquiv]
    exact hp
  let B := F.restrictScalars K
  have hAB : A ≤ B := fun x hx => F.algebraMap_mem ⟨x, hx⟩
  have hlt : A < B := lt_of_le_not_ge hAB (by
    intro hBA
    apply hprime.ne_one
    apply IntermediateField.finrank_eq_one_iff.mpr
    apply le_antisymm _ bot_le
    intro x hx
    exact ⟨⟨x, hBA hx⟩, rfl⟩)
  refine ⟨B, hlt, hAB, ?_⟩
  change FiniteDimensional A F ∧ IsGalois A F ∧ IsCyclic Gal(F/A) ∧
    Nat.Prime (Module.finrank A F)
  exact ⟨inferInstance, inferInstance, inferInstance, hprime⟩

private theorem exists_tower_from (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Group.IsSolvable Gal(L/K)] (A : IntermediateField K L) :
    ∃ (n : ℕ) (T : Fin (n + 1) → IntermediateField K L),
      T 0 = A ∧ T (Fin.last n) = ⊤ ∧
        ∀ i : Fin n, PrimeStep (T i.castSucc) (T i.succ) := by
  induction A using
      (measure fun A : IntermediateField K L => Module.finrank A L).wf.induction with
  | h A ih =>
    by_cases hA : A = ⊤
    · exact ⟨0, fun _ => A, rfl, hA, Fin.elim0⟩
    · obtain ⟨B, hAB, hstep⟩ := exists_prime_step K L A hA
      obtain ⟨n, T, h0, hlast, hsteps⟩ :=
        ih B (IntermediateField.finrank_lt_of_gt hAB)
      refine ⟨n + 1, Fin.cons A T, Fin.cons_zero _ _, ?_, ?_⟩
      · simpa only [Fin.cons_last] using hlast
      · intro i
        cases i using Fin.cases with
        | zero => simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, h0]
            using hstep
        | succ i => simpa only [Fin.castSucc_succ, Fin.cons_succ] using hsteps i

/-- A finite solvable Galois extension has a tower of actual intermediate
fields whose consecutive inclusion extensions are cyclic Galois of prime degree. -/
theorem solvableGaloisPrimeTower : SolvableGaloisPrimeTower.{u,v} := by
  intro K L _ _ _ _ _ _
  exact exists_tower_from K L ⊥

end Langlands.FieldTheory
