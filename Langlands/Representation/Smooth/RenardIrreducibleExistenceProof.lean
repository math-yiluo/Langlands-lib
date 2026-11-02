import Langlands.Representation.Smooth.RenardIrreducibleExistenceStatement
import Langlands.CategoryTheory.Renard.SimpleQuotient
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Proof of the three irreducible-existence assertions of Renard III.1.4

The categorical finite-type and composition-chain hypotheses are used directly.
The unrestricted subquotient is a simple quotient of a cyclic subrepresentation.
Its cyclic route generalizes Worker 379's complex-coefficient proof.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace Langlands.SmoothRep

universe uK uG uV

variable {k : Type uK} {G : Type uG}
variable [Field k] [Group G] [TopologicalSpace G]

namespace RenardIrreducibleExistence

/-- A nontrivial carrier gives a nonzero object in the actual smooth category. -/
theorem not_isZero (A : SmoothRep.{uK, uG, uV} k G) [Nontrivial A] :
    ¬ Limits.IsZero A := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  have he := congrArg (fun f : A ⟶ A => hom f v) (h.eq_of_src (𝟙 A) 0)
  exact hv he

/-- Categorical simplicity implies irreducibility of the actual group action. -/
theorem isIrreducible_of_simple (A : SmoothRep.{uK, uG, uV} k G) [Simple A] :
    A.IsIrreducible := by
  refine
    { exists_pair_ne := ⟨⊥, ⊤, ?_⟩
      eq_bot_or_eq_top := ?_ }
  · intro h
    apply id_nonzero A
    ext v
    have hv : v ∈ (⊥ : Subrepresentation A.representation) := by
      rw [h]
      exact Submodule.mem_top
    exact hv
  · intro S
    let i := subtype A S
    have : Mono i := (mono_iff_injective i).mpr (subtype_injective A S)
    by_cases hi : i = 0
    · left
      apply SetLike.ext
      intro v
      constructor
      · intro hv
        have he := congrArg (fun f : subrepresentation A S ⟶ A => hom f ⟨v, hv⟩) hi
        exact he
      · intro hv
        exact hv ▸ S.toSubmodule.zero_mem
    · right
      have : IsIso i := isIso_of_mono_of_nonzero hi
      have hs := (epi_iff_surjective i).mp inferInstance
      apply SetLike.ext
      intro v
      constructor
      · intro _
        exact Submodule.mem_top
      · intro _
        obtain ⟨w, hw⟩ := hs v
        exact hw ▸ w.property

/-- A maximal proper invariant submodule has an irreducible actual quotient. -/
theorem quotient_isIrreducible_of_isCoatom
    (A : SmoothRep.{uK, uG, uV} k G)
    (S : Subrepresentation A.representation) (hS : IsCoatom S) :
    (quotient A S).IsIrreducible := by
  let f : A.representation.asModule →ₗ[k[G]] (quotient A S).representation.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule _ _ (hom (mkQ A S))
  have hf : Function.Surjective f := mkQ_surjective A S
  have hker : f.ker = S.asSubmodule := by
    ext v
    exact Submodule.Quotient.mk_eq_zero S.toSubmodule
  have hco : IsCoatom S.asSubmodule :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso.isCoatom_iff S).mpr hS
  have hs : IsSimpleModule k[G] (A.representation.asModule ⧸ f.ker) := by
    rw [hker]
    exact isSimpleModule_iff_isCoatom.mpr hco
  exact (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
    ((f.quotKerEquivOfSurjective hf).isSimpleModule_iff.mp hs)

/-- The cyclic subrepresentation of a nonzero vector has an irreducible quotient.
All subobjects and quotients retain the ambient carrier universe. -/
theorem exists_irreducible_subquotient
    (A : SmoothRep.{uK, uG, uV} k G) [Nontrivial A] :
    ∃ B : SmoothRep.{uK, uG, uV} k G, B.IsIrreducible ∧ IsSubquotient B A := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  let N : Submodule k[G] A.representation.asModule :=
    Submodule.span (M := A.representation.asModule) k[G]
      {A.representation.asModuleEquiv.symm v}
  let S : Subrepresentation A.representation := Subrepresentation.ofSubmodule' N
  let B := subrepresentation A S
  have hvS : v ∈ S := by
    change A.representation.asModuleEquiv.symm v ∈ N
    exact Submodule.subset_span (Set.mem_singleton _)
  let v' : B := ⟨v, hvS⟩
  have hv' : v' ≠ 0 := fun h => hv (congrArg Subtype.val h)
  have : Nontrivial B := ⟨⟨v', 0, hv'⟩⟩
  let j : B.representation.asModule →ₗ[k[G]] N :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (hom (subtype A S))).codRestrict N (fun w => w.property)
  have hj : Function.Bijective j :=
    ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h),
      fun w => ⟨⟨w.val, w.property⟩, rfl⟩⟩
  have : Module.Finite k[G] N := Module.Finite.span_of_finite _ (Set.finite_singleton _)
  have : Module.Finite k[G] B.representation.asModule :=
    Module.Finite.equiv (LinearEquiv.ofBijective j hj).symm
  have hco : IsCoatomic (Subrepresentation B.representation) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso
      (ρ := B.representation)).isCoatomic_iff.mpr inferInstance
  rcases hco.eq_top_or_exists_le_coatom ⊥ with h | ⟨T, hT, _⟩
  · exfalso
    apply hv'
    have hmem : v' ∈ (⊥ : Subrepresentation B.representation) := by
      rw [h]
      exact Submodule.mem_top
    exact hmem
  · exact ⟨quotient B T, quotient_isIrreducible_of_isCoatom B T hT,
      S, T, ⟨Iso.refl _⟩⟩

/-- Source categorical finite type gives an actual irreducible smooth quotient. -/
theorem exists_irreducible_quotient_of_finiteType
    (A : SmoothRep.{uK, uG, uV} k G) [Nontrivial A]
    (hA : Langlands.Renard.IsFiniteTypeObject A) :
    ∃ B : SmoothRep.{uK, uG, uV} k G, B.IsIrreducible ∧ IsQuotient B A := by
  obtain ⟨P, _, hP⟩ :=
    Langlands.Renard.exists_simple_cokernel_of_finiteType (not_isZero A) hA
  let B := Limits.cokernel P.arrow
  have : Simple B := hP
  exact ⟨B, isIrreducible_of_simple B,
    Limits.cokernel.π P.arrow,
    (epi_iff_surjective (Limits.cokernel.π P.arrow)).mp inferInstance⟩

/-- The first step of a nonzero finite composition chain is an irreducible
actual smooth subrepresentation. -/
theorem exists_irreducible_subrepresentation_of_finiteLength
    (A : SmoothRep.{uK, uG, uV} k G) [Nontrivial A]
    (hA : Langlands.Renard.IsFiniteLength A) :
    ∃ B : SmoothRep.{uK, uG, uV} k G,
      B.IsIrreducible ∧ IsSubrepresentation B A := by
  obtain ⟨n, ⟨c⟩⟩ := hA
  have hn : 0 < n := by
    by_contra h
    have hn : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    exact not_isZero A
      ((Langlands.Renard.hasCompositionChainOfLength_zero_iff A).mp ⟨c⟩)
  let i : Fin n := ⟨0, hn⟩
  have hc := (Langlands.Renard.simple_cokernel_ofLE_iff_covBy
    _ _ (c.le_succ i)).mp (c.simple_factor i)
  have hc0 : c.subobject i.castSucc = ⊥ := c.subobject_zero
  rw [hc0] at hc
  have hs : Simple (c.subobject i.succ : SmoothRep.{uK, uG, uV} k G) :=
    (subobject_simple_iff_isAtom _).mpr hc.is_atom
  have := hs
  exact ⟨_, isIrreducible_of_simple _, (c.subobject i.succ).arrow,
    (mono_iff_injective (c.subobject i.succ).arrow).mp inferInstance⟩

end RenardIrreducibleExistence

/-- The exact three irreducible-existence assertions of Renard III.1.4. -/
theorem renardIrreducibleExistence :
    RenardIrreducibleExistenceStatement.{uK, uG, uV} (k := k) (G := G) := by
  intro _ A hA
  let := hA
  exact ⟨RenardIrreducibleExistence.exists_irreducible_subquotient A,
    RenardIrreducibleExistence.exists_irreducible_quotient_of_finiteType A,
    RenardIrreducibleExistence.exists_irreducible_subrepresentation_of_finiteLength A⟩

end Langlands.SmoothRep
