import Langlands.Representation.Induction.OpenAdjunction
import Langlands.Representation.Smooth.RenardIrreducibleExistenceProof
import Mathlib.RingTheory.Finiteness.Basic

/-! # Ambient irreducibles containing an open-subgroup irreducible -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

open CategoryTheory

namespace Langlands.Induction

universe uR uG uV

variable {R : Type uR} [Field R] {G : Type uG} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (hH : IsOpen (H : Set G))

/-- The translates of the unit image span compact induction from an open subgroup. -/
theorem compactInduced_eq_top_of_unit_mem
    (A : SmoothRep.{uR, uG, uV} R H)
    (S : Subrepresentation (compactInduced H A.representation))
    (hS : ∀ v : A, unitMap H hH A.representation A.isSmooth v ∈ S) :
    S = ⊤ := by
  apply top_unique
  intro f _
  rw [← cosetSum_unitMap H hH A.representation A.isSmooth f, cosetSum_apply]
  apply finsum_induction (fun x => x ∈ S.toSubmodule) S.toSubmodule.zero_mem
    (fun _ _ => S.toSubmodule.add_mem)
  intro q
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact S.apply_mem_toSubmodule x⁻¹ (hS (eval H A.representation f.1 x))

/-- Compact induction of an irreducible representation of an open subgroup is cyclic. -/
theorem compactInduced_span_unit_eq_top
    (A : SmoothRep.{uR, uG, uV} R H) (hA : A.IsIrreducible)
    (v : A) (hv : v ≠ 0) :
    Submodule.span (MonoidAlgebra R G)
      { (compactInduced H A.representation).asModuleEquiv.symm
          (unitMap H hH A.representation A.isSmooth v) } = ⊤ := by
  let U := unitMap H hH A.representation A.isSmooth
  let N := Submodule.span (MonoidAlgebra R G)
    {(compactInduced H A.representation).asModuleEquiv.symm (U v)}
  let S : Subrepresentation (compactInduced H A.representation) :=
    Subrepresentation.ofSubmodule' N
  let P : Subrepresentation A.representation :=
    { toSubmodule := S.toSubmodule.comap U.toLinearMap
      apply_mem_toSubmodule h w hw := by
        change U (A.representation h w) ∈ S
        rw [U.isIntertwining]
        exact S.apply_mem_toSubmodule (h : G) hw }
  have hvP : v ∈ P := Submodule.subset_span (Set.mem_singleton _)
  have hP : P = ⊤ := by
    rcases hA.eq_bot_or_eq_top P with hp | hp
    · exfalso
      apply hv
      change v ∈ (⊥ : Subrepresentation A.representation)
      rw [← hp]
      exact hvP
    · exact hp
  have hS : S = ⊤ := compactInduced_eq_top_of_unit_mem H hH A S (fun w => by
    change w ∈ P
    rw [hP]
    exact Submodule.mem_top)
  exact congrArg Subrepresentation.asSubmodule hS

include hH in
/-- The induced module is finitely generated over the ambient group algebra. -/
theorem finite_compactInduced_of_irreducible
    (A : SmoothRep.{uR, uG, uV} R H) (hA : A.IsIrreducible) :
    Module.Finite (MonoidAlgebra R G) (compactInduced H A.representation).asModule := by
  classical
  have : A.representation.IsIrreducible := hA
  have : Nontrivial A := IsSimpleModule.nontrivial
    (MonoidAlgebra R H) A.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  rw [Module.finite_def]
  rw [← compactInduced_span_unit_eq_top H hH A hA v hv]
  exact Submodule.fg_span_singleton _

/-- An ambient irreducible and an actual embedding of the subgroup representation
into its restriction. The ambient carrier has the size needed by compact induction. -/
structure OpenIrreducibleExtension
    (A : SmoothRep.{uR, uG, max uG uV} R H) where
  obj : SmoothRep.{uR, uG, max uG uV} R G
  irreducible : obj.IsIrreducible
  embedding : A ⟶ (smoothRestriction R H).obj obj
  injective : Function.Injective (SmoothRep.hom embedding)

/-- Choose an irreducible quotient of compact induction and use open Frobenius
reciprocity to embed the given irreducible into its restriction. -/
def openIrreducibleExtension
    (A : SmoothRep.{uR, uG, max uG uV} R H) (hA : A.IsIrreducible) :
    OpenIrreducibleExtension H A := by
  classical
  apply Classical.choice
  let I := (smoothCompactInduction R H).obj A
  have : A.representation.IsIrreducible := hA
  have : Nontrivial A := IsSimpleModule.nontrivial
    (MonoidAlgebra R H) A.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  have hU : Function.Injective (unitMap H hH A.representation A.isSmooth) := by
    intro a b hab
    simpa only [unitMap_apply, eval_unitFunction_one] using
      congrArg (fun f => eval H A.representation f.1 1) hab
  have : Nontrivial I :=
    Function.Injective.nontrivial hU
  have : Module.Finite (MonoidAlgebra R G) I.representation.asModule :=
    finite_compactInduced_of_irreducible H hH A hA
  have hco : IsCoatomic (Subrepresentation I.representation) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso
      (ρ := I.representation)).isCoatomic_iff.mpr inferInstance
  obtain ⟨S, hS⟩ : ∃ S : Subrepresentation I.representation, IsCoatom S := by
    rcases hco.eq_top_or_exists_le_coatom ⊥ with hbot | ⟨S, hS, _⟩
    · exfalso
      obtain ⟨f, hf⟩ := exists_ne (0 : I)
      apply hf
      change f ∈ (⊥ : Subrepresentation I.representation)
      rw [hbot]
      exact Submodule.mem_top
    · exact ⟨S, hS⟩
  let B := SmoothRep.quotient I S
  let q := SmoothRep.mkQ I S
  have hB : B.IsIrreducible :=
    SmoothRep.RenardIrreducibleExistence.quotient_isIrreducible_of_isCoatom I S hS
  let e := compactInductionHomEquiv H hH A B q
  have he : SmoothRep.hom e ≠ 0 := by
    intro he
    have he0 : e = 0 := congrArg SmoothRep.ofHom he
    have hq0 : q = 0 := by
      apply (compactInductionHomEquiv H hH A B).injective
      simpa only [e, he0] using
        (show compactInductionHomEquiv H hH A B (0 : I ⟶ B) = 0 from rfl).symm
    have : B.representation.IsIrreducible := hB
    have : Nontrivial B := IsSimpleModule.nontrivial
      (MonoidAlgebra R G) B.representation.asModule
    obtain ⟨b, hb⟩ := exists_ne (0 : B)
    obtain ⟨a, ha⟩ := SmoothRep.mkQ_surjective I S b
    apply hb
    rw [← ha]
    exact congrArg (fun f : I ⟶ B => SmoothRep.hom f a) hq0
  exact ⟨⟨B, hB, e,
    (Representation.IsIrreducible.injective_or_eq_zero (SmoothRep.hom e)).resolve_right he⟩⟩

end Langlands.Induction
