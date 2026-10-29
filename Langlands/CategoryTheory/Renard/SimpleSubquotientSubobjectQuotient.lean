import Langlands.CategoryTheory.Renard.SimpleSubquotientIdentitiesStatements
import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# Simple subquotients of a subobject and quotient

Proof of clause (i) of Renard A.VI.3's unnumbered Lemma, printed264/PDF270
of the French edition dated 9 July 2026. The internal transports hold in
every abelian category; the exact public target retains both source
antecedents and independent family, Hom and object universes.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An actual mono/epi presentation gives a simple subquotient class. -/
theorem objectClass_mem_simpleSubquotientClasses_of_mono_epi
    {X M S : C} (m : M ⟶ X) [Mono m] (p : M ⟶ S) [Epi p] [Simple S] :
    objectClass S ∈ simpleSubquotientClasses X := by
  let A : Subobject X := Subobject.mk (kernel.ι p ≫ m)
  let B : Subobject X := Subobject.mk m
  have h : A ≤ B := Subobject.mk_le_mk_of_comm (kernel.ι p) rfl
  have hw : Subobject.ofLE A B h ≫ (Subobject.underlyingIso m).hom =
      (Subobject.underlyingIso (kernel.ι p ≫ m)).hom ≫ kernel.ι p := by
    rw [← cancel_mono m]
    simp [A, B]
  let e : cokernel (Subobject.ofLE A B h) ≅ S :=
    cokernel.mapIso _ (kernel.ι p)
      (Subobject.underlyingIso (kernel.ι p ≫ m)) (Subobject.underlyingIso m) hw ≪≫
        asIso (Abelian.factorThruCoimage p)
  exact ⟨A, B, h, Simple.of_iso e, objectClass_eq_iff.mpr ⟨e⟩⟩

/-- Simple subquotient classes transport along a monomorphism. -/
theorem simpleSubquotientClasses_subset_of_mono
    {X Y : C} (m : X ⟶ Y) [Mono m] :
    simpleSubquotientClasses X ⊆ simpleSubquotientClasses Y := by
  rintro q ⟨A, B, h, hs, rfl⟩
  have := hs
  exact objectClass_mem_simpleSubquotientClasses_of_mono_epi
    (B.arrow ≫ m) (cokernel.π (Subobject.ofLE A B h))

/-- Simple subquotient classes lift along an epimorphism by pullback. -/
theorem simpleSubquotientClasses_subset_of_epi
    {X Y : C} (p : X ⟶ Y) [Epi p] :
    simpleSubquotientClasses Y ⊆ simpleSubquotientClasses X := by
  rintro q ⟨A, B, h, hs, rfl⟩
  have := hs
  exact objectClass_mem_simpleSubquotientClasses_of_mono_epi
    (pullback.snd B.arrow p)
    (pullback.fst B.arrow p ≫ cokernel.π (Subobject.ofLE A B h))

/-- Every simple subquotient occurs in the subobject or its quotient. -/
theorem simpleSubquotientClasses_subset_union (X : C) (P : Subobject X) :
    simpleSubquotientClasses X ⊆
      simpleSubquotientClasses (P : C) ∪
        simpleSubquotientClasses (cokernel P.arrow) := by
  rintro q ⟨A, B, h, hs, rfl⟩
  have := hs
  let p := cokernel.π (Subobject.ofLE A B h)
  by_cases hz : pullback.fst B.arrow P.arrow ≫ p = 0
  · right
    let j := cokernel.map (pullback.fst B.arrow P.arrow) P.arrow
      (pullback.snd B.arrow P.arrow) B.arrow pullback.condition
    have : Mono j :=
      Abelian.mono_cokernel_map_of_isPullback (IsPullback.of_hasPullback B.arrow P.arrow)
    let d := cokernel.desc (pullback.fst B.arrow P.arrow) p hz
    have : Epi d := epi_of_epi_fac
      (cokernel.π_desc (pullback.fst B.arrow P.arrow) p hz)
    exact objectClass_mem_simpleSubquotientClasses_of_mono_epi j d
  · left
    have : Epi (pullback.fst B.arrow P.arrow ≫ p) := epi_of_nonzero_to_simple hz
    exact objectClass_mem_simpleSubquotientClasses_of_mono_epi
      (pullback.snd B.arrow P.arrow) (pullback.fst B.arrow P.arrow ≫ p)

end

/-- Renard A.VI.3, unnumbered Lemma (i), with the original source antecedents. -/
theorem simpleSubquotientSubobjectQuotient
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSubquotientSubobjectQuotientStatement.{w} C := by
  intro _ _ X P
  exact Set.Subset.antisymm (simpleSubquotientClasses_subset_union X P)
    (Set.union_subset (simpleSubquotientClasses_subset_of_mono P.arrow)
      (simpleSubquotientClasses_subset_of_epi (cokernel.π P.arrow)))

end Langlands.Renard
