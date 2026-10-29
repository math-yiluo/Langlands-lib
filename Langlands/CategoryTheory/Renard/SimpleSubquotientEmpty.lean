import Langlands.CategoryTheory.Renard.SimpleSubquotientIdentitiesStatements
import Langlands.CategoryTheory.Renard.SimpleQuotient

/-!
# Renard A.VI.3: empty simple-subquotient classes detect zero objects

Proof of clause (ii) of the unnumbered Lemma on printed page 264 / PDF270
of the 9 July 2026 French edition.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

/-- Renard A.VI.3, Lemma (ii), with both source antecedents retained. -/
theorem simpleSubquotientEmpty
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSubquotientEmptyStatement.{w} C := by
  intro hG hAB6 X
  constructor
  · intro hempty
    have hnot (A B : Subobject X) (h : A ≤ B) :
        ¬ Simple (cokernel (Subobject.ofLE A B h)) := by
      intro hs
      have hmem : objectClass (cokernel (Subobject.ofLE A B h)) ∈
          simpleSubquotientClasses X := ⟨A, B, h, hs, rfl⟩
      rw [hempty] at hmem
      exact hmem
    by_contra hX
    have hfinite : Langlands.Renard.IsFiniteTypeObject X := by
      by_contra hnfinite
      obtain ⟨A, B, hAB, hs⟩ :=
        nonFiniteTypeSimpleSubquotient C hG hAB6 X hnfinite
      exact hnot A B hAB.le hs
    obtain ⟨P, _, hs⟩ := exists_simple_cokernel_of_finiteType hX hfinite
    have := hs
    let e : cokernel (Subobject.ofLE P ⊤ le_top) ≅ cokernel P.arrow :=
      (cokernelCompIsIso (Subobject.ofLE P ⊤ le_top) (⊤ : Subobject X).arrow).symm ≪≫
        cokernelIsoOfEq (Subobject.ofLE_arrow (show P ≤ ⊤ from le_top))
    exact hnot P ⊤ le_top (Simple.of_iso e)
  · intro hX
    have := Subobject.subsingleton_of_isZero hX
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro q ⟨A, B, hAB, hs, _⟩
    have hEq : A = B := Subsingleton.elim _ _
    subst B
    have := hs
    have : IsIso (Subobject.ofLE A A hAB) := by
      rw [Subobject.ofLE_refl]
      infer_instance
    exact Simple.not_isZero (cokernel (Subobject.ofLE A A hAB))
      (isZero_cokernel_of_epi (Subobject.ofLE A A hAB))

end Langlands.Renard
