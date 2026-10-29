import Langlands.CategoryTheory.Renard.SimpleQuotientStatements
import Langlands.CategoryTheory.Renard.JordanHolder
import Mathlib.Order.Zorn

/-!
# Renard A.VI.3: simple quotients and simple subquotients

The actual cokernel witnesses are obtained by Zorn's lemma and the canonical
local finite-type condition, without additional smallness hypotheses.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

omit [Abelian C] in
/-- A zero object is finite type for Renard's full-subobject definition. -/
theorem isFiniteTypeObject_of_isZero {X : C} (hX : IsZero X) :
    Langlands.Renard.IsFiniteTypeObject X := by
  have := Subobject.subsingleton_of_isZero hX
  constructor
  · intro S
    exact ⟨⊤, fun _ _ => le_top, fun _ _ => le_of_eq (Subsingleton.elim _ _)⟩
  · intro S hS _ hproper _
    obtain ⟨P, hP⟩ := hS
    exact hproper P hP (Subsingleton.elim _ _)

/-- A nonzero finite-type object has a simple actual cokernel quotient.
This stronger helper does not need either category-wide source antecedent. -/
theorem exists_simple_cokernel_of_finiteType {X : C} (hX : ¬ IsZero X)
    (hfinite : Langlands.Renard.IsFiniteTypeObject X) :
    ∃ P : Subobject X, P < ⊤ ∧ Simple (cokernel P.arrow) := by
  classical
  have := Subobject.nontrivial_of_not_isZero hX
  obtain ⟨P, hP, hmax⟩ := zorn_le₀ {P : Subobject X | P < ⊤} (by
    intro S hS hchain
    rcases S.eq_empty_or_nonempty with rfl | hnonempty
    · exact ⟨⊥, (show (⊥ : Subobject X) < ⊤ from bot_lt_top), fun _ h => h.elim⟩
    · obtain ⟨U, hU⟩ := hfinite.1 S
      have hproper : U ≠ ⊤ := by
        intro heq
        subst U
        exact hfinite.2 S hnonempty hchain (fun Q hQ => (hS hQ).ne) hU
      exact ⟨U, lt_top_iff_ne_top.mpr hproper, hU.1⟩)
  have hcover : P ⋖ (⊤ : Subobject X) := by
    refine covBy_iff_lt_and_eq_or_eq.mpr ⟨hP, fun Q hPQ _ => ?_⟩
    by_cases hQ : Q = ⊤
    · exact Or.inr hQ
    · exact Or.inl (le_antisymm (hmax (lt_top_iff_ne_top.mpr hQ) hPQ) hPQ)
  have hs := (simple_cokernel_ofLE_iff_covBy P ⊤ le_top).mpr hcover
  have := hs
  let e : cokernel P.arrow ≅ cokernel (Subobject.ofLE P ⊤ le_top) :=
    (cokernelIsoOfEq (Subobject.ofLE_arrow (show P ≤ ⊤ from le_top))).symm ≪≫
      cokernelCompIsIso (Subobject.ofLE P ⊤ le_top) (⊤ : Subobject X).arrow
  exact ⟨P, hP, Simple.of_iso e⟩

/-- Canonical source AB6 gives a nonzero finite-type actual subobject
of every nonzero object. -/
theorem exists_nonzero_finiteType_subobject (hAB6 : SourceAB6 C)
    {X : C} (hX : ¬ IsZero X) :
    ∃ B : Subobject X, Langlands.Renard.IsFiniteTypeObject (B : C) ∧
      ¬ IsZero (B : C) := by
  classical
  by_contra h
  have hzero : ∀ B : Subobject X,
      Langlands.Renard.IsFiniteTypeObject (B : C) → IsZero (B : C) := by
    intro B hB
    by_contra hnB
    exact h ⟨B, hB, hnB⟩
  have htop : (⊤ : Subobject X) ≤ ⊥ := (hAB6 X).2 (by
    intro B hB
    have harrow : B.arrow = 0 := (hzero B hB).eq_of_src _ _
    have hbot : B = ⊥ := by
      simpa only [Subobject.mk_arrow] using
        (Subobject.mk_eq_bot_iff_zero.mpr harrow)
    exact hbot.le)
  have := Subobject.nontrivial_of_not_isZero hX
  exact bot_ne_top (le_antisymm bot_le htop)

/-- Renard A.VI.3(i), with both published source antecedents retained. -/
theorem finiteTypeSimpleQuotient (C : Type u) [Category.{v} C] [Abelian C] :
    FiniteTypeSimpleQuotientStatement.{w} C := by
  intro _ _ X hX hfinite
  exact exists_simple_cokernel_of_finiteType hX hfinite

/-- Renard A.VI.3(ii), using actual nested subobjects and their cokernel. -/
theorem nonFiniteTypeSimpleSubquotient
    (C : Type u) [Category.{v} C] [Abelian C] :
    NonFiniteTypeSimpleSubquotientStatement.{w} C := by
  intro _ hAB6 X hfinite
  have hX : ¬ IsZero X := fun hz => hfinite (isFiniteTypeObject_of_isZero hz)
  obtain ⟨B, hBfinite, hBzero⟩ := exists_nonzero_finiteType_subobject hAB6 hX
  obtain ⟨P, hP, hs⟩ := exists_simple_cokernel_of_finiteType hBzero hBfinite
  let A : Subobject X := Subobject.mk (P.arrow ≫ B.arrow)
  have hAB : A < B := by
    simpa only [Subobject.mk_arrow] using
      Subobject.mk_lt_mk_of_comm (i₁ := P.arrow ≫ B.arrow) (i₂ := B.arrow) P.arrow rfl
        ((Subobject.isIso_arrow_iff_eq_top P).not.mpr hP.ne)
  let e : (A : C) ≅ (P : C) := Subobject.underlyingIso (P.arrow ≫ B.arrow)
  have hinc : Subobject.ofLE A B hAB.le = e.hom ≫ P.arrow := by
    rw [← cancel_mono B.arrow, Subobject.ofLE_arrow, Category.assoc]
    exact (Subobject.underlyingIso_hom_comp_eq_mk (P.arrow ≫ B.arrow)).symm
  let q : cokernel (Subobject.ofLE A B hAB.le) ≅ cokernel P.arrow :=
    cokernelIsoOfEq hinc ≪≫ cokernelEpiComp e.hom P.arrow
  have := hs
  exact ⟨A, B, hAB, Simple.of_iso q⟩

/-- Both clauses of Renard A.VI.3's simple-quotient Proposition. -/
theorem simpleQuotientProposition
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleQuotientPropositionStatement.{w} C :=
  ⟨finiteTypeSimpleQuotient C, nonFiniteTypeSimpleSubquotient C⟩

end

end Langlands.Renard
