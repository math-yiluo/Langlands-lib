/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Subobject.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.FinitePresentationSupportReductionFiltration
import WeilConjectures.CategoryTheory.FiniteFiltrationRefinement
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Integral-ideal filtrations in the finite-presentation interface

Source: Stacks Project, Tag 01YF.
(blueprint: lem-pc-e2-finite-presentation-integral-filtration)
 -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A finitely presented module on a Noetherian scheme has a finite filtration whose
quotients are pushforwards of ideals on integral closed subschemes.

Source: Stacks Project, Cohomology of Schemes, Lemma 30.12.3, Tag 01YF.
(blueprint: lem-pc-e2-finite-presentation-integral-filtration)

Proof: Use Noetherian induction on closed subsets of X, with induction assertion that
all finitely presented modules whose support closure is contained in the given closed
set have the asserted filtration. The support-reduction filtration gives a finite chain
with quotients either already integral-ideal pushforwards or finitely presented modules
with strictly smaller support closure. For a smaller-support quotient, its closure is
strictly below the closed induction bound by transitivity, so apply the induction
hypothesis. Integral-ideal quotients need no induction. The predicate of being an
integral-ideal pushforward is invariant under isomorphism, by composing the witnessing
isomorphisms. Apply finite_filtration_refinement to refine all smaller-support factors
at once and obtain a chain with only integral-ideal quotients. Apply the induction
assertion to F and its own support closure. The geometric support-reduction theorem
contains the reducible-support, J-adic and generic-inclusion parts of Tag 01YF, but does
not filter smaller-support factors. The refinement theorem is fully proved using the
source library's extension-closed filtrationClosure and conversion to subobjects. -/
theorem exists_finitePresentation_integral_filtration
    (X : Scheme.{u}) [IsNoetherian X] (F : X.Modules) [F.IsFinitePresentation] :
    ∃ (m : ℕ) (c : Fin (m + 1) → Subobject F) (hc : Monotone c),
      c 0 = ⊥ ∧ c (Fin.last m) = ⊤ ∧
      ∀ j : Fin m, ∃ (Z : Scheme.{u}) (i : Z ⟶ X),
        IsClosedImmersion i ∧ IsIntegral Z ∧
        ∃ I : Z.IdealSheafData,
          Nonempty (cokernel (Subobject.ofLE (c j.castSucc) (c j.succ)
            (hc j.castSucc_le_succ)) ≅ (pushforward i).obj I.toModules) := by
  classical
  let P : X.Modules → Prop := fun Q ↦
    ∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsClosedImmersion i ∧ IsIntegral Z ∧
      ∃ I : Z.IdealSheafData, Nonempty (Q ≅ (pushforward i).obj I.toModules)
  have hP : ∀ (A B : X.Modules), Nonempty (A ≅ B) → P A → P B := by
    rintro A B ⟨e⟩ ⟨Z, i, hi, hZ, I, ⟨f⟩⟩
    exact ⟨Z, i, hi, hZ, I, ⟨e.symm ≪≫ f⟩⟩
  let S : X.Modules → TopologicalSpace.Closeds X := fun G ↦
    ⟨closure {x : X | ¬ Subsingleton (G.presheaf.stalk x)}, isClosed_closure⟩
  let Good : X.Modules → Prop := fun G ↦
    ∃ (m : ℕ) (c : Fin (m + 1) → Subobject G) (hc : Monotone c),
      c 0 = ⊥ ∧ c (Fin.last m) = ⊤ ∧
      ∀ j : Fin m, P (cokernel (Subobject.ofLE (c j.castSucc) (c j.succ)
        (hc j.castSucc_le_succ)))
  have hind : ∀ T : TopologicalSpace.Closeds X,
      ∀ (G : X.Modules), G.IsFinitePresentation → S G ≤ T → Good G := by
    intro T
    refine (wellFounded_lt : WellFounded
      ((· < ·) : TopologicalSpace.Closeds X → TopologicalSpace.Closeds X → Prop)).induction
        (C := fun T ↦ ∀ (G : X.Modules), G.IsFinitePresentation → S G ≤ T → Good G)
        T (fun T ih ↦ ?_)
    intro G hG hGT
    have : G.IsFinitePresentation := hG
    obtain ⟨m, c, hc, hbot, htop, hquot⟩ :=
      exists_finitePresentation_support_reduction_filtration X G
    apply finite_filtration_refinement P hP G m c hc hbot htop
    intro j
    rcases hquot j with hj | ⟨hQ, hsmall⟩
    · exact Or.inl hj
    · let Q := cokernel (Subobject.ofLE (c j.castSucc) (c j.succ)
        (hc j.castSucc_le_succ))
      have hlt : S Q < T := lt_of_lt_of_le hsmall hGT
      exact Or.inr (ih (S Q) hlt Q hQ le_rfl)
  exact hind (S F) F inferInstance le_rfl

end AlgebraicGeometry.Scheme.Modules
