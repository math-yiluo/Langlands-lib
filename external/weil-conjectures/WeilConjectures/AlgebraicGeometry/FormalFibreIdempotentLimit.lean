/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalFibreCohomology
import WeilConjectures.AlgebraicGeometry.FormalFibreTransitionIdempotents
import Mathlib.LinearAlgebra.Span.Basic

/-! # Compatible lifting of formal-fibre idempotents

Source: Stacks Project, Tag 0G7X, the infinitesimal lifting step.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- An idempotent on the zeroth formal fibre extends to a compatible system of sections.
Source: Stacks Project, Tag 0G7X, lines 8133--8146; Tags 09ZU, 04EX and 00EE.
(blueprint: lem-weil-pbc-formal-fibre-idempotent-limit)

Proof: Put A = O_(S,s) and m = its maximal ideal. The map from X_0 to X_n is
base change of A/m^(n+1) to A/m. Its quotient ideal m/m^(n+1) has (n+1)st power
zero. Identify this pullback with X_0 by pullback pasting and the quotient-ring
isomorphism. Nilpotent base change therefore gives a unique idempotent e_n mapping
to e. A transition pulls an idempotent back to an idempotent. Its composite with
restriction to X_0 is restriction to X_0, so uniqueness implies that e_(n+1)
restricts to e_n. The resulting compatible family is a section of the inverse
system. The concrete limit of modules identifies compatible families with elements
of the limit; its zeroth projection is e. No properness or Noetherian hypothesis
is needed for this step. -/
theorem formalFibre_idempotent_limit {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (e : Γ(formalFibre f s 0, ⊤)) (he : IsIdempotentElem e) :
    ∃ v : ↥(limit (formalFibreSectionsSystem f s)),
      (limit.π (formalFibreSectionsSystem f s) (op 0)) v = e := by
  classical
  let R := AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk s))
    (S.presheaf.stalk s)
  let step (n : ℕ) (a : {a : Γ(formalFibre f s n, ⊤) // IsIdempotentElem a}) :
      {a : Γ(formalFibre f s (n + 1), ⊤) // IsIdempotentElem a} :=
    Classical.choose (formalFibreTransition_idempotents f s n a.val a.property)
  have hstep (n : ℕ) (a : {a : Γ(formalFibre f s n, ⊤) // IsIdempotentElem a}) :
      (formalFibreSectionsTransition f s n).hom (step n a).val = a.val :=
    (Classical.choose_spec (formalFibreTransition_idempotents f s n a.val a.property)).1
  let a : (n : ℕ) → {a : Γ(formalFibre f s n, ⊤) // IsIdempotentElem a} :=
    fun n ↦ Nat.rec (motive := fun n ↦
      {a : Γ(formalFibre f s n, ⊤) // IsIdempotentElem a}) ⟨e, he⟩ step n
  let legs (n : ℕ) : ModuleCat.of R R ⟶ formalFibreSections f s n :=
    ModuleCat.ofHom (X := ModuleCat.of R R) (Y := formalFibreSections f s n)
      (LinearMap.toSpanSingleton R (formalFibreSections f s n) (a n).val)
  let c : Cone (formalFibreSectionsSystem f s) :=
    { pt := ModuleCat.of R R
      π := NatTrans.ofOpSequence (F := (Functor.const ℕᵒᵖ).obj (ModuleCat.of R R))
        (G := formalFibreSectionsSystem f s) legs (by
          intro n
          simp only [Functor.const_obj_map, formalFibreSectionsSystem,
            Functor.ofOpSequence_map_homOfLE_succ]
          change legs n = legs (n + 1) ≫ formalFibreSectionsTransition f s n
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro r
          change r • (show formalFibreSections f s n from (a n).val) =
            (formalFibreSectionsTransition f s n).hom
              (r • (show formalFibreSections f s (n + 1) from (a (n + 1)).val))
          rw [map_smul]
          exact congrArg (fun x ↦ r • x) (hstep n (a n)).symm) }
  refine ⟨(limit.lift (formalFibreSectionsSystem f s) c).hom 1, ?_⟩
  have hπ := limit.lift_π c (op 0)
  have hval := congrArg (fun q ↦ q.hom 1) hπ
  exact hval.trans (by
    change (1 : R) • (show formalFibreSections f s 0 from e) = e
    exact one_smul R (show formalFibreSections f s 0 from e))

end AlgebraicGeometry
