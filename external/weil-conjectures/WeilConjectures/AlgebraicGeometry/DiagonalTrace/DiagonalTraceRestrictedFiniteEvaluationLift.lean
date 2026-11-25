/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEvaluationEquation
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteResidueFunctor
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceExactFiniteEvaluationLift

/-! # Finite evaluation of an arbitrary restricted tower arrow -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
attribute [local irreducible] CategoryTheory.Abelian.Ext DerivedCategory
  Functor.mapDerivedCategory diagonalFiniteToPadic

/-- Every derived arrow of tower systems has a finite residue realization in fixed endpoints.
Source: exact quotient realization and exact-functor Ext naturality.
(blueprint: lem-sfb-diagonal-trace-restricted-finite-evaluation-lift).

Proof: scalar annihilation constructs the exact residue quotient functor. Ordinary scalar
restriction is fully faithful. Apply the generic exactFiniteEvaluation_lift theorem to this
functor, its natural evaluation isomorphism, the supplied endpoints and the supplied arrow. -/
theorem restrictedFiniteEvaluation_lift (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T] (r : Restriction l (ULift.{u} (Padic l)) T) (n : ℕ)
    {X Y : SpTowerClasses.Systems T (SpTowerClasses.Arings l (ULift.{u} (Padic l)) T)}
    {P Q : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (diagonalResidue.{u} l n))}
    (a : (r.F.obj X).obj (op n) ≅ (diagonalFiniteToPadic l n T).obj P)
    (b : (r.F.obj Y).obj (op n) ≅ (diagonalFiniteToPadic l n T).obj Q)
    (f : (DerivedCategory.singleFunctor _ 0).obj X ⟶
      ((DerivedCategory.singleFunctor _ 0).obj Y)⟦(2 : ℤ)⟧) :
    ∃ y : Ext P Q 2, finiteEvaluationEquation r.F (diagonalFiniteToPadic l n T) n a b f y := by
  let S := diagonalFiniteToPadic l n T
  obtain ⟨G, hG, hlim, hcol, ⟨e⟩⟩ := exactFiniteResidueFunctor_exists l T r n
  have := hG
  have := hlim
  have := hcol
  obtain ⟨hfull, hfaith⟩ := finiteResidueRestriction_full_faithful l n T
  have := hfull
  have := hfaith
  have : HasExt.{u + 2} (SpTowerClasses.Systems T
      (SpTowerClasses.Arings l (ULift.{u} (Padic l)) T)) := HasExt.standard _
  exact exactFiniteEvaluation_lift r.F G S n e a b f

end AlgebraicGeometry.ProEtale.DiagonalTrace
