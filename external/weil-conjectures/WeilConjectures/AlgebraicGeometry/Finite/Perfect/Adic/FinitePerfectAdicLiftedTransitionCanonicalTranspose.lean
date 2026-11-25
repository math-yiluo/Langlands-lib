/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCohomology
public import WeilConjectures.RingTheory.DerivedModuleScalarAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicLiftedTransitionCanonicalTransposeFormula

/-! # Canonical transpose of the lifted finite perfect transition

Source: Stacks Project, Tags 06YY and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-lifted-transition-canonical-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived

/-- The transpose of the lifted transition is invertible for the canonical derived
restriction adjunction. This is the universe-lifted form of the normalized transpose
in the supplied algebraic tower. The proof transports the original transpose through
exact universe lifting and the scalar-restriction comparison.
(blueprint: lem-weil-pbc-finite-perfect-adic-lifted-transition-canonical-transpose). -/
theorem finitePerfectAdicLiftedTransition_canonical_transpose_isIso
    {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    (T : FinitePerfectAdicAlgebraTower d) (n : ℕ) :
    let q : ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)) →+*
        ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)) :=
      RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
    letI : (normalizationModuleRestrict q).IsRightAdjoint :=
      ModuleCat.derivedRestrictScalars_isRightAdjoint.{t + 1, 0} q
    let adj := Adjunction.ofIsRightAdjoint (normalizationModuleRestrict q)
    IsIso ((adj.homEquiv _ _).symm (finitePerfectAdicLiftedTransition T n)) := by
  dsimp
  obtain ⟨e, he⟩ := finitePerfectAdicLiftedTransition_canonical_transpose_formula T n
  letI := T.normalized n
  rw [he]
  infer_instance

end AlgebraicGeometry.Scheme
