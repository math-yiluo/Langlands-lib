/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCohomology
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicLiftedTransitionTranspose
import WeilConjectures.RingTheory.DerivedModuleScalarAdjunction
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Universality of the lifted algebraic transition

Source: Stacks Project, Tags 06YY and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-lifted-transition-universal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived

/-- The coefficient-universe lift of a normalized algebraic transition is universal.

Source: Stacks Project, Tags 06YY and 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-lifted-transition-universal).

The transpose under the recorded step adjunction is invertible by the normalized
structure field. Universe lifting and the coefficient interchange preserve this
transpose, so the lifted arrow is isomorphic in the structured-arrow category to
the adjunction unit, which is initial.
-/
theorem finitePerfectAdicLiftedTransition_universal
    {A : Type t} [CommRing A] {d : AdicCoefficientDatum A}
    (T : FinitePerfectAdicAlgebraTower d) (n : ℕ) :
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
      (finitePerfectAdicLiftedTransition T n))) := by
  let q : ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)) →+*
      ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)) :=
    RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))
  let F : DerivedCategory (ModuleCat.{t + 1}
      (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) ⥤
      DerivedCategory (ModuleCat.{t + 1}
        (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)))) :=
    normalizationModuleRestrict q
  letI : F.IsRightAdjoint :=
    ModuleCat.derivedRestrictScalars_isRightAdjoint.{t + 1, 0} q
  let adj : F.leftAdjoint ⊣ F := Adjunction.ofIsRightAdjoint F
  haveI : IsIso ((adj.homEquiv _ _).symm (finitePerfectAdicLiftedTransition T n)) :=
    finitePerfectAdicLiftedTransition_transpose_isIso T n adj
  let e := asIso ((adj.homEquiv _ _).symm (finitePerfectAdicLiftedTransition T n))
  have he : adj.unit.app _ ≫ F.map e.hom = finitePerfectAdicLiftedTransition T n := by
    simpa [e] using (adj.homEquiv_unit _ _ e.hom).symm.trans
      ((adj.homEquiv _ _).apply_symm_apply (finitePerfectAdicLiftedTransition T n))
  exact ⟨(mkInitialOfLeftAdjoint _ adj _).ofIso
    (StructuredArrow.isoMk e he)⟩

end AlgebraicGeometry.Scheme
