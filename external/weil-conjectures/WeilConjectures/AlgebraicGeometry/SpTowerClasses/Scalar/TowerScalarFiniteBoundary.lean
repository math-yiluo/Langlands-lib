/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarFiniteBoundaryData
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.ScalarFiniteBoundaryEquality

/-! # Finite evaluation of scalar extension of an arbitrary integral arrow -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Scalar extension and finite evaluation preserve the underlying integral arrow.

Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
scalar extension and evaluation; steps 2--3 of
`lem-sfb-normalized-chern-finite-boundary`.
(blueprint: lem-sfb-tower-scalar-finite-boundary).

Proof: transpose the scalar-extended arrow under the derived scalar adjunction.
The scalar-unit normalization cancels the source comparison. For its target,
choose a K-flat resolution of the single root module. The representative transpose
identity and naturality of the universal scalar counit identify lineComparison
with the ordinary scalar unit, sending x to one tensor x. Cancellation of the
resolution isomorphism establishes this identity for the original root module;
no flatness hypothesis on that module is needed. The unit_section equation
identifies the supplied ordinary adjunction with tensor/restriction. The
transpose_model equation at the identity fixes the derived unit on each
K-flat representative, since the universal counit is invertible there.
Naturality and a K-flat resolution then fix that unit on every object, identifying
the supplied derived adjunction with its canonical counterpart.
Consequently the canonical scalar shift comparison is the one induced by this
adjunction. Naturality of its derived unit and shift comparison identifies the
underlying
scalar-extended arrow with the original arrow followed by that ordinary unit.
Evaluate at n and forget scalars. The sections fields of the specified
forgetful functor give identity-transport components of the comparison. Its
restrictions fields make these maps natural on the site; its morphisms fields
make them natural in the module. Thus they compare the two exact functors.
Its single and shift comparisons transport the preceding equality. On sources,
the composite of integerGenerator and scalarGenerator sends k to k times one,
so uniqueness in finiteQuotient_existsUnique identifies it with finiteQuotient.
On targets, the pure-tensor equation of lineEvaluation identifies the composite
of rootForget inverse and the scalar unit with z mapping to one tensor z;
finiteRootMap_existsUnique identifies it with finiteRootMap. Substitution gives
the displayed boundary equality, with HEq witnesses for the two endpoint
transports. This argument works for every integral arrow f, independently of
its construction or any Kummer normalization. Empty schemes, zero coefficient
rings, and f equal to zero satisfy exactly the same formulas. The remaining
composition identity is isolated in the proof plan for subsequent completion. -/
private theorem finiteBoundaryEquality_of_composition {D : Type u} [Category D]
    {X X' Y Y' : D} (q : X ⟶ X') (r : Y ⟶ Y')
    {a : X' ⟶ Y'} {beta : X ⟶ Y}
    (h : q ≫ a = beta ≫ r) : finiteBoundaryEquality q r a beta := by
  exact ⟨a, beta, HEq.rfl, HEq.rfl, h⟩

theorem scalarFiniteBoundary (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (hc : unitNormalization c.scalar.T
      (SemilinearSections.res.{u + 1, u, u + 1} (coefficientSystemMap l E T))
      c.scalar.adjunction c.scalarUnit (scalarGenerator l E T))
    (f : unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        c.rootModule)⟦(2 : ℤ)⟧) (n : ℕ) :
    ScalarFiniteBoundary l E c f n := by
  refine ⟨?_⟩
  dsimp [ScalarFiniteBoundary]
  exact finiteBoundaryEquality_of_composition _ _
    (scalarFiniteBoundary_composition l E c hc f n)

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
