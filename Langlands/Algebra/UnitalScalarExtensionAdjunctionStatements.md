# Renard A.V.2: scalar extension and restriction are adjoint

Module `Langlands.Algebra.UnitalScalarExtensionAdjunctionStatements`.
Namespace `Langlands.Algebra.UnitalScalarExtensionAdjunction`.
Entry proposition `ScalarExtensionAdjunctionStatements`.

Worker 709 authored the statement draft. Worker 185 checked the governing
source and the published construction and prepared this focused submission.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.V.2, the scalar-extension
example on printed pp.260–261 (one-based PDF266–267). Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

For a unital complex algebra A and a unital subalgebra B, the source gives
the extension functor P, sending X to A tensor_B X, as a left adjoint of the
restriction functor F. It gives the Hom maps theta and sigma:

- theta(f)(x) = f(1 tensor x);
- sigma(g)(a tensor x) = a g(x).

The source states their naturality and that they are mutually inverse, then
computes the unit eta(x) = 1 tensor x and the counit epsilon(a tensor y) = a y.
The surrounding A.V.2 unit–counit formulation supplies naturality and both
triangle identities. The equations connecting Hom maps to unit and counit
are the same formulation specialized to this example.

The supplementary older-edition corrections are registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.
PDF18–19 correct the old scalar example's “B-morphism” to “A-morphism” and a
parenthesization error. The governing 2026 example already contains these
corrections. The published construction's reading of “subalgebra” as unital
is retained: restriction must land in unital B-modules and theta uses 1.
No commutativity assumption on A is introduced.

The generalization from a subalgebra inclusion to any unital ring homomorphism
phi : B → A between possibly noncommutative rings is internal derived
infrastructure. Neither injectivity of phi nor any commutativity of B is
required. Explicit universe parameters, exact comparison with the native
`Adjunction.homEquiv`, repetition of its intrinsic laws, and the proposition
names and grouping are internal formal packaging. This is not a new numbered
theorem attributed to the source.

## Actual constructions and universes

The only imported scalar constructions are those in the published module
`Langlands.Algebra.UnitalScalarExtension`. Write E for
`functor.{uB,uA,uM} phi` and R for
`restriction.{uB,uA,max uA uM} phi`. E uses the actual balanced integer-tensor quotient,
the residual left A-action, and the tensor map on morphisms from that module.
R is the native restriction functor through the same homomorphism.
`tmul phi X a x` is the actual pure-tensor class in that quotient.
No tensor object, functor, balancing property or adjunction is assumed in
the closed target.

There are three independent universe parameters uB, uA and uM.
B lies in `Type uB` and A in `Type uA`. Both module categories have carrier
universe `max uA uM`, which is closed under tensoring with A. The restriction
functor is specialized to that same carrier universe: tensoring a carrier in
`Type (max uA uM)` with A produces a quotient in
`Type (max uA (max uA uM)) = Type (max uA uM)`.
B indexes balancing relations without raising the quotient carrier universe.
No relation between
uB and either uA or uM is imposed. This target does not assert an adjunction
between module categories at unequal carrier universes.

For `X : ModuleCat B` and `Y : ModuleCat A` at that carrier universe,
the native Hom equivalence of `adj : E ⊣ R` has direction

`(E.obj X ⟶ Y) ≃ (X ⟶ R.obj Y)`.

Thus the scalar example's theta is the native **forward** Hom map, and sigma
is its inverse. This use of theta differs from the direction of the initial
two-variable natural isomorphism in A.V.1 (printed p.258 / PDF264), whose
displayed theta goes from `Hom(Y,F(X))` to `Hom(G(Y),X)`.
After identifying G with E and F with R, that direction is the inverse of
the native forward map used here. Comparison with that general Hom-bifunctor
formulation remains a separate unit.

## Proposition definitions

Every declaration in this file is a `Prop`-valued definition. The seven
property predicates refer to one chosen native adjunction, and
`AdjunctionProperties` conjoins them in the following order, associating
to the right:

1. `HomFormulas` gives the two displayed theta/sigma formulas for all X, Y,
   f, g, a and x. The values are computed through actual ModuleCat
   morphisms, and sigma's formula uses the target Y's A-action.
2. `HomInverseLaws` requires sigma(theta(f)) = f and theta(sigma(g)) = g
   as equalities of whole module morphisms.
3. `HomNaturality` gives both simultaneous precomposition/postcomposition
   laws. For u : X' → X and v : Y → Y', theta(E(u); f; v) equals
   u; theta(f); R(v), and sigma(u; g; R(v)) equals E(u); sigma(g); v.
   Semicolons here mean categorical composition in its written order.
4. `UnitCounitFormulas` computes eta_X(x) = 1 tensor x and
   epsilon_Y(a tensor y) = a y for the unit and counit of the same adjunction.
   The latter tensor is formed from the restricted module R(Y).
5. `UnitCounitNaturality` gives the whole-morphism equations
   u; eta_X' = eta_X; R(E(u)) and
   E(R(v)); epsilon_Y' = epsilon_Y; v.
6. `TriangleIdentities` gives E(eta_X); epsilon_E(X) = identity_E(X)
   and eta_R(Y); R(epsilon_Y) = identity_R(Y), component by component.
7. `HomUnitCounitRelations` identifies theta(f) with eta_X; R(f), and
   sigma(g) with E(g); epsilon_Y.

`ScalarExtensionAdjunctionStatements` is closed: for every pair of rings
and every unital phi it requires the existence of one native adjunction
E ⊣ R satisfying `AdjunctionProperties`. Although the property predicates
are parameterized by an adjunction for convenient expression, the aggregate
takes no adjunction or conclusion as an input. All formulas and laws share
the same existentially required adjunction.

Its quantifier order is exactly
`∀ (B : Type uB) (A : Type uA) [Ring B] [Ring A] (phi : B →+* A),
  ∃ adj : E ⊣ R, AdjunctionProperties phi adj`.
Each property quantifies all objects, morphisms and elements displayed above;
equations without element arguments are equalities of whole ModuleCat morphisms.
In particular, the two inverse laws, both naturality pairs, both triangles
and both Hom–unit–counit relations hold for this same `adj`.

The source specialization is obtained by taking a complex algebra A,
`S : Subalgebra ℂ A`, B = S and `phi = S.val.toRingHom`. More generally the
same specialization works for a commutative coefficient ring k and a
possibly noncommutative k-algebra A. The module actions are precisely those
on the published ordinary module categories; no independent coefficient
action is imposed on their objects.

## Scope and dependencies

This file states the adjunction and its explicit formulas. It constructs
no adjunction or Hom maps and proves none of these propositions. A later
proof unit must prove the unchanged published aggregate.

The file imports `Langlands.Algebra.UnitalScalarExtension` and pinned Mathlib
`Mathlib.CategoryTheory.Adjunction.Basic`, in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`). The scalar construction is a
prerequisite; the general Hom-bifunctor comparison is independent.
Original nonunital-module adapters, other scalar-change assertions and the
rest of Appendix A retain their separate obligations.
