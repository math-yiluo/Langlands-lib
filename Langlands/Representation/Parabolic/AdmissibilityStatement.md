# Admissibility for actual block parabolics

Author: Worker 8. This proposition pair contributes to the broad group-side
task. It imports the published concrete `Langlands.Group.GL.Blocks`
construction. The assertions are statements with separate proof obligations.

## The four assertions

Fix a prime `p`, an actual finite p-adic extension `F : PadicField p`, a supplied
`T : F.TopologicalData`, and an ordered positive block shape `B` of rank `n`.
The topologies on the matrix groups, the parabolic and the product Levi are
induced by precisely `T.topology`. The field and representation module have
independent universes. The coefficient field is the complex numbers; no topology
or finite-dimensionality is imposed on the representation module `V`.

Write `G = GL_n(F)`, `P = B.parabolic F.Carrier`,
`M = B.Levi F.Carrier`, `q = B.leviProjection F.Carrier`,
and `s = B.leviInParabolic F.Carrier`. These are actual matrix groups and
homomorphisms, with the proved identity `q(s(m)) = m`. The normal subgroup
`N = B.unipotentRadical F.Carrier` is the actual kernel of `q`; its matrices
are upper block unipotent.

`AdmissibleRadicalTrivialClause` asserts that every admissible complex
representation of `P` is trivial on `N`.

`LeviInflationAdmissibilityClause` asserts that a representation `sigma` of
`M` is admissible if and only if its inflation `sigma.comp q` is admissible
as a representation of `P`.

`InductionAdmissibilityClause` asserts that the actual smooth induction to
`G` of this inflation is admissible whenever `sigma` is admissible.
Induction here is **unnormalized**: its functions satisfy
`f(pg) = sigma(q(p)) f(g)`, and `G` acts by right translation. Its vectors
are the smooth vectors of the actual covariant function representation.

`JacquetAdmissibilityClause` asserts that an admissible representation `rho`
of `G` has an admissible unnormalized Jacquet representation of `M`.
The expression in Lean first restricts `rho` to `P`, then forms Mathlib's
actual quotient by the span of `rho(u)v - v`, for `u` in the normal kernel
`N`, with its descended `P`-action, and finally restricts that action along
`s`. It is consequently the action `m[v] = [rho(s(m))v]`.
The quotient carrier, submodule structures and action laws are constructed
by the imported APIs. No Jacquet-module functor or desired theorem is an
arbitrary input predicate or assumed field.

`Langlands.Parabolic.AdmissibilityStatement` is the conjunction of these four
concrete clauses. The imported `Langlands.IsAdmissible` includes smoothness
and finite-dimensional invariants for **every open subgroup**, including
noncompact ones.

## Source correspondence and scope

The original source is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, *Induced representations and
the Jacquet module*, April 29, 2019:

- Section 1, pp.1-2, defines normalized induction by right translation and
  uses compactness of `P \ G` for admissibility.
- Section 2, p.2, identifies the admissible representations of `M` with those
  of `P` trivial on `N`; Proposition III.2.1 states that every admissible
  representation of `P` is trivial on `N`.
- Section 3, pp.3-4, constructs the relation quotient and its descended Levi
  action, before twisting by the inverse half-modulus.
- Theorem III.5.6, p.7, states admissibility of the Jacquet module. The explicit
  restriction to a field before III.5.5 is retained by using complex
  coefficients. The warning following III.5.7 about an earlier erroneous
  general-Noetherian-ring argument is not suppressed.

This is a documented specialization of those general reductive assertions to
actual block parabolics of `GL_n` over finite extensions of `Q_p`. It does not
cover equal-characteristic local fields or assert a theorem for arbitrary
topological groups.

The source's normalized induction and Jacquet assertions imply the stated
unnormalized versions: their normalizations differ by the usual smooth
half-modulus character of the actual Levi. Twisting by a character with open
kernel preserves and reflects admissibility. Indeed, intersect an open
fixing subgroup with that kernel for smoothness; for finiteness, the fixed
space for an arbitrary open subgroup embeds into the untwisted fixed space
for its intersection with the kernel. Apply the same argument to the inverse
character for the converse. This explains the change of normalization; the
Lean target itself uses no unevaluated modulus parameter and claims no
definition or identification of the genuine half-modulus.

For inflation, the actual projection `q` is continuous and open: the proved
homeomorphism `P = N times M` turns it into the second projection. Inverse
images of open subgroups prove one direction, and images of open subgroups
under `q` prove the other. Their fixed spaces are the same subspaces of `V`.
These facts explain the precise equivalence in the second clause, rather
than assuming that equivalence in the group data.

For induction, compactness of the actual parabolic quotient and finite
double-coset decompositions for compact open subgroups give finite invariant
spaces. Compact-open cofinality then supplies the all-open-subgroups
convention. For the Jacquet clause, Casselman's canonical lift argument is the
substantive theorem; it is not a consequence of algebraic quotient existence.
These explanations justify statement scope, not Lean proofs of the assertions.

Literature identifier: `casselman-2019-jacquet-module`.
SHA256: `377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The full eight-page text was read; original pp.2 and 7 were also visually inspected.
The concrete upper-block convention is described and sourced in `Blocks.md`
to BZ77 Sections 2.1-2.2, printed p.446.

## Dependencies and remaining obligations

The published imports are `Langlands.Group.GL.Blocks`, `Langlands.Group.GL.Padic`,
`Langlands.Representation.Induction.Definitions`, their smoothness and
local-field prerequisites, and the pinned Mathlib coinvariant construction.
The block definitions and proofs are by their geometry owners and are not
resubmitted as Worker 8's work. No definition code was copied into this
statement pair.

The actual normalized functor constructions, full-modulus identification,
normalized transitivity, canonical opposite-parabolic pairing and duality,
and proofs of all four assertions remain separate obligations. No statement
here claims irreducibility of induction or completes the broad task.
