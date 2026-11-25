# Algebraic coinvariant tower, twist and central-action statements

`Langlands.Jacquet.CoinvariantAlgebraStatement` is a proposition definition,
not a proof. It states three compatible laws for the actual Mathlib
normal-subgroup coinvariant representations over the complex numbers.
The group and representation carrier have independent universes. No topology,
smoothness, admissibility, finite generation or finite dimension is assumed.
Its three clauses are themselves concrete proposition definitions in the same
module: `CoinvariantTowerStatement`, `CoinvariantTwistStatement`, and
`CoinvariantCentralActionStatement`, all in `Langlands.Jacquet`.
The combined target is their conjunction. They are not predicate parameters
or hypotheses asserting the desired laws.

For a representation `rho` and a normal subgroup `N`, write `V_N` for the
actual quotient by the span of `rho(n)v - v`. Mathlib's `rho.toCoinvariants N`
is the descended representation of the original group on this quotient.
It is not an arbitrary object supplied with assumed quotient properties.

1. If `N ≤ P` and both subgroups are normal in the acting group, there is
   an actual equivalence of group representations `(V_N)_P ≃ V_P`.
   It sends the double quotient of each vector to its single quotient.
   The second coinvariant construction uses `P` itself; its action already
   kills `N`, so this is the usual quotient by `P/N` without changing group
   types. The canonical quotient formula determines the equivalence.
2. If a unit-valued character `chi` is trivial on `N`, taking `N`-coinvariants
   commutes with twisting by `chi`. The equivalence is the identity on
   represented quotient vectors. Triviality on `N` is an explicit premise;
   a character nontrivial on `N` would instead involve twisted coinvariants,
   which are not the objects in this statement.
3. A prescribed scalar action of the original group's center descends to
   the quotient with the same character. No nonzero-quotient assertion,
   irreducibility, or uniqueness of the descended central character is
   asserted.

These are unnormalized algebraic prerequisites for the Jacquet functor.
The normality assumptions are relative to the specified acting group; they
do not assert that the unipotent radical of a proper parabolic is normal in
the full reductive group. In parabolic applications one first works in the
appropriate normalizing subgroup and later restricts the descended action
to the Levi subgroup. Matching the actual parabolic tower and its modulus
characters is a separate geometric and normalized-transitivity step.
This pair does not carry out that step.

## Original sources and derived formulation

Bernstein and Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977), Section 1.8(b), printed pages 444-445 / PDF pages 5-6,
defines the relation span, quotient and descended normalizer action.
Section 1.9(c) gives transitivity, and 1.9(f) gives character compatibility.
Those passages were read in the original. Their framework includes smooth
representations and modular normalization. The present statement isolates
the algebraic quotient identities underlying those assertions and explicitly
uses unnormalized actions. It is a derived algebraic formulation, not a
claim that all source hypotheses can be removed from the normalized
parabolic theorems.

The algebraic reasoning identifies precisely why no topology is needed.
For the tower law, the `N`-relation span is contained in the `P`-relation
span. The `P`-relations on `V_N` are the images of the original
`P`-relations. The two quotient maps consequently induce inverse linear
maps, and their formulas on represented vectors prove equivariance.
For twisting, `chi(n)=1` makes the two `N`-relation spans equal; the
remaining group actions differ by the scalar `chi(g)` on either side.
For the central-action clause, apply the linear quotient map to the
given scalar-action identity and use its surjectivity. This third clause
is a direct consequence of the source's quotient action, not a separately
numbered source theorem.

- Literature ID: `bernstein-zelevinsky-1977-induced-i`.
- PDF SHA256:
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
- Original:
  `C:/Central-Library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter III, revision April 29, 2019, Section 3, printed/PDF pages 3-4,
also supplies the relation quotient, its universal property (III.3.2),
and the descended action preceding III.3.5. These passages were read.
Its inverse-half-modulus twist is deliberately absent here.

- Literature ID: `casselman-2019-jacquet-module`.
- PDF SHA256:
  `377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
- Original:
  `C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.

## Actual dependencies and checking

The quotient, group action and intrinsic laws are the existing Mathlib
`Representation.Coinvariants`, `Coinvariants.mk`, `toCoinvariants`,
`toCoinvariants_mk`, and `toCoinvariantsMkQ`, from
`Mathlib/RepresentationTheory/Coinvariants.lean`. Their actual definitions
were inspected, including the normality instances and stability argument.
No second coinvariant construction is introduced. The more general
normalizer-action construction of `Langlands.Representation.Jacquet.Coinvariants`
is not an import of this pair.

The sole project mathematical dependency is the scalar-twist definition
module `Langlands.Representation.Twist.Definitions`.
Its Lean file and Markdown page were read; their hashes at that reading were:

- Lean SHA256:
  `9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf`.
- Markdown SHA256:
  `94e8c64945411e253a2c91a8e1bf52090d6df15a43362b2032717064c6ac49bc`.

It has no project mathematical prerequisites. The checks used Lean 4.34.0
and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

The complete pair passed an incremental Lake build and exact
declaration inspection, with zero errors and warnings and
`statement_returns_prop = true`.
The full elaborated bodies of all three component propositions and the
conjunction were also inspected with explicit universes. The components are
named for reuse within this single coherent pair, with no assumed theorem
fields or predicate parameters.

This pair proves none of the three laws. The tower clause is proved by
`coinvariantTower` in `Langlands.Representation.Jacquet.CoinvariantTowerProof`.
