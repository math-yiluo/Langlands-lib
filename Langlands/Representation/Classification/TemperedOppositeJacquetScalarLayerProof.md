# Tempered scalar-character layers of the opposite Jacquet module

This module proves the published proposition
`Langlands.GLTemperedOppositeJacquetScalarLayerStatement`
(see [TemperedOppositeJacquetScalarLayerStatement](TemperedOppositeJacquetScalarLayerStatement.md))
as the theorem

```text
Langlands.glTemperedOppositeJacquetScalarLayer :
  GLTemperedOppositeJacquetScalarLayerStatement.{uF, uV, uW}
```

Let `π` be an irreducible analytically tempered representation of `GL_n(F)`
and `B` a block shape of `n`. Let `ρ` be a representation of the Levi `M` with
an exact unitary scalar central character that is a quotient of a
subrepresentation of the opposite normalized Jacquet representation of `π`
along `B`. Then `ρ` is analytically tempered modulo the full centre of `M`,
for every Borel Haar measure on `M ⧸ Z(M)`.

## Proof

The proof applies one published theorem to another:

```text
glTemperedOppositeJacquetScalarLayer_of_productLeviNecessity
  glProductLeviTemperedExponentNecessity.{uF, uV}
```

- `glTemperedOppositeJacquetScalarLayer_of_productLeviNecessity` is proved in
  [TemperedOppositeJacquetScalarLayerAssembly](TemperedOppositeJacquetScalarLayerAssembly.md).
  It derives the target statement from the hypothesis
  `GLProductLeviTemperedExponentNecessityStatement.{uF, uV}`.
  - That module first applies the hypothesis to the single-block Levi
    `oneBlock n`, which it identifies with `GL_n(F)` by `oneBlockLeviEquiv`.
    This gives the bound `TemperedUpperExponentBound`: every upper Jacquet
    exponent `χ` of an irreducible tempered `GL_n(F)` representation satisfies
    `‖χ a‖ ≤ 1` on tuples `a` whose normalized absolute values are monotone.
  - It then proves the target from this bound. By
    `tempered_of_upperExponentHypothesis`, it suffices to bound every upper
    refined Jacquet exponent `ψ` of `ρ`. The published inheritance theorem
    `glOppositeJacquetSubquotientExponentInheritance` makes the reversed `ψ` a
    dual exponent of `π` along a flattened shape. Hence it is an upper Jacquet
    exponent of `π` along the reversed shape, and the bound applies. The
    unitary central character of `ρ` makes the real parts of `ψ` sum to zero
    over each outer block. Summation by parts then gives `‖ψ a‖ ≤ 1`.
  - The Markdown of that module describes every step.
- `glProductLeviTemperedExponentNecessity` is proved in
  [ProductLeviTemperedExponentNecessityProof](ProductLeviTemperedExponentNecessityProof.md).
  It proves the hypothesis `GLProductLeviTemperedExponentNecessityStatement.{uF, uV}`.

The universe parameters `uF`, `uV` and `uW` are those of the target statement
and stay independent. The necessity theorem is used at `uF` and `uV`. The
kernel check of the compiled theorem reports only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

The proof adds no hypothesis on `ρ`. Irreducibility, finite length,
admissibility and semisimplicity are not assumed, and the scalar central action
is not weakened. Admissibility of `ρ` is proved in the assembly module.

## Acyclic boundaries

The modules imported by this proof, directly or transitively, contain no proof
of any of the following: the regular Langlands head or exhaustion results, the
square-integrable Langlands classification, or the opposite Jacquet quotient
criterion `GLTemperedDiscreteSeriesJacquetQuotientStatement` and the summand and
support statements built on it. Some of these appear in the imports only as
proposition definitions, in statement files.

## Provenance

The target statement is derived from J.-L. Waldspurger, *La formule de
Plancherel pour les groupes p-adiques, d'après Harish-Chandra* (2003),
literature ID `waldspurger-2003-plancherel`:

- Proposition III.2.2 (printed pp. 265–266): an admissible representation is
  tempered if and only if the real parts of all its Jacquet exponents lie in
  the closed positive cone.
- Section III.3 and Lemma III.3.1 (printed p. 267): the weak summand of the
  Jacquet module of a tempered representation is tempered.

The route of this proof is derived rather than taken from the source. The
provenance sections of the two modules linked above give the details.
