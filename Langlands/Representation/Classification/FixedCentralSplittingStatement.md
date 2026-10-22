# Splitting with a fixed scalar central character

`Langlands.GLFixedCentralCharacterSplittingStatement` is a proposition
definition, not a proof. Worker 19 authored this coherent pair of projective
and injective splitting assertions and its concrete coefficient-support
predicate.

For every prime `p`, finite extension `F : PadicField p` with its canonical
topology, and positive rank `n`, let `G` be the actual matrix group `GL_n(F)`.
Let `rho` be an admissible complex representation on `V`. Fix a homomorphism
`chi : Z(G) -> Complex units` with open kernel which acts on all of `V` by
its scalar values. Suppose every coefficient of a vector and a smooth
algebraic-dual functional has compact support modulo the center. Then:

1. Every surjective intertwiner from a smooth representation `sigma` with
   the same scalar character `chi` onto `rho` has an intertwining section.
2. Every injective intertwiner from `rho` into a smooth representation `tau`
   with that same scalar character has an intertwining retraction.

The source representation `sigma` and target representation `tau` need
neither admissibility nor irreducibility, finite generation, finite length,
or finite dimension. Their carriers `U` and `W`, the distinguished carrier
`V`, and the field carrier have four independent universe parameters.
No topology is assigned to these complex vector spaces. The distinguished
representation need not be irreducible or nonzero.

## Concrete predicates and normalization

`HasCompactSmoothCoefficientsModCenter rho` says that for every
`ell : SmoothDual rho` and `v : V` there exists a compact subset `C` of
the actual topological quotient `G / Z(G)` such that

```text
ell(rho(g)v) != 0  implies  [g] belongs to C.
```

The set `C` may depend on both `ell` and `v`. The predicate uses the
published bilinear matrix-coefficient function and the published smooth
part of the algebraic dual. It has no assumed cuspidality, splitting,
quotient, or classification fields. On an arbitrary group with topology
this defines only the stated support condition; no general group theorem
is asserted at that scope.

The coefficient itself need not descend to `G / Z(G)`: a nontrivial scalar
central character changes its value. Its nonzero locus is invariant under
the center because character values are units. Smoothness of `rho` and
of `ell` makes the coefficient locally constant. Consequently this
central-invariant support descends to a closed subset of the quotient.
For the Hausdorff central quotient of `GL_n(F)`, containment in a compact
set therefore agrees with the source's compact-support-modulo-center
condition. There is no requirement of compact support in `G` itself.

Scalar action is expressed by
`centralCharacterSpace rho chi 1 = top`, using the published actual
exponent-one invariant subrepresentation. Its membership formula is
`rho(z)v = chi(z) * v` for every central element. The identical
exponent-one condition is required for the other representation in each
splitting clause. A generalized central-character condition with powers
greater than one would allow central extensions and is not used here.
Unitarity of `chi` is not a hypothesis. No choice or normalization of Haar
measure is part of this algebraic conclusion.

The project coefficient convention is `ell(rho(g)v)`. The smooth dual
uses `ell` acted on by composition with `rho(g inverse)`, with no complex
conjugation. These are Casselman's conventions in the cited formulas.
All equalities in the conclusion are equalities of actual intertwiners:
`f.comp s = id rho` and `r.comp j = id rho`.

## Original sources and exact specialization

W. Casselman, *Introduction to the theory of admissible representations of
p-adic reductive groups*, draft of 1 May 1995:

- Section 2.1, printed/PDF pages 18-22: smoothness, admissibility, the
  open-kernel convention for characters, scalar and generalized central
  spaces, and the smooth contragredient.
- Theorem 5.3.1, page 48, with proof on page 49: for an admissible
  representation, absolute cuspidality is equivalent to compact support
  modulo the center of every smooth-dual matrix coefficient.
- Theorem 5.4.1 and its complete proof, pages 49-50: an absolutely
  cuspidal scalar-character representation is projective and injective
  in the category of smooth representations with that scalar character.
  The proof treats surjections and injections explicitly. Proposition
  5.4.2 on page 50 extends the initial irreducible argument to general
  absolutely cuspidal scalar-character representations.
- Corollary 5.4.4, pages 50-51: the distinct multiplicity-free argument
  removes central extensions before applying projectivity. It does not
  license projectivity in the entire generalized-character block.

Registered original: `casselman-1995-admissible-representations`.
Actual PDF SHA-256:
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
Retained file:
`C:/Central-Library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
The cited statements and proofs were read directly; the formula-bearing
projectivity pages were also visually checked. The 1995 draft is not
identified without evidence with the historical Casselman preprint cited
by Silberger in 1978.

This statement specializes Casselman's connected reductive setting to
`GL_n`, and combines Theorems 5.3.1 and 5.4.1. Its coefficient-support
hypothesis is an actual object-level condition equivalent in this
admissible reductive setting to the absolute-cuspidality hypothesis.
It does not define an arbitrary predicate to stand for cuspidality.
The explicit finite extension of `Q_p` and positive rank retain the
source's characteristic-zero local-field case. The field's canonical
finite-dimensional module topology, product matrix topology, and induced
units topology give the ordinary topology on invertible matrices.
The conclusion is stated for actual linear intertwiners, so no assumed
abelian-category or categorical projectivity instance is required as input.

The source proof first constructs a convolution projection using the
formal-degree coefficient identity, then splits a surjection by lifting
one vector. It extends this to arbitrary absolutely cuspidal scalar
representations through Proposition 5.4.2. Injectivity follows by smooth
duality, admissible reflexivity of the distinguished representation, and
the natural embedding of an arbitrary smooth representation into its
smooth bidual. This explains the literature implication only; none of
these arguments has been supplied as a Lean proof by this pair.

## Formal dependencies and remaining obligations

Direct project imports, read in Library commit
`459d17160ca3aef5c5b4e8ba056125e56d9479a0`, are:

| Module | Objects used |
| --- | --- |
| `Langlands.LocalField.Definitions` | `PadicField`, its actual carrier and canonical topology |
| `Langlands.Representation.Exponents.Central` | `centralCharacterSpace` and its exponent-one scalar-action interpretation |
| `Langlands.Representation.MatrixCoefficient.Definitions` | The actual bilinear coefficient `matrixCoefficient` |
| `Langlands.Representation.Smooth.Contragredient.Definitions` | `SmoothDual`, the smooth subspace of the algebraic dual |

The working imports were compared byte for byte with that published tree:

| Module | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- |
| `Langlands.LocalField.Definitions` | `8d9cc8aa128861b13b4f96d38bf95be46844d2eaad28aa3cbb654b070ee0e517` | `6cfb939cf42a71a81fa648b77bd4bab1076bffe0d62519181f7dc7db742124bf` |
| `Langlands.Representation.Exponents.Central` | `ec9eac0489adf392dc2b94dcfec664f41c7ce02a310007d86d0c9341d8ea0557` | `173e76107b355511c75435f04b996c3ed7998a4056d6f4f8cadbb8a82084c290` |
| `Langlands.Representation.MatrixCoefficient.Definitions` | `92c0bf57151ef798f1198793a4d685afd175274240c1956b54ce3d10e855b7ae` | `c9fdcc728fe28ed0de403801ed10d861d70dd69994179b4fd14f35662d910955` |
| `Langlands.Representation.Smooth.Contragredient.Definitions` | `878b6130d7c563ead853cbdd50a6c70aac01f9104062049e696f9e68cbb30de3` | `531fc58fb846d22f48363964f7fb5af0ab9459747c7ca08a683df6ada7c8aae0` |

Smoothness and admissibility are imported transitively. Pinned Mathlib
supplies actual matrix groups, the center and quotient topology,
compact sets, linear intertwiners, injectivity, surjectivity, composition
and identity. The prepared environment pins Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

This differs from the existing
`Langlands.CompactCoefficientSplittingStatement`, which concerns
irreducible representations with compact coefficients on a general
unimodular group. Here the support is compact only modulo the center,
the distinguished representation is admissible but need not be
irreducible, and all maps remain in the fixed scalar-character category.

The definition owner's actual Jacquet-vanishing notion of GL
supercuspidality is separate. Its equivalence with the coefficient-support
predicate, and the translation of this statement into that vocabulary,
remain explicit future theorem obligations. No such equivalence is assumed
or claimed proved here. The splitting proof, cuspidal Jacquet multiplicity,
temperedness criteria and regular-positive Langlands quotient families
remain separate obligations of the larger development.
