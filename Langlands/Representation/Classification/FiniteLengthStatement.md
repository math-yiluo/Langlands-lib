# Finite length of finitely generated admissible GL_n representations

`Langlands.GLAdmissibleFiniteLengthStatement` states the following prerequisite
for the Jacquet and Langlands-quotient arguments. For every prime `p`, every
finite extension `F` of `Q_p`, every positive integer `n`, and every complex
representation `rho` of `GL_n(F)`, admissibility and finite generation as a
group module imply finite length as a group module.

This file supplies a proposition definition. The theorem's proof remains a
separate obligation.

## Objects, hypotheses and quantifiers

The field is the accepted `PadicField p`, with an arbitrary carrier universe
`uF`. Its specified finite-dimensional `Padic p`-algebra structure includes no
Galois, unramifiedness or degree restriction. The statement installs
`F.canonicalTopology`, namely `moduleTopology (Padic p) F.Carrier`. It does
not quantify over an arbitrary topology or require an additional chosen
local-field certificate.

The group is the existing Mathlib
`Matrix.GeneralLinearGroup (Fin n) F.Carrier`: the units of the matrix ring.
The topology is Mathlib's units topology on matrices with their product
topology. Concretely, it is induced by the matrix and its inverse together.
For matrices over the topological field `F`, this is the usual topology on
the invertible matrices: inversion is continuous there by the adjugate and
nonzero-determinant formula. This is an interpretation of the existing
construction, not a new topology field or a new theorem assumed by the
statement.

The representation carrier `V : Type uV` has a separate, unrestricted
universe. It has `AddCommGroup V` and `Module Complex V`; it has no topology
and need not be finite-dimensional over the complex numbers.
`Representation Complex G V` is the actual homomorphism into linear
endomorphisms.

`IsAdmissible rho` is the accepted predicate: every vector has an open
fixing subgroup, and the fixed-vector space for every open subgroup is
finite-dimensional over the complex numbers. Silberger's convention tests
compact open subgroups; on `GL_n(F)` this agrees with the all-open convention,
because compact open subgroups form a neighborhood basis and fixed vectors
for a larger subgroup form a vector subspace of those for a smaller one.
Neither finite generation of `V` over `Complex` nor irreducibility is a
hypothesis.

`rho.asModule` is Mathlib's type synonym for `V` with its actual action of
`MonoidAlgebra Complex G`, the algebraic group algebra. A basis element
supported at `g` with coefficient `c` acts as `c` times `rho(g)`. Thus
`Module.Finite (MonoidAlgebra Complex G) rho.asModule` means finite generation
by group translates, exactly the source's "finite type" condition. It is not
a finite-dimensionality condition on the complex representation.

`IsFiniteLength (MonoidAlgebra Complex G) rho.asModule` means a finite
iterated extension of simple group-algebra modules. Mathlib's
`isFiniteLength_iff_exists_compositionSeries` identifies it with existence
of a composition series of the actual invariant-submodule lattice from
bottom to top. It includes the zero representation. No series, semisimple
decomposition, scalar central character or quotient is supplied as input.

## Original source and explicit specialization

Allan J. Silberger, *Introduction to Harmonic Analysis on Reductive p-adic
Groups*, Princeton University Press, 1979:

- Theorem 5.4.1.6, printed pp.291-292 (PDF pp.297-298), statement and entire
  proof: an admissible representation whose group module is of finite type
  has a finite composition series.
- Section 1.3, printed p.25 (PDF p.31): complex representations and finite
  generation as a group module.
- Section 1.5, printed pp.35-36 (PDF pp.41-42): smoothness and admissibility.
- Chapter 0, printed pp.1-7 (PDF pp.7-13): the general linear group,
  connected reductive groups, and the topology on their rational points.

The registered original is `silberger-1979-harmonic-analysis`, content
SHA-256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
The retained file is
`C:/Central-Library/Silberger--Introduction to harmonic analysis on reductive p-adic groups (book)--1979.pdf`.
The cited theorem and proof, finite-generation definition, and admissibility
definition were read directly in that original, with the formula-bearing
pages visually checked.

Silberger's theorem is for the rational points of a connected reductive
group over a p-adic field, in the book's ambient setup. This proposition
restricts it explicitly to the split connected reductive group `GL_n`,
and to characteristic-zero local fields finite over `Q_p`. Its actual
rational-point group is exactly the invertible matrix group used in Lean.
It does not purport to formalize the arbitrary-reductive-group theorem.
The positive-rank hypothesis `0 < n` matches the usual `GL_n` convention.
The finite-field-extension and representation-carrier universes remain
independent.

The source imposes no unitarity, temperedness, fixed central character,
irreducibility, or parabolic-induction assumption on this theorem.
In particular, the scalar central character reached during its proof is
an intermediate reduction, not a hypothesis added to the conclusion.
No induction, Jacquet normalization, additive character, Haar measure,
or real-exponent ordering occurs in this proposition.

## Source-to-declaration and dependency map

| Source or interface | Lean role |
| --- | --- |
| Silberger, Theorem 5.4.1.6, pp.291-292 | The implication in `GLAdmissibleFiniteLengthStatement`, restricted to `GL_n(F)` |
| Silberger, Section 1.3, p.25 | `Representation`, its `asModule`, and finite generation over the group algebra |
| Silberger, Section 1.5, pp.35-36 | `IsAdmissible rho`, including smoothness |
| Mathlib `RingTheory/FiniteLength.lean`, definition `IsFiniteLength` and `isFiniteLength_iff_exists_compositionSeries` | Actual finite-length conclusion and its composition-series interpretation |
| Mathlib `RepresentationTheory/Basic.lean`, `asModule`, its group-algebra instance, and `asAlgebraHom_single` | Group translates and group-algebra scalar multiplication are the same action |

Exact accepted project dependencies, both version 1 and current at Library
commit `5bc58c2525e0499012801c80f17b6a9c04d57263` when checked:

- `ac4cb7d5-5dd1-44b6-9d56-f0ec6c70bce0`,
  `Langlands.LocalField.Definitions`. Accepted Lean SHA-256
  `8d9cc8aa128861b13b4f96d38bf95be46844d2eaad28aa3cbb654b070ee0e517`;
  accepted Markdown SHA-256
  `6cfb939cf42a71a81fa648b77bd4bab1076bffe0d62519181f7dc7db742124bf`.
- `665022df-625b-44ae-9dbd-425f6e266bab`,
  `Langlands.Representation.Smooth.Definitions`. Accepted Lean SHA-256
  `435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb`;
  accepted Markdown SHA-256
  `4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569`.

The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1:
Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`. The remaining imports are existing
Mathlib complex numbers, matrix general linear groups, finite-length modules,
and matrix/units topology. No unpublished project definition is imported.

## Proof-source and formalization boundary

The retained source contains a proof of this theorem. It reduces to cyclic
modules, filters by generalized central action, uses the scalar-character
splitting of Lemma 5.4.1.4, bounds the cuspidal part by admissibility, and
then uses maximal-parabolic Jacquet modules and induction on rank. Its final
length comparison invokes Jacquet exactness, Lemma 5.4.1.2. These earlier
passages were read, but this contribution does not claim their Lean proofs.
The source attributes an earlier result to Howe; the statement here is
supported by Silberger's retained statement and proof, without assuming
identity with another edition of a cited manuscript.

This finite-length prerequisite does not itself provide the exponent
criteria, cuspidal multiplicities, projectivity, tempered induction, or
Langlands quotient classification. Those remain separate parts of the
assigned theorem families. The module declares one `Prop` definition,
introduces no project axiom or placeholder, and does not prove that `Prop`.
