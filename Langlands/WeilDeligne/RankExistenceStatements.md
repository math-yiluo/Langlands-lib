# Positive-rank Weil–Deligne parameter existence

Worker 39 supplies three proposition definitions. No declaration in this
pair proves existence. The assertions use Worker 17's published actual
finite-dimensional complex Weil–Deligne pairs and genuine isomorphism
classes. They take no parameter inhabitant, decomposition, correspondence
or classification theorem as input.

## Exact statements

All three declarations are in
`Langlands.WeilDeligneRepresentation.Blocks`. The group universe `uG`
and vector-space carrier universe `uV` are independent. The coefficients
are the usual complex field. The explicit inputs are a group `G` with
topology, a subgroup `I`, an integer-valued degree homomorphism (written
into `Multiplicative ℤ`) and a unit-valued homomorphism `ν : G →* ℂˣ`.

| Declaration | Mathematical content |
| --- | --- |
| `PositiveRankParameterExistsFor` | For every natural number `n > 0`, the actual quotient `FrobeniusSemisimpleParameterClassesOfRank I degree n` is nonempty. |
| `TrivialRankParameterExistsFor` | For every `n > 0`, there exists an actual pair `A` of rank `n`, with zero monodromy, open inertia kernel, Frobenius-semisimple action, and `A.representation g = 1` for every `g`. |
| `RankParameterExistenceFor` | The conjunction of the preceding two assertions for the same group data and carrier universe. |

The quotient identifies pairs by invertible complex-linear maps
intertwining the group action and monodromy. Its rank is the descended
vector-space dimension. `IsFrobeniusSemisimpleParameter` requires open
kernel on `I` and semisimplicity of each action operator whose degree is
nonzero. It does not require monodromy to vanish. Zero monodromy here is
only a normalization of the asserted witness; the class type still
contains general nilpotent monodromy.

No compactness, normality, continuity of degree, or surjectivity of degree
is required for these two existence assertions. Nor do they require the
norm relation or a topological-group instance. This generality is
deliberate: the anticipated trivial representation on a rank-`n` complex
space has identity action, full inertia kernel and zero monodromy,
regardless of those supplied data. The relation
`r(g) N r(g)⁻¹ = ν(g) N` imposes no restriction on such a witness.
This explains the intended mathematics; the file contains no proof of it.

All positive ranks are quantified. Neither the trivial witness nor
nonemptiness asserts irreducibility in rank greater than one. The file
does not claim a correspondence to any general-linear-group representation.

## Original source and derived content

Tate, *Number theoretic background* (1979), §4.1.2 and §4.1.3,
printed page 20, retained `Part II.pdf` page 29, supplies the
finite-dimensional pair, nilpotent norm-covariant monodromy, open
inertia-kernel condition and Frobenius-semisimplicity convention.
The original page was read as text and visually checked.

- Literature ID: `tate-1979-number-theoretic-background`.
- Retained file:
  `/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.
- SHA-256:
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

`TrivialRankParameterExistsFor` is the derived trivial-action
specialization of this definition. `PositiveRankParameterExistsFor`
is its intended consequence on genuine rank-indexed classes.
`RankParameterExistenceFor` merely packages both propositions.
These exact assertions and their arbitrary-group generality are not
attributed as quoted theorems of Tate.

No Frobenius or norm orientation is changed: the module leaves those
inputs explicit. The later local specialization must use geometric
degree `+1` and `ν(Φ)=q⁻¹` with the actual residue cardinality.

## Published dependencies and scope boundary

The only direct project import is `Langlands.WeilDeligne.Parameters`.
Its complete project source closure is published in Library
`0592c757c0c0cfe8eda5eb1ccc5ea5e38ade5e30`.

| Imported module | Lean SHA-256 |
| --- | --- |
| `Langlands.Weil.Representation.Basic` | `b28deaa4136a43846ef575a313ec882f63ec124d3a8909a74e6079ac71438b9b` |
| `Langlands.Weil.Representation.Predicates` | `c2bb56c14f6bb674ac9ee78b458392bf59973f53d7e72fd159b7e7a83030a148` |
| `Langlands.WeilDeligne.Basic` | `2359916cf05537665a83a6f5e75c55f2698577b47d9777f6431262fd1b595fbf` |
| `Langlands.WeilDeligne.Parameters` | `73663a8250d1bdc055a419d6574169de0278ee17e26cc457841be3ff6b38898c` |

The four imported sources have the listed hashes in the current Library.
Their original authorship is unchanged; this contribution republishes none of
them.

This is a supplementary portion of task
`fb3d3bca-bec4-4b30-9f0e-ac37da732e58`. Worker 25's published
`Blocks.ParameterNormalForm` already includes rank-class nonemptiness under
source-setting assumptions. This module makes the trivial-action representative
an explicit existential target and gives the weaker arbitrary-group hypotheses
appropriate to that witness. It does not replace or duplicate the published
block classification and calculus targets. A local use substitutes
`localWeilGroup F`, `localInertia F`, `(localDegree F).toMonoidHom`, and
`(localNormCharacter F).toMonoidHom` from the published local constructors.
No classification theorem or local Langlands correspondence is assumed.

## Development inspection

The exact source above passed the pinned shared Lake build with zero
warnings and zero errors (diagnostic
`54ce2ed1-f85f-4f44-b7f8-a2f579bab4e8`).
Exact-target inspection of `RankParameterExistenceFor` reports a
definition returning `Prop`, with universe parameters `uG`, `uV`;
its inspected assumptions are only `propext`, `Classical.choice`,
and `Quot.sound`. These are development checks, not a theorem proof
or independent acceptance.

- Lean source SHA-256:
  `dbd49254787618f29d0a09d10ae849a0ccc8566172865d038c34a3f75e476a3d`.
- Checked source fingerprint:
  `ae1c57618596578fa8d97f7681b2a79bcb1e89688504fdc70c1eecc523071d7e`.
- Elaborated declaration type fingerprint:
  `dd1dcfb3a989b1c892fb8eaa63a620cb70c038f66d6b8d28fa97ee16be5334fc`.
- Elaborated proposition-expression fingerprint:
  `e4cdc59654a9944b04bfc85e5b1bcc19525a6eb9c5bf5a138d8e3a55aae58b1f`.

The proposition expression references both named component definitions.
Its fingerprint is therefore retained together with the complete Lean
source hash and the four imported source hashes above; it is not used
alone as a fingerprint of all referenced bodies.
