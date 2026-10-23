# Actual local Weil reciprocity and quasicharacter transport

Author: Worker 10. This proposition family states actual geometric local
Weil reciprocity and its quasicharacter consequences. All construction
imports are published. No reciprocity theorem is claimed as proved.
Worker 159 corrected the documentation of the separate published
coherent-system and absolute-filtration definitions and targets.

## Objects and normalization

The base ranges over every prime and every `PadicField.{u} p`, with
unrestricted carrier universe `u`. The topology on its multiplicative
group is supplied by arbitrary `T : F.TopologicalData`. The published
`F.canonicalTopologicalData` realizes this input for every field.

The Weil group is `Weil.Local.localWeilGroup F`, the existing integer
pullback of `Weil.Local.localResidueDegree F`. That degree is constructed
from the canonical field's actual absolute residue action and the
finite-field geometric-Frobenius comparison. It is not an arbitrary
continuous homomorphism named as if it were geometric. Using a canonical
degree while allowing `T` retains all topological realizations of the
same field; their normalized valuation and residue cardinality agree.
This agreement is part of the mathematical content when applying the
statement to arbitrary `T`.

`WeilReciprocityCandidate T (localResidueDegree F)` is the existing type
of continuous group isomorphisms `W_F^ab -> F^x`. The source is the
quotient by the closed commutator subgroup, with its quotient topology.
The inverse of a candidate takes values in that quotient, never in the
nonabelian Weil group.

`GeometricWeilReciprocityRelation` requires two existing relations:

- `GeometricOrderRelation`: normalized integer order after the candidate
  equals geometric integer degree.
- `GeometricProfiniteReciprocityRelation` for the induced Galois map:
  density, all actual finite norm kernels, finite surjectivity and
  restriction compatibility, and geometric residue normalization.

The second condition uses the exact finite residue action, not just the
valuation of a candidate image. Neither condition assumes a Weil
reciprocity existence or uniqueness theorem, a completion isomorphism,
unit images, or a character-transport theorem. A candidate is quantified
existentially in the existence target and universally in consequences.

## Statements

`WeilReciprocityExistenceUniqueness` says that there is exactly one such
isomorphism for every field and realization. It has no reciprocity map
as an input. Its uniqueness is a derived formulation: the strong
profinite characterization identifies the induced map into `G_F^ab`;
the actual map `W_F^ab -> G_F^ab` is injective under the Weil form of
local class field theory, so it also identifies the candidate itself.
This explanation is a mathematical proof route, not an implemented proof
or an assumed injectivity certificate.

`WeilReciprocityCompletion` says that every normalized candidate gives
exactly one continuous isomorphism from the actual open-finite-quotient
completion of `F^x` to `G_F^ab` satisfying the imported comparison
diagram. This keeps `F^x`, its completion, `W_F^ab`, and `G_F^ab`
distinct. Uniqueness of the extension follows from the dense completion
map and a Hausdorff target.

`WeilReciprocityInertiaImage` identifies the image of
`WeilQuotients.inertia` with `T.unitSubgroup`. The imported
`WeilQuotients.inertia_eq_image` already identifies that subgroup with
the image of inertia of the actual pullback, so it is the actual
inertia/units assertion. No principal-unit or higher-filtration
compatibility is assumed here.

The existing `weilCandidateCharacterEquiv` gives transport for every
continuous complex quasicharacter, with the usual complex topology. It
first descends through the closed-commutator quotient and then composes
with the inverse of the candidate. The existence theorem makes this
conditional construction available for the actual local Weil group.
It does not restrict these quasicharacters to finite-image or unitary ones.

`WeilReciprocityUnramifiedCharacters` identifies triviality on actual
Weil inertia with the existing `T.IsUnramifiedQuasicharacter` predicate.
For every `z : Complex^x`, it sends the actual degree character
`w -> z^(deg w)` to `a -> z^(ord a)`. The value `z` is arbitrary,
including infinite-order and nonunitary values.

`WeilReciprocityUnramifiedTwists` gives the corresponding pointwise
formula after multiplying an arbitrary continuous Weil quasicharacter
by that degree character. This is the exact arbitrary-unramified-twist
adapter needed by the downstream rank-one normalization. It follows
from multiplicativity of the imported descent and composition
constructions and the preceding degree formula.

`WeilReciprocityNormCharacter` specializes the formula to the actual
norm character, whose geometric degree-one value is `q_F^(-1)`. Its
transport is the complex-valued normalized absolute value of the field.
No complex logarithm, chosen exponent of a norm character, or chosen
Frobenius lift occurs in these statements.

`WeilReciprocityTheorems` conjoins exactly these six targets. The coherent
finite-extension system and higher absolute filtration are separate
published units:

- [ReciprocitySystem](ReciprocitySystem.md) defines
  `CommonClosure.CoherentFamilyRelation` and `CommonClosure.CoherentFamilyExistence`
  for candidates on every finite intermediate field in a common algebraic
  closure, including nonnormal fields. Coherence comprises the actual norm,
  transfer and conjugation squares, density and completion comparison.
  `NormalizedSystemRelation` adds geometric normalization; coherence alone
  is not the normalized reciprocity system.
  [ReciprocitySystemStatement](ReciprocitySystemStatement.md) specializes to
  the constructed geometric residue degree and canonical extension-field
  topologies. Its `CommonClosureReciprocityTheorems` states existence and
  uniqueness of this normalized system for every base field and supplied
  base topology.
- [Herbrand.Absolute](../../LocalFactor/Ramification/Herbrand/Absolute.md)
  constructs `Langlands.Ramification.Padic.absoluteUpperRamificationGroup`
  from the intersection of actual finite Galois restriction preimages and
  `localAbelianUpperRamificationGroup` as its image in the abelianization.
  [AbsoluteReciprocityStatement](AbsoluteReciprocityStatement.md) states the
  separate `AbsoluteUpperReciprocityTheorems`: inertia image, natural and real
  higher-unit images, conductor-level equivalence and last-upper-break
  characterization. These targets quantify a supplied map satisfying
  `GeometricProfiniteReciprocityRelation`; they do not construct one.

These definitions and statement targets are already available in the Library.
Proofs of the Weil, common-closure and absolute-reciprocity targets remain
outstanding. None of the separate system or higher-filtration targets is an
additional conjunct or an assumed input of the six-part Weil aggregate.

## Original-source correspondence

John Tate, *Number theoretic background*, Corvallis Part II (1979),
registered source `tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`,
retained at
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.

Worker 10 read the original printed pages 3-7 / PDF pages 12-16 and
printed page 20 / PDF page 29. The first pages define the topological
abelianizations and reciprocity isomorphisms. Section 1.4.1, printed
page 6 / PDF page 15, describes the actual nonarchimedean Weil subgroup
and its topology and explicitly chooses the geometric convention.
Thus a uniformizer corresponds to geometric Frobenius, the inverse of
arithmetic Frobenius.
Section 1.4.6, printed page 7 / PDF page 16, identifies its norm with
the normalized absolute value under reciprocity. Section 4.1.3,
printed page 20 / PDF page 29, confirms `|w| = q^(-v(w))`.

Jean-Pierre Serre, *Local Fields*, GTM 67 (1979), registered source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
The finite norm-residue and completion correspondence is XI.3-5,
printed pages 169-175 / PDF pages 175-181, read directly. The local
existence theorem is XIV.6, printed pages 218-219 / PDF pages 223-224,
also read directly. The exact uniqueness characterization is the
derived formulation documented in `ProfiniteReciprocityStatement.md`.
Serre's arithmetic map is inverted for the geometric convention;
norm kernels, finite surjectivity, density and subgroup images survive
that inversion.

The character assertions are derived from these actual reciprocity
isomorphisms and the existing continuous-character universal property;
they are not attributed to a numbered theorem with the exact Lean
formula. Inertia/units follows from the integer-degree/order identity.
The norm-character formula is the direct normalization statement of
Tate 1.4.6 in the project's direction of reciprocity.

## Dependencies and validation status

All imports are published: `ReciprocityRelations`,
`ProfiniteReciprocityStatement`, `Weil.Local.Assembly`, and
`HarmonicAnalysis.Conductor`. The actual Assembly constructions rely on
published `Galois.Local.AbsoluteProof`, including the proved continuity
and surjectivity of the residue action. No checking substitute or assumed
exactness is used.

Development compilation against the published imports succeeded with
zero errors and warnings. Exact inspection of
`Langlands.LocalClassField.WeilReciprocityTheorems` confirmed `Prop`,
unrestricted universe `u`, and the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. The environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
This statement pair has independent semantic acceptance and is published;
that status does not supply proofs of its proposition definitions.
The separate definitions and targets linked above are also published.
This documentation correction changes no Lean declaration or import.
