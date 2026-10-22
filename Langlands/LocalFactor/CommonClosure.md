# Actual common-closure inputs for local constants

This module constructs the inputs needed to state local-constant relations over
all finite intermediate fields in one specified algebraic closure. It uses the
actual assembled local Weil group, continuous complex representations, the
quotient by short exact relations, actual field traces, and actual Haar measures.
It neither constructs nor assumes the existence of reciprocity or a local-constant
system.

## Fields, groups, and exact virtual representations

For a finite p-adic field `F`, `Extension F` is the existing
`FiniteIntermediateExtension F.Carrier`, including nonnormal extensions.
`weilSubgroup F E` is the preimage of the actual fixing subgroup of `E.field`
under the projection from `localWeilGroup F` to the absolute Galois group. Its
topology is the inherited subgroup topology. The finite-index instance uses the
published finite-index preimage result; `weilSubgroup_open` uses the published
Krull-openness result. Characteristic zero is derived from the p-adic algebra
structure when the perfect-field instance is needed.

`ContinuousPredicate F E` is the published ordinary continuity condition into
the usual finite-dimensional endomorphism topology. `Virtual F E` is the existing
exact Grothendieck quotient for those representations, not the split completion
or a free group on irreducibles. `degree` is its actual integer dimension map,
and `DegreeZero` is its actual kernel. Representation carriers have universe
`max uF uV`; the existing induction construction therefore stays in the same
carrier universe. No semisimplicity or classification is used.

## Actual nested induction

For `h : E.field ≤ L.field`, fixing groups reverse inclusion.
`weilSubgroup_antitone` proves this for their Weil preimages.
`nestedWeilEquiv` rebrackets the smaller group as a subgroup of the larger one;
its two maps are the same subtype elements, and its topology is the iterated
subtype topology. `nestedWeil_open` is openness pulled back along the inclusion.
The finite-index instance inside the larger group follows from the smaller
group's ambient finite index.

`inducedRepresentation` restricts along this specific rebracketing equivalence
and applies the existing finite-index equivariant-function induction.
`FiniteRepresentation.isContinuous_induce` proves its usual-topology continuity.
`induce` composes the published continuous exact restriction with the published
exact induction map. Algebraic exactness is already proved using actual coset
coordinates in `ExactInduction`; no equivariant splitting is assumed.
`induce_ofRepresentation` identifies the result on every genuine representation
generator with `inducedRepresentation`.

`degree_induce` follows from the degree formula for exact induction and the
preservation of degree by exact restriction. Its multiplier is explicitly the
index of the actual nested subgroup. This module does not additionally identify
that index with a field degree. `induceDegreeZero` restricts the same map to the
genuine dimension kernels, using this proved formula.

## Harmonic inputs and trace

`fieldData F E` is the existing canonical topological local-field data on the
same intermediate field. `AdditiveCharacter` reuses continuous nontrivial unitary
additive characters. `FieldCharacter` reuses continuous homomorphisms from field
units to complex units. `HaarMeasure` reuses regular additive Haar measures on
the canonical topology's Borel measurable space. None of these types is supplied
with a chosen element or an existence assertion.

`scaleHaar` applies the existing positive finite scaling construction, with an
actual `NNReal` scalar and proof of strict positivity. `traceCharacter F E L h`
uses the algebra structure induced by the actual field inclusion and the
existing trace-character constructor. Its scalar-tower certificate is the
identity between the actual composite algebra maps. Continuity follows from
the published restriction-of-scalars argument over `Padic p`; nontriviality
follows from the finite separable trace's surjectivity. `traceCharacter_apply`
states the exact formula with that inclusion-induced trace, rather than a
supplied arbitrary additive map.

## Conditional character lines

`ReciprocityFamily F` is exactly the published common-closure candidate family
with canonical topologies and the actual `localResidueDegree F`.
`NormalizedReciprocity F e` is exactly its full normalized-system relation:
norm, transfer and conjugation compatibility, density, completion comparison,
and the base-field-degree absolute-value normalization. No candidate or proof
of this relation is chosen.

For an explicitly supplied family `e`, `reciprocityUnits` composes the genuine
closed-commutator quotient projection with the component `e E`.
`weilCharacter` pulls a field quasicharacter back along that map.
`characterClass` inserts its actual continuous scalar line into `Virtual F E`;
`degree_characterClass` proves degree one. These constructions require only the
candidate data; arithmetic normalization is separately expressed by
`NormalizedReciprocity`. They do not declare an arbitrary candidate canonical.

## Provenance and scope

This is a derived assembly of the following published constructions:

- `ClassFieldTheory.Local.ReciprocitySystem` supplies the actual finite
  intermediate fields, candidate families and their precise relations.
- `Weil.Local.Assembly` and `LocalClassField.Transfer` supply the actual local
  pullback, fixing subgroups, finite index, openness and subgroup rebracketing.
- `VirtualRepresentation.Exact`, `ExactInduction`, and `ExactRestriction` supply
  the actual exact quotient, intrinsic exactness, restriction and degree laws.
- `Weil.Representation.InductionContinuity` proves continuity of the actual
  induction operation; `CharacterLine` constructs the actual continuous line.
- `HarmonicAnalysis.CharacterTransport` proves the trace and Haar-scaling
  construction obligations. `LocalClassField.Galois` supplies the actual
  topological abelianization projection.

No additional literature theorem is invoked. The implemented proofs are the
specializations and compositions described above. In particular this module
makes no standalone Weil-group comparison, closure-lift independence assertion,
local-constant assignment, spectral epsilon construction, or existence/uniqueness
claim. Those remain separate constructions or propositions.
