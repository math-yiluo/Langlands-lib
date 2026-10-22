# Determinant and rank-one character normalization

Worker 6 proves `Langlands.Weil.representationCharacterNormalization`, whose
complete type is the existing proposition
`Langlands.Weil.RepresentationCharacterNormalization.{uG,uV}`. The target and
all its imported Lean/Markdown pairs are unchanged. The group and representation
carrier universes are independent.

## Determinant character

The witness is the published
`FiniteRepresentation.determinantCharacter (FiniteRepresentation.of ρ)`.
The wrapper retains the actual carrier and action. Its scalar value is
`LinearMap.det (ρ g)` by definition, and the published constructor supplies
its unit values and homomorphism laws.

The private helper `continuous_det_moduleTopology` chooses `Module.finBasis`
inside the proof. The matrix-coordinate map is linear, hence continuous out
of `moduleTopology ℂ (Module.End ℂ V)` by
`IsModuleTopology.continuous_of_linearMap`. `Continuous.matrix_det` proves
continuity of its determinant, and `LinearMap.det_toMatrix` identifies that
function with the basis-independent determinant. Composing with the assumed
continuity of the action gives continuous scalar values.
`Units.isEmbedding_val₀.continuous_iff` then gives continuity into `ℂˣ`.
This uses the ordinary complex topology and its continuous inversion away
from zero; it never uses inversion on the group `G`.

The argument includes dimension zero: the finite basis and the matrix
determinant API permit the empty index type. No nontriviality or positive
rank hypothesis on the carrier occurs in this clause. Equality of scalar
values determines unit values, so pointwise extensionality proves uniqueness
of the determinant character.

## Rank-one equivalence and uniqueness

The private helper `eq_det_smul_one_of_finrank_one` uses Mathlib's
`LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one` to write an arbitrary
endomorphism as `c • id`. `LinearMap.det_smul` and the rank-one hypothesis
identify its determinant with `c`. Thus every action operator is its
own determinant times the identity.

`Module.nonempty_linearEquiv_of_finrank_eq_one` supplies a linear equivalence
from `ℂ` to `V`. Its inverse is used as the underlying equivalence from `ρ`
to `Langlands.characterRepresentation δ`, where `δ` is the determinant
character already constructed. Linearity and the scalar-operator identity
prove the intertwining equation. The actual representation equivalence is
constructed in the conclusion; no chosen basis, scalar character, or
equivalence is an input hypothesis.

For any other character `η` admitting an equivalence from `ρ`, the published
`FiniteRepresentation.determinantCharacter_eq` identifies their determinant
characters, including across the different carrier universes. On the scalar
line, `LinearMap.det_ring` evaluates the determinant at `1`, giving `η(g)`.
Pointwise equality then proves `η = δ`. Continuity of the witness was already
established in the determinant clause.

## Provenance and scope

This is an internal proof of the published target using existing Mathlib and
project constructions, with no new mathematical definitions or assumptions.
Its source boundary remains Tate, *Number theoretic background*, Corvallis
Part II (1979), section 2 opening, printed page 9/PDF page 18: determinant
identifies rank-one representation isomorphism classes with quasicharacters.
The original paragraph was checked in the registered source
`tate-1979-number-theoretic-background`, retained `Part II.pdf`, SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
The implemented matrix-continuity and scalar-endomorphism proof is internal;
no particular proof route is attributed to Tate.

The published target generalizes that paragraph from topological groups to
a group with any topology and a continuous action; the proof preserves this
generality. There is no assumption of `IsTopologicalGroup`, local-field
structure, compactness, finite image, open kernel, unitarity, or discrete
complex scalars. The result is a parameter-side normalization statement;
it supplies neither reciprocity nor a local Langlands correspondence.

The project imports are `Langlands.Weil.Representation.Operations` and
`Langlands.Weil.Representation.Determinant`; additional Mathlib imports supply
matrix continuity and the topology of units. Their constructions are reused
without modification. The closing theorem is submitted for exact-target
validation and independent semantic review; development compilation alone
does not establish publication.
