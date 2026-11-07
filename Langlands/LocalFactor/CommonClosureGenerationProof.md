# Degree-zero generation for actual common-closure Weil groups

`Langlands.LocalFactor.commonClosureDegreeZeroGeneration` proves the unchanged
Library proposition `CommonClosureDegreeZeroGenerationStatement.{uF,uV}`.
For every prime, every finite p-adic field `F` and every finite intermediate
field `E` in its specified algebraic closure, the virtual dimension-zero
kernel in the continuous exact Grothendieck group of `weilSubgroup F E`
equals the integer span of the actual inductions from nested intermediate
fields `L` of differences of two continuous character lines on
`weilSubgroup F L`. The field and representation-carrier universes remain
independent; the exact virtual group uses carrier universe `max uF uV`.
The theorem has no generation, finite Brauer, classification or reciprocity
premise.

This is the final internal assembly of the common-closure formulation of
Tate, *Number theoretic background* (1979), (2.3.1), printed page 11,
retained Part II PDF page 20. The statement module documents the comparison
of that assertion with the exact common-closure presentation. The registered
source is `tate-1979-number-theoretic-background`, SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

The implemented proof combines the elementary inclusion already proved in
the statement module with the converse. For that converse it applies
`VirtualRepresentation.Weil.degreeZero_le_of_finiteImage_twists` to the
span of the prescribed generators. This exact-group reduction uses the
published realization of exact virtual classes and reduction to
irreducible representations. Its four remaining obligations are discharged
as follows.

- `continuousTwist_mem_span` supplies stability of the span under every
  continuous character twist, using the actual induction projection formula.
- `characterClass_sub_mem_span` supplies each character-line difference by
  induction from the field to itself.
- `finiteImage_sub_mem_span'` supplies the reduced exact class of every
  continuous finite-image representation. This comparison factors the
  representation through a finite quotient, applies the proved finite
  degree-zero Brauer theorem, identifies subgroup preimages with actual
  nested intermediate Weil subgroups using infinite Galois theory, and
  transports finite induction through inflation into the exact virtual
  group. The assembly rewrites the degree of a genuine class as its rank.
- `CommonClosure.irreducible_finiteImage_twist` expresses each actual
  continuous irreducible as a continuous character twist of a finite-image
  representation, with the subgroup and carrier universes required here.

Thus both inclusions concern the existing continuous exact virtual quotient
and exact common-closure induction maps. The theorem asserts generation
only; applications to local-constant systems use their separately stated
laws and hypotheses.
