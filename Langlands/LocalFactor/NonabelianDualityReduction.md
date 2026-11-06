# Spectral reduction of the actual local-constant dual equation

This auxiliary module is authored by Worker 1763 for task
`e945d920-df9f-446c-9528-b488a3bee609`. It proves algebraic identities on the
published continuous exact Grothendieck group and implications between the two
published duality statements. It does not prove either functional equation
without a functional equation as a premise.

The generic identity `continuousDual_continuousTwist` descends the published
algebraic representation identity `Langlands.dual_twist`. Equality of linear
maps on the exact quotient reduces to genuine representation classes. On those
classes the actual dual of a character twist is equivalent to the inverse
character twist of the actual dual. The existing quotient imposes all genuine
short exact sequence relations; this argument does not replace it by a split
quotient or restrict representations to finite image.

The construction `continuousTwistedDual` packages the character twist of this
contragredient as an integer-linear automorphism of the actual continuous exact
virtual group. The dual/twist identity proves that this automorphism is an
involution for each fixed continuous character. It also preserves the actual
integer virtual dimension. For the norm character it is precisely the operation
occurring in the fixed-Haar clause.

The actual common-closure spectral character at parameter `-s` is the inverse
of the character at `s`, by multiplicativity in the parameter. At parameter
`1` it is the restricted base norm character: both evaluate to the base residue
cardinality to the negative restricted base degree. The proof uses the real
exponential-logarithm identity for a positive residue cardinality. It does not
renormalize degrees on extension-field Frobenius elements.

Consequently the norm twist of the contragredient of `virtualTwist s x` equals
`virtualTwist (1-s) (continuousDual x)`. Applying fixed-Haar duality to the former
spectral twist proves spectral duality for the published
`conditionalDeligneValue`. Conversely, the spectral equation at `s=0` recovers
the fixed-Haar equation. The implication to the aggregate target retains the
fixed-Haar assertion as an explicit premise.

All these implications retain the entire published quantification: every prime,
independent field and representation universes, normalized supplied system,
actual intermediate field, nontrivial unitary additive character, exact virtual
element, pair of supplied Haar measures satisfying `FourierDualMeasures`, and
every complex spectral parameter. They neither choose a system or measure nor
alter the actual two-integral convergence and reflection condition.

This is an internal derived formulation of the spectral restatement explained
in `NonabelianDualityStatement.md`, based on Deligne (1973), formula (5.7.1) and
the unshifted spectral convention. The implementation uses the published
algebraic dual/twist proof and the existing exact-quotient and spectral
constructions. The analytic rank-one identity and the induction reduction
needed for unconditional fixed-Haar duality remain outside the proved result.
