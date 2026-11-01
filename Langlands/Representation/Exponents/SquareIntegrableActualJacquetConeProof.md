# Strict cones for actual scalar upper Jacquet subquotients

This internal proof implements `Langlands.SquareIntegrableActualJacquetConeStatement`.
It retains the analytic square-integrability predicate and the actual nonzero
subquotient hypothesis, with independent field and carrier universes.

The proof forms the actual surjection from the invariant submodule witnessing
the subquotient to the supplied scalar representation. Compact open subgroups
of the block Levi are cofinal. The continuous block-scalar central map and
admissibility of normalized Jacquet modules therefore let the local central
scalar detector produce an ordinary full-transpose eigencharacter with open
kernel. Local central dual-to-primal conversion produces a nonzero generalized
Jacquet vector for the same character.

Lifting this vector to the source proves that the source carrier is nonzero.
The analytic predicate supplies a genuine central character at an existing
central-quotient Haar measure. The strict GL exponent criterion gives the
strict chamber inequalities. Scalar compatibility of normalized Jacquet modules
identifies the character on constant block scalars with that central character.
Finally, the published real-part/cone equivalence gives zero total and positive
proper prefix sums. This proof constructs no cuspidal word and asserts no
classification or global support result.

The dependency audit follows the named theorems used here. The local central
scalar detector uses compact averaging and finite fixed-space character
spectra. The dual-to-primal conversion restricts a nonzero eigenfunctional to
a finite fixed space and uses its commutative character decomposition. Jacquet
admissibility uses the normalized canonical-lift construction and a smooth
character twist. Scalar compatibility is the direct normalized-quotient action
on scalar matrices followed by the algebraic scalar-character uniqueness
lemma. None of these steps uses cuspidal support classification.

For the strict GL criterion, its forward implication restricts to the actual
one-block Levi, uses the independently proved refined upper strict cone and
whole-chamber necessity, and transports the actual normalized Jacquet action
back to GL. The converse, although imported with the theorem, is the analytic
strict coefficient L2 summability argument. Central-character reduction uses
actual Haar existence and scalar uniqueness. These are analytic and local
Jacquet inputs rather than global disjoint-support irreducibility, ordered
quotient coverage, multisegment exhaustion, or a single-integral-line theorem.

A recursive import audit of this proof's 419 project modules found no missing
module and no occurrence of any of the excluded conclusion or proof names:
`SegmentEssentialSquareIntegrableClassification`, `MultisegmentHeadExhaustion`,
`OrderedMultisegmentHeadExistence`, `OrderedMultisegmentQuotientExhaustion`,
`TemperedBlockUniqueness`, `SquareIntegrableLanglandsClassification`,
`SquareIntegrableLanglandsExhaustion`, or `GLRegularLanglandsExhaustionStatement`,
including their lower-case proof names. Since the complete project import
closure contains none of those declarations, the local proof dependencies
cannot invoke them transitively. No theorem asserting the desired support
conclusion under another name is used by the implemented proof.
