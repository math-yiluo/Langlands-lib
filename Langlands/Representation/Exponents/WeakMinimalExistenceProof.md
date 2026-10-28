# Existence of a weakly minimal standard opposite-Jacquet pair

Author: Worker 436.

`Langlands.glWeaklyMinimalStandardPairExistence` proves exactly the published
closed proposition `Langlands.GLWeaklyMinimalStandardPairExistenceStatement`
from `WeakCriticalStatement`. It retains every prime `p`, supplied
`F : PadicField.{uF} p`, supplied realization `T`, positive rank `n`, and
irreducible analytically tempered representation
`A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)`. The field and representation-carrier
universes remain independent.

The conclusion supplies a positive ordered block shape `B` whose actual
standard conjugate pair has a nonempty unitary spectrum in the full algebraic
transpose dual of the normalized opposite Jacquet quotient. Every concrete
conjugate block pair strictly refining that pair has empty unitary spectrum.
The refinement relation is the published relation on actual parabolic and
split-component subgroups, including arbitrary conjugating matrices.

## A one-block unitary exponent

Two private matrix lemmas treat an arbitrary shape of length one.
`oneBlock_scalar` identifies its block-scalar matrix with the ambient scalar
matrix of the unique coordinate. `oneBlock_oppositeUnipotent_eq_one` uses the
actual matrix-entry membership description to show that every element of its
opposite unipotent subgroup is the identity. The published
`singleBlock_leviHalfModulus` identifies its normalization factor with one.

`PadicField.TopologicalData.exists_unitaryDualJacquetExponent_oneBlock`
assumes a nontrivial representation and an actual `UnitaryCentralCharacter`
of that representation. It pulls the character back along evaluation at the
unique coordinate followed by the scalar-to-center map. Continuity of that map
and the central character's open kernel give an open kernel for the pulled-back
character; the norm-one condition is inherited pointwise.

A nonzero algebraic functional on the source is invariant under the trivial
opposite radical. The published `splitCentreDualJacquetSourceEquiv` carries it
to a nonzero functional on the actual opposite Jacquet quotient. Applying
`mem_dualJacquet_eigenspace_iff`, the central scalar action and the trivial
half-modulus prove that it belongs to the exponent-one eigenspace for precisely
the pulled-back character. A nonzero member makes that eigenspace non-bottom.
This is the full transpose-dual convention, with the same character and no
character inversion or conjugation.

`IsTempered.exists_unitaryDualJacquetExponent_oneBlock` obtains the required
central character from analytic temperedness. It first instantiates the
all-Haar quantifier at the existing Haar measure on the actual central quotient,
using `exists_isHaarMeasure_centralQuotient`. Thus the measure quantifier is
used with an actual witness.

`IsTempered.exists_unitaryDualJacquetExponent` extracts nontriviality from
irreducibility through the simple monoid-algebra module and chooses the shape
with one block of size `n`. The positive-rank hypothesis supplies its positive
block-size proof. These arguments use only the central-character part of the
Library's analytic temperedness predicate; the stronger analytic hypotheses in
the target remain intact.

## Finite selection and all conjugate comparisons

The private `exists_weaklyMinimal_of_unitarySpectrum` selects a standard shape
with nonempty unitary spectrum and largest possible block length. The published
`GeneralLinear.BlockShape.length_le` bounds every shape's length by `n`, because
its positive block sizes sum to `n`. `Nat.findGreatest` therefore gives the
required maximum from the one-block seed. Pullback at the standard pair agrees
with the original representation, as shown by the private
`standard_pullbackRep` lemma.

Suppose a strictly finer concrete pair `Q` had a unitary exponent. The published
`glDualJacquetInnerConjugation` transports that exponent from `Q.pullbackRep A`
to `A` at the same ordered shape and same character. The published
`conjugatePairRefinementRank` makes the length of `Q.shape` strictly greater
than the selected length. It applies to `F.Carrier` because the injective
algebra map from the infinite field `Padic p` proves that this carrier is
infinite. The transported exponent would put this greater length in the
selection predicate, contradicting maximality.

This argument quantifies over every `Q`; it does not restrict comparisons to
standard pairs or to a supplied combinatorial refinement. The closing theorem
combines this finite selection lemma with the irreducible tempered one-block
seed. No algebraic prerequisite remains as a theorem-valued hypothesis of the
closing declaration.

## Provenance and scope

The motivating source is A. J. Silberger, *Introduction to harmonic analysis on
reductive p-adic groups* (1979), registered as
`silberger-1979-harmonic-analysis`, SHA-256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
The paragraph before Corollary 4.5.11, printed p.189 (one-based PDF p.195),
supplies the minimal-pair existence argument; section 0.3, printed pp.5–6
(PDF pp.11–12), supplies the pair ordering and standard-pair conjugacy context.
Those original passages, including the formula-bearing page images, were read.

The implemented route is a derived type-A proof from the current Library's
concrete definitions. It uses an explicit one-block seed and bounded block
length instead of assuming nonempty spectrum or an abstract minimum principle.
Every concrete pair is already presented by a standard shape and an actual
conjugating matrix in `ConjugateBlockPair`; the independently proved inner
transport and rank growth justify the selection over standard shapes while
retaining all concrete comparisons. The proof does not assert an abstract
algebraic-group conjugacy theorem or a class-exponent comparison.

All mathematical inputs are imported by Lean module name. Prescribed critical
support, the critical-to-minimal converse, ordinary tempered support, tempered
block exhaustion, tempered unitarity or genericity, regular exhaustion, and
equal-exponent grouping do not enter this proof. The target and its imported
Lean/Markdown pairs are unchanged.
