# Relative cosocle multiplicity equality

Author: Worker 435.

`Langlands.relativeCosocleMultiplicity.{uF,uV,uM,uW,uZ}` proves exactly
`Langlands.GLRelativeCosocleMultiplicityStatement`. The field, fine,
middle, coarse and outer-quotient carrier universes remain independent.
The theorem retains the actual nested `Q/R/S` refinements and literal
flatten equality, the irreducible unitary cuspidal fine representation,
the positive scalar-root parameter, the actual square-integrable middle
quotient, an arbitrary irreducible analytically tempered coarse input,
a strictly decreasing coarse vector, and every specified irreducible
actual outer quotient `J`.

The conclusion supplies one natural number and actual finite composition
series witnessing its Jordan–Hölder multiplicity in both canonical heads.
The number may be zero. Both heads are the existing
`Classification.head`, the quotient by `Classification.headKernel`.
The proof derives the required finite length and admissibility, and uses
the published relative Hom comparison as a proved theorem. It introduces
no support map to the coarse input and no assumption that `J` is a
quotient of the fine ambient induction.

The proof transports the fine representation and parameter across the
literal flatten equality. The helper `transportFineData` transports
irreducibility and Levi cuspidality by equality elimination. The public
`fineTwistIrreducibleAdmissible` theorem supplies regularity and
cuspidality for the negative fine twist and the negative fine plus
restricted positive coarse twist. The twist irreducibility equivalence
also supplies irreducibility on the flattened Levi.

The public `relativeCosocleAdmissibility` theorem extracts admissibility
of the analytically tempered coarse representation and preserves it
through the coarse twist and actual outer induction. Admissibility then
passes through the given surjection to `J`.

For the fine ambient induction,
`CuspidalSupport.cuspidalInductionLength.{uF,uV} F T n` gives finite
length over the actual ambient complex group algebra. The private
`ambientLengthAdapter` unfolds the concrete normalized-induction
wrappers, identifying the smooth cuspidal induction in that theorem
with the actual fine ambient induction. For the inner induction,
`CuspidalSupport.refinedCuspidalInductionFiniteLength.{uF,uV}` supplies
finite length over the actual coarse product Levi's group algebra.
It is applied to the flattened fine representation twisted by the
negative fine parameter; its transport along the actual flattened-Levi
equivalence is exactly the inducing representation of the inner
induction. Neither length is an input hypothesis.

The private `fineAmbientHomRank` uses the standard clause of
`Parabolic.normalizedSecondAdjointness.{uF,uV,uZ}`. The second conclusion
of `Parabolic.flattenedOppositeJacquetComparison` identifies the actual
flattened opposite Jacquet module with the composed opposite Jacquet
module. Postcomposition by the inverse representation equivalence and
change of group along the flattened-Levi multiplicative equivalence
transport the adjunction to the fine Hom space used by the relative
comparison. The target throughout is the opposite Jacquet module of
`J` itself. The private `innerHomRank` similarly uses the refined clause
of `Parabolic.normalizedSecondAdjointness.{uF,uV,uW}` to identify the
inner-induction Hom dimension with its actual refined opposite-Jacquet
Hom dimension.

The published `relativeCosocleHomComparison.{uF,uV,uM,uW,uZ}` is applied
to the complete original nested data and the specified outer surjection.
It equates these two fine Hom dimensions. Composing with the adjunction
identities equates the dimensions of intertwiners from the fine ambient
induction to `J` and from the fine inner induction to the coarse input.

The private `commonHeadMultiplicity` applies
`Classification.finiteLengthHeadHomMultiplicity.1` to each of these
finite-length inductions and its admissible irreducible target. That
published bridge derives finite length and semisimplicity of each
canonical head, identifies Hom from the induction with Hom from the head
using its actual surjective projection and universal property, and uses
admissible Schur's lemma to count simple factors. It supplies an actual
composition filtration for each head with multiplicity equal to the
corresponding Hom dimension. The dimension equality transports the
inner witness to the same natural number as the ambient witness. Thus
the conclusion asserts the existence of both series, even when the
common multiplicity is zero. The bridge's filtration argument computes
the same Hom dimension for any composition filtration of a finite-length
semisimple source; the count is independent of a choice of such a
filtration.

The provenance is an internal assembly of the imported finite-length,
admissibility, second-adjointness, actual Jacquet transport, relative
Hom comparison and head/Hom results. These imports retain their own
documented authorship. The motivating source is A. J. Silberger,
*The Langlands Quotient Theorem for p-adic Groups*, Math. Ann. 236
(1978), 95–104: the nested support setup on p.99, the comparison and
recovery arguments on pp.100–102, and Proposition 5.9 with its two
reciprocity formulas on p.102. The original article and formula pages
were read during this task. The retained source is
`literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`,
registered as
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.

The imported Hom comparison implements a uniform replacement for the
source's continuation step. Its actual geometric filtration and tempered
character exclusion isolate the generalized leading central block;
finite central action lifts that block through every specified quotient;
second adjointness and target naturality control every fine Hom map.
This supplies the arbitrary-input comparison, including central
generalized directions, without presupposing fine support or applying
a constituent-restricted generic comparison to unsupported input. The
present assembly uses that established actual-quotient result and the
two reciprocity identities. It does not invoke the false unrestricted
wording of Lemma 5.3 or downstream Langlands classification.

All induction and Jacquet objects are the imported actual constructions:
upper induction with right translation and positive half-modulus
covariance, residue-normalized `q^(-valuation)` absolute values, inverse
half-modulus opposite Jacquet action, and fine determinant exponents
`-vB` plus the restricted positive coarse twist. The proof adds no
replacement cosocle or Jacquet carrier.
