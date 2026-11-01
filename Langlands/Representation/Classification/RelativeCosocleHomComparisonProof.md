# Finite-dimensional relative Hom comparison for every outer quotient

Worker 526 assembled this proof with the central-block and source-twist
design of Workers 430 and 359, the literal shape transport of Worker 435,
and the Hom transport of Workers 845, 526 and 435. The imported geometric,
analytic, adjunction, finite-length and lower-bound results retain their
own documented authorship.

`Langlands.relativeCosocleHomComparison.{uF,uV,uM,uW,uZ}` proves exactly
`Langlands.GLRelativeCosocleHomComparisonStatement`. The field, fine,
middle, coarse and outer-carrier universes remain independent. The exact
nested `Q/R/S` refinements, literal flatten equality, irreducible unitary
cuspidal fine input, positive-root parameter, square-integrable actual
middle quotient, arbitrary irreducible analytically tempered coarse
input, strictly decreasing coarse vector and arbitrary irreducible
actual outer quotient are retained. There is no added premise.

The conclusion gives finite dimension of the two actual fine
opposite-Jacquet Hom spaces and equality of their complex finranks. The
outer target is the composed opposite Jacquet module of the specified
quotient `J` itself. The common dimension may be zero.

The entry first proves
`Langlands.Exponents.wholeInductionLeadingRealBlock` with the exact
public whole-isolation proposition as its type. It applies the actual
whole-induction construction in `WholeInductionGeometricIsolation` with
three proved inputs:

- `Geometric.padicGeometricLemma` supplies the upper geometric filtration
  and hence the actual opposite filtration and identity grade.
- `relativeGeometricLeadingCharacterExclusion` excludes the leading real
  character from every other raw reversed piece. Its analytic proof uses
  actual untwisted source characters, closed tempered cones, the
  size-weighted coarse projection and inverse-reversal rigidity.
- `RelativeCosocleHomIsolationReduction.temperedInductionFiniteGeneration`
  follows from twist regularity and actual normalized-induction finite
  length, without a supplied finite-generation hypothesis.

The resulting embedding and retraction identify the complete generalized
leading central block of the opposite Jacquet module of the whole
induction. Their identities hold for all qualifying full central
characters with one pair of maps. Restricting this stronger conclusion
to the open-kernel characters gives the exact whole-isolation statement.

For an arbitrary irreducible outer quotient, actual second adjointness
produces a nonzero map from the inducing coarse twist into its opposite
Jacquet module. All adjunction admissibility conditions follow from the
public relative admissibility and opposite-Jacquet theorems. Finite
full-central operator spans give exact lifting on generalized character
spaces and a global equivariant projector. The whole-induction block
identity therefore survives the actual quotient map and constructs a
map `rQ` back to the coarse twist. This handles arbitrary quotients
without assuming a fine-support map or identifying the nonzero
adjunction map with the whole-induction embedding.

Every fine Hom factors through the selected coarse real block: inverse
refined second adjointness turns it into a map from actual inner
induction, whose entire carrier has the coarse scalar real part
`size * t` by the nested fine-twist calculation. Naturality transfers
the projector identity back to every fine Hom. Postcomposition by the
refined opposite Jacquet map of `rQ` is consequently injective on the
entire Hom space. Actual opposite-refinement transitivity and common
coarse-twist transport give `finrank Hout ≤ finrank Hin`.

The public `fineRelativeHomLowerBound` supplies both finite-dimensionality
conclusions and the reverse inequality. Antisymmetry proves equality.
The final theorem is exactly the isolation-reduction assembly applied
to the proved whole-isolation and finite-generation families.

This is an internal proof using generalized central blocks and actual
geometric and adjunction maps. It provides a uniform multiplicity-sensitive
replacement for the continuation step motivating the comparison in
Silberger's Proposition 5.9: every actual Hom map is controlled, including
central generalized directions, without varying a parameter family.
It does not identify Hom dimensions with raw composition-factor counts,
extend fixed-exponent projectivity over self-extensions, or assume full
Jacquet semisimplicity. The unrestricted wording of Silberger's Lemma
5.3, the consuming relative cosocle conclusion and downstream full
classification are not used. The proof preserves the published
residue-normalized absolute value, negative fine plus positive coarse
twist, right-translation upper induction and inverse-half opposite
Jacquet normalization throughout.
