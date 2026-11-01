# Actual Aubert commutation with normalized parabolic induction

Authors: Worker 76 (source-refinement coefficients, regrouping and final
assembly), Worker 165 (rank-zero construction), Worker 320 (actual
geometric-piece and induction comparisons, geometric class proof), and
Worker 585 (geometric class proof integration and verification).

`Langlands.Aubert.inductionCommutation` proves exactly the published
`Langlands.Aubert.InductionCommutationStatement.{uF,uV} F T`. Its only outer
data are an arbitrary prime, supplied p-adic field and supplied topological
data. For every natural rank and every actual ordered positive block shape,
it identifies the integer-linear maps given by the ambient unadjusted Aubert
operator after normalized induction and normalized induction after the
product-Levi unadjusted Aubert operator. There are no additional theorem,
preservation, irreducibility, admissibility, cuspidality, dimension or
splitting premises.

For positive rank the proof applies
`inductionCommutation_positive_of_piece_comparison` to the proved actual
`geometricLemmaGrothendieck`. That assembly compares the maps on actual
finite-length product-Levi object classes. The geometric formula supplies
uniform actual intersection refinements and a finite enumeration of all
minimal representatives. The actual geometric-piece generator formula and
reindexing by that enumeration give the sum of `geometricPieceK0` values.

The supplied comparison is the proved equality of integer-linear maps
`normalizedInductionK0_comp_geometricPieceK0`, evaluated on each virtual
class. Its proof factors each actual piece as normalized refined Jacquet
restriction, actual inverse intersection transport, and normalized refined
induction. The two actual source/target intersection equalities give the
conjugacy of their flattened Levis. The actual transport agrees, in flattened
coordinates, with the existing inverse whole-Levi transport. Normalized
induction in stages, whole-Levi induction invariance on exact K0, and source
induction in stages then identify induction of the piece with ordinary
source induction of refined induction after refined Jacquet restriction.
This argument compares the actual representation constructions; the finite
coefficient identity is applied only after those maps have been identified.

Each induced piece therefore depends only on its source refinement. The
assembly's `refinementSignedSum_eq_refinement_sum` groups the ambient signed
sum by that refinement. The actual subgroup-to-Weyl intersection comparison
and total source-side Solomon coefficient formula identify its coefficient
with the intrinsic product-Levi sign. Thus the ambient signs remain
`(-1)^(n - C.length)`, and the product-Levi signs remain
`(-1)^(sum i, (B.size i - (S i).length))`. Linearity turns the resulting sum
into source induction after `alternatingOperatorOnLevi`. No sign adjustment
or Aubert involutivity is used.

Rank zero is a separate actual-functor argument, via
`inductionCommutation_rankZero`. The rank-zero general linear group and
empty product Levi are singleton groups. Evaluation at the identity
identifies the actual smooth induction carrier with its inducing carrier;
the identity map descends through the actual trivial coinvariant quotient
and is inverse to its quotient map. These representation equivalences
identify ordinary and refined induction-after-Jacquet with the input class.
There is one empty block shape and one refinement, each with sign one,
so both alternating operators are identity maps. This proves commutation
in rank zero without invoking a positive-rank geometric formula.

All groups throughout are the existing full exact finite-length smooth
complex Grothendieck quotients, including every actual short exact relation
and nonsplit sequences. Field and carrier universes remain independent;
carriers are saturated in `Type (max uF uV)`. The implementation uses the
supplied topology, upper block parabolics, positive half-modulus covariance,
right translation and the existing normalized Jacquet/refined functors.
The statement pair and all of its imported pairs are reused unchanged.

This is an internal algebraic assembly of the indicated actual construction,
transport, exact-class and finite-coefficient results. The source translation
of Aubert's induction identity remains in the published target Markdown;
no new original-literature assertion is transcribed here. The proof uses
no analytic segment classification, multisegment or square-integrable
exhaustion, ordered-head existence, quotient coverage, tempered uniqueness,
regular exhaustion, Aubert involutivity or irreducible-image conclusion.
