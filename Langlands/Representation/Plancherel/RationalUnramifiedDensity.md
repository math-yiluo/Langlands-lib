# Density of nonzero unramified regular scalars

This derived supporting unit proves uniqueness and density for the existing
algebra of actual unramified regular scalar functions. It applies to a connected
reductive group over an arbitrary nonarchimedean local field, using the full
rational-character norm family. With a supplied topology on rational points,
it assumes continuity of the actual valuation-image projection. In particular,
the existing canonical point-topology continuity theorem supplies this premise
in the intended application. There is no splitness, characteristic, or
positive-rank restriction.

`finiteLaurentEvaluation` evaluates a finite Laurent combination at a tuple of
complex units. Its monomial formula is the coefficient times the product of the
specified integer powers.

`laurent_eq_zero_of_eval_on_infinite` is a one-variable coefficient-separation
lemma. The coefficient ring is any commutative ring with a separating family of
ring homomorphisms to the complex numbers. Multiplying a Laurent polynomial by a
power of its invertible variable clears negative exponents. If all scalar
images vanish on an infinite set of complex units, each mapped polynomial has
infinitely many distinct complex roots and is zero. The separating family then
makes every coefficient zero. The invertible power can finally be cancelled.

`finiteLaurentEvaluation_cons` compares evaluation after separating the first
variable with `finiteLaurentSuccessorEquiv`.
`finiteLaurentEvaluation_empty` identifies rank-zero evaluation with the
coefficient-ring equivalence. These comparisons give
`finiteLaurent_eq_zero_of_eval_on_box`: a finite Laurent combination vanishing
on a product of infinite subsets of complex units is zero, including rank zero.
The induction uses evaluations in the remaining variables as the separating
family of coefficient maps in the one-variable lemma.

`complexUnits_infinite_of_isOpen` proves that every nonempty open subset of the
complex units is infinite, by the open embedding of the units into the complex
numbers. A finite product neighborhood contains a box of such open sets.
Consequently `finiteLaurent_eq_zero_of_eval_on_open` proves uniqueness from
vanishing on any nonempty open subset of a finite complex torus.

`rationalUnramifiedLaurentAlgebraEquiv_eval` compares this finite evaluation
with evaluation of the actual regular function supplied by
`rationalUnramifiedLaurentAlgebraEquiv`. It proves the formula on monomials
using the existing basis-evaluation theorem, then extends by linear induction.
The character coordinates are the inverse of
`rationalImageUnramifiedContinuousEquiv` followed by
`rationalReductiveImageCharacterCoordinates`; this is a homeomorphism for the
existing compact-open topology on the full actual character space.

`rationalUnramifiedRegular_eq_zero_of_isOpen` transports open-set uniqueness
through these two comparisons. It states that an actual regular scalar
vanishing on a nonempty open set is zero as an element of the existing
function algebra. Its contrapositive,
`rationalUnramifiedRegular_exists_ne_zero_of_isOpen`, finds a nonzero value in
every nonempty open set for any nonzero regular scalar.
`rationalUnramifiedRegular_dense_nonzero` expresses this as density of the
nonzero locus in the entire actual character space.
`rationalUnramifiedRegular_dense_nonzero_on_open` restricts density to any open
parameter region by the open subtype inclusion, including an empty region.

This proof uses Mathlib's Laurent exponent-clearing, polynomial infinite-root,
finite-product topology, and density theorems, together with the actual
coordinate algebra and character homeomorphisms. It introduces no external
representation-theoretic or analytic assumption. Density alone does not prove
local hypersurface divisibility, denominator cancellation, a denominator
nonzero on a whole region, convergence, operator rationality, or the conditional
standard intertwining theorem.
