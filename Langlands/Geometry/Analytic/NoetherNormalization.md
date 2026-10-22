# Constructing a finite injective Tate map

Author: Worker 56.

Over a complete ultrametric normed field `K`, the construction starts with an
actual finite bounded map from a finite-variable Tate algebra into a
nontrivial normed commutative `K`-algebra. If the map is injective, it already
has the required properties. Otherwise, the preceding finite-reduction theorem
constructs a finite bounded map with one fewer variable. Induction on the
variable count produces an injective map after finitely many steps.

For the base case, the proof shows directly that every restricted series in
zero variables is a scalar constant. A unital map from the coefficient field
into a nontrivial ring is injective, giving the required injectivity in zero
variables. No dimension, distinguished-series witness, division operation, or
normalizing map is assumed.

The final theorem applies this construction to the genuine quotient map of
`PresentedStrictAffinoidAlgebra`. That map is surjective and hence finite. The
resulting bounded algebra map is injective, the target is finite as a module
over its source, and the number of variables is bounded by the original
presentation arity. The nontriviality condition excludes the zero quotient,
which cannot contain a field. No nontrivial-valuation, discreteness, or
algebraic-closure hypothesis is added.

This implements the finite injective map conclusion of Proposition 2.4.1 and
Corollary 2.4.2, Section 2.4, pages 6–7 of the retained Berkovich-course
notes. The notes also retain a chart of the original ambient Tate algebra; the
present theorem returns the constructed normalization map and the
variable-count bound. The analytic input is the actual
distinguished-coordinate construction and division proved in preceding
modules. The refinement in `NoetherNormalizationLift` also retains an
isometric embedding into the original ambient Tate algebra.

Source
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
