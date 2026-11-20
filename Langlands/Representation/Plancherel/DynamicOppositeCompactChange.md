# Compact change for the opposite continuations and canonical scalar

Fix the dynamic parabolic of a cocharacter and its opposite in a connected
reductive group over a nonarchimedean local field. The two compact open
subgroups `K` and `L` each give actual parabolic–compact products in both
directions. The inducing smooth complex representation of the common Levi has
an independent carrier universe. The conditional modulus uses the relative
root reflection and central split torus character statements.

The two full convergence domains agree for `K` and `L` by the quotient
measure scaling theorem in `DynamicCommonLeviMeasureScaling`. The forward
and reverse continuation constructors first apply
`transportedCompactModelContinuation` to change both compact pictures. They then
multiply the numerator by the corresponding positive quotient Haar factor.
Each retains the old denominator and hence its whole regular region. The
operator equations use the actual parameter-dependent equivalences and hold
throughout those regular regions.

`oppositeQuotientHaarScale` is the product of the two quotient Haar factors
from `K` to `L`. On the common regular region the intermediate compact
equivalence is shared by both operator equations. Composing the equations
gives the old composite transported to the new source picture and multiplied
by this product.

`conditionalCanonicalRationalScalar_changeCompact` uses the same nonempty
open convergence loci and generic irreducibility locus at both compacts.
The canonical fraction specification gives two scalar presentations on the
common regular region. The proof applies the composite equation to a nonzero
vector and uses injectivity of complex scalar multiplication on its
transport. The two presentations therefore satisfy the measure scale
identity there. Open-set uniqueness for regular functions gives equality of
their cross-products and hence the stated equality in the fraction field.

The compact change is derived from the Library's actual quotient Haar
comparison, its compact model equivalences, and its canonical scalar
specification. It supplies the comparison needed to transport the
continuation input of the Plancherel weight to the common compact in the
weak-term argument of Waldspurger VI.3.1.
