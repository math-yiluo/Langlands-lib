# Polynomial residue kernels and valuation-kernel lifting

This is an internal algebraic prerequisite for a graded polynomial-coherence
argument. It uses the published valuation kernel-splitting results and Mathlib's
coefficient reduction, homogeneous components and Nakayama lemma. It asserts no
polynomial coherence or geometric extension theorem.

Let `R` be a commutative ring, `I` an ideal, and `σ` any variable type.
`polynomialCoefficientReduction I` is the actual coefficient quotient map
from `MvPolynomial σ R` to `MvPolynomial σ (R ⧸ I)`, viewed as an `R`-linear
map via the quotient algebra structure. `polynomialVectorReduction I n`
applies it at every coordinate of an actual `Fin n` vector. The kernels
are respectively `I • ⊤` in the polynomial and polynomial-vector modules.
No finiteness assumption on `σ` is needed for these assertions. To prove the
first equality, a polynomial reducing to zero has every coefficient in `I`;
its finite monomial expansion then lies in the ideal multiple. Conversely,
quotient scalars from `I` act by zero. The vector equality follows by the
finite expansion into single-coordinate vectors and the corresponding
coordinatewise converse.

`homogeneousPolynomialVectorComponent n d` applies Mathlib's degree-`d`
homogeneous component to each vector coordinate. Its values lie in the
actual degree-`d` submodule `homogeneousPolynomialVectors R σ n d`, and
it fixes this submodule, so its range is exactly that submodule. Applying
this projection to ideal multiples gives

`homogeneousPolynomialVectors R σ n d ⊓ I • ⊤ =
 I • homogeneousPolynomialVectors R σ n d`.

`homogeneousPolynomialVectorReduction I n d` restricts vector reduction to
that homogeneous source while retaining the full vector space over the
quotient ring as target. Its kernel is `I • ⊤` in the homogeneous source
module itself. The proof maps the kernel along the injective subtype map,
uses the full-vector kernel equality and the preceding intersection
equality, and reflects equality through the injective map. These projection
and reduction statements hold over every commutative ring.

The lifting theorem `valuationKernel_le_of_reduction_image_le` has separate
ring, source and target universes. Here `R` is a valuation domain, `M` is
a finite `R`-module, `N` is torsion-free over `R`, and `P` is any `R`-module.
For linear maps `f : M →ₗ[R] N` and `g : M →ₗ[R] P`, assume
`ker g = I • ⊤`, `I ≤ Ideal.jacobson ⊥`, and `L ≤ ker f`. If the image of
`ker f` under `g` is contained in the image of `L`, then `ker f ≤ L`.
The valuation hypothesis permits fields and arbitrary rank. Given `x` in
`ker f`, image containment supplies `y` in `L` with `g x = g y`. Thus
`x - y` belongs to `ker f ⊓ I • ⊤`, which the imported split-kernel result
identifies with `I • ker f`. Consequently `ker f ≤ L ⊔ I • ker f`.
The imported valuation-kernel finiteness result and Mathlib's Nakayama lemma
give the claimed containment.

Finite generation of full polynomial relation modules, homogeneous residue
generator lifting, homogenization and the host two-axis extension statement
remain outside this contribution.
