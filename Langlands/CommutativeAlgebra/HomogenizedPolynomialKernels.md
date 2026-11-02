# Homogeneous relations and polynomial coherence over valuation domains

This internal algebraic construction removes the grading hypothesis from the
finite-generation result in `GradedPolynomialKernels`. It proves that kernels
of all maps between finite free modules over a polynomial ring in finitely many
variables over an arbitrary valuation domain are finitely generated. Consequently
these polynomial rings satisfy `FiniteFreeSubmoduleCoherent`. Fields and
valuation domains of arbitrary rank are included.

## Graded submodules with kernel pieces

`polynomialGradedSubmodule_fg_of_piece_kernels` concerns an actual
`MvPolynomial σ R`-submodule `K` of `Fin n → MvPolynomial σ R`. Here `R` is a
commutative valuation domain, `σ` is finite, and the ring, variable type and
target module may occupy independent universes. Its assumptions are:

- `K` is closed under every homogeneous-component projection.
- `F` is an `R`-linear map from the full vector module to an `R`-torsion-free
  module `N`, and every member of `K` is killed by `F`.
- Every homogeneous vector killed by `F` belongs to `K`.

Its conclusion is finite generation of `K` over the polynomial ring. In each
degree, `K` is therefore exactly the kernel of `F` restricted to the finite
`R`-module of homogeneous vectors. The proof extracts finitely many residues
of homogeneous members of `K`, using Noetherianity of the finite vector module
over the residue-field polynomial ring. Their polynomial span is graded and
lies in `K`. Surjectivity of coefficient reduction lifts all residue spans.
Projecting these lifts to each degree and applying the previously constructed
valuation-kernel Nakayama lemma proves equality in that degree. Finite
homogeneous decomposition then gives equality of the full submodules. The
argument does not assume that `F` is polynomial-linear or that its full kernel
is finitely generated.

## Evaluation and homogeneous lifts

`polynomialDehomogenization` is the actual `R`-algebra homomorphism
`MvPolynomial (Option σ) R →ₐ[R] MvPolynomial σ R` that sends `X none` to `1`
and `X (some i)` to `X i`. It is a left inverse to renaming by `Option.some`.
`polynomialVectorRename` applies this renaming coordinatewise and is `R`-linear.
`polynomialVectorDehomogenization` applies evaluation coordinatewise and is
semilinear for the displayed polynomial-ring homomorphism.

`polynomialVectorHomogenize D x` is the finite sum, for `d ≤ D`, of
`(X none)^(D-d)` times the renamed degree-`d` component of `x`.
`polynomialVectorHomogenize_mem` proves that it is homogeneous of degree `D`.
Choosing `D` from the finite homogeneous decomposition of `x` gives
`exists_homogeneous_polynomialVector_lift`: a homogeneous vector over the
larger polynomial ring whose dehomogenization is exactly `x`. These lift
constructions require only a commutative coefficient ring and an arbitrary
variable type; no valuation or finite-variable assumption is needed.

## Arbitrary polynomial relations

For a polynomial-linear map `f` between finite polynomial-vector modules,
`homogeneousPolynomialRelations f` is the polynomial span, in the ring with
the additional variable, of all homogeneous vectors `y` such that
`f (polynomialVectorDehomogenization n y) = 0`. This definition and its
containment in the inverse image of the actual kernel require only a
commutative ring and arbitrary variables.

Over a valuation domain with finitely many variables,
`homogeneousPolynomialRelations_fg` proves this span is finitely generated.
It is graded because its generators are homogeneous. It lies in the kernel
of the `R`-linear composite of vector dehomogenization and `f`. In each degree,
every vector killed by that composite is a defining generator, so the
kernel-piece theorem applies; the full target vector module is torsion-free
over `R`.

`polynomialKernel_fg_of_valuationRing` identifies the semilinear image of this
finitely generated submodule with `LinearMap.ker f`. One containment follows
from its defining relation condition. For the reverse containment, a relation
has a homogeneous lift, and that lift is itself a defining generator. The
scalar homomorphism is surjective by polynomial renaming, so finite generation
passes to the semilinear image.

Finally, `finiteFreeSubmoduleCoherent_mvPolynomial_of_valuationRing` takes a
finitely generated submodule `K` of a finite free polynomial module and chooses
a finite free surjection onto `K`. Composing with its inclusion has finitely
generated kernel by the preceding theorem; the inclusion is injective, so
this is also the kernel of the surjection. The resulting finite presentation
is precisely the condition `FiniteFreeSubmoduleCoherent`.

## Provenance and scope

These are internal derived constructions using the preceding graded-kernel,
residue-kernel and valuation-kernel results and Mathlib's actual polynomial,
module and finite-presentation operations. The explicit homogenization and
image argument justify the passage from graded kernels to arbitrary matrices;
no external theorem of polynomial coherence is assumed.

This module establishes polynomial coherence. It does not establish finite
projective dimension in all variable counts, smooth or etale permanence, local
Picard vanishing for the geometric rings, or the exact two-axis bundle extension
theorem. Those remain separate obligations of the host task.
