# Graded polynomial kernels over valuation domains

This internal development constructs polynomial-semilinear coefficient reduction
and proves finite generation of an actual polynomial kernel when that kernel
is closed under homogeneous degree projections. It builds on the valuation
split-kernel and residue/Nakayama modules and on Mathlib's homogeneous
polynomials and Hilbert basis theorem. No external literature result is assumed.

For a commutative ring `R`, a variable type `σ`, and a finite coordinate set
`Fin n`, `PolynomialVectorGraded K` means that the actual
`MvPolynomial σ R`-submodule `K` of polynomial vectors is closed under every
`homogeneousPolynomialVectorComponent n d`. This is an explicit closure
condition, not an assumption that an arbitrary matrix is homogeneous.

The component lemmas first prove that projection of a homogeneous vector of
degree `e` to degree `d` gives that vector when `d = e`, and gives zero
otherwise. Multiplying a homogeneous scalar of degree `d` by a homogeneous
vector of degree `e` gives a vector of degree `d + e`. Every vector is a
finite sum of its homogeneous components: take the maximum coordinate total
degree as a common bound and use Mathlib's polynomial decomposition, with
higher components zero. These assertions do not require finitely many variables.

For a polynomial-vector submodule `L`, the component of a scalar multiple of
a homogeneous vector in `L` is again in `L`. The proof decomposes the scalar
into homogeneous components, projects each homogeneous product, and observes
that the result is either that product or zero. Span induction, strengthened
to all scalar multiples, then proves `polynomialVectorGraded_span`: a span
of homogeneous vectors is closed under projections. Conversely,
`polynomialVectorGraded_span_homogeneous` proves that a closed submodule is
the span of its homogeneous elements, by the finite vector decomposition.

`polynomialVectorQuotientMap I n` is the actual coefficient-reduction map
on vectors, semilinear over the polynomial ring homomorphism
`MvPolynomial.map (Ideal.Quotient.mk I)`. Its underlying function is the
previous module's `R`-linear vector reduction. A coefficient calculation
proves that this reduction commutes with every homogeneous vector projection.
A private finite-extraction lemma says that, in a Noetherian target module,
the span of the image of any set under any function is already the span of
the image of a finite subset of that set. The proof extracts finitely many
image generators and chooses one preimage in the original set for each.

Now let `R` be an arbitrary valuation domain, let `σ` be finite, and let
`f` be an actual polynomial-linear map from `Fin n` polynomial vectors to
`Fin m` polynomial vectors. `polynomialKernel_le_of_reduction` assumes that
`ker f` and a submodule `L ≤ ker f` are closed under projections. For an
ideal `I ≤ Ideal.jacobson ⊥`, suppose every element of `ker f` has the same
coefficient reduction as some element of `L`. Then `ker f ≤ L`.
For a homogeneous element of degree `d`, restrict `f` to the finite
`R`-module of degree-`d` vectors. Project a matching lift in `L` to degree
`d`; closure keeps it in `L`, and reduction compatibility preserves the
matching residue. The residue map on the homogeneous source has kernel
`I • ⊤`. The preceding valuation-kernel Nakayama theorem therefore proves
containment for each homogeneous piece. Decomposing an arbitrary kernel
vector into its components proves the full containment. The target of the
restricted map is the full torsion-free polynomial-vector module, as
required by the valuation-kernel theorem.

The final theorem `polynomialKernel_fg_of_graded` assumes only the valuation
domain hypotheses, finite `σ`, and closure of `ker f` under projections.
Reduce modulo the maximal ideal of `R`. The quotient is a field, so its
polynomial ring in finitely many variables is Noetherian by Mathlib, and
its finite vector module is Noetherian. Apply finite extraction to the
residues of all homogeneous elements of `ker f`; this supplies a finite
subset of actual homogeneous lifts. Let `L` be their polynomial span.
It lies in `ker f` and is closed under projections. The homogeneous-span
equality for `ker f`, polynomial-semilinearity of reduction, and the
surjectivity of the polynomial coefficient quotient map show that every
kernel residue comes from `L`. The containment theorem for the maximal
ideal, which lies in the Jacobson radical, gives `L = ker f`. The finite
spanning set proves the asserted finite generation.

The theorem permits arbitrary valuation rank and fields, and independent
universes for the ring and variable type. It does not prove that arbitrary
polynomial kernels are closed under projections. Homogenization, polynomial
coherence for arbitrary matrices, and the exact host geometric extension
statement remain outside this contribution.
