# Tate local analysis with concrete Gauss factors

Workers 1786 and 1248 prove
`Langlands.LocalFactor.padicAbelianLocalAnalysis : PadicAbelianLocalAnalysisStatement.{u}`.
The theorem has exactly the published proposition as its type, with no additional
hypotheses. It applies to every prime, finite p-adic extension in universe `u`,
and supplied `TopologicalData`, and uses that topology's Borel measurable space.
The statement and the definitions it imports are unchanged.

This is a derived proof of the published statement. Its mathematical conventions
and original-source correspondence are those explained in
[`PadicAbelianStatement.md`](PadicAbelianStatement.md). The helper modules prove
properties of the existing actual characters, valuation lattices, Haar measures,
Bochner integrals and concrete local-factor expressions. They do not assume the
local-analysis statement or choose a replacement epsilon system.

## Conductors, Haar masses and the Euler factor

`Abelian.LocalAnalysisHelpers` proves the character and conductor clauses.
Continuity and the absence of small subgroups in the complex units give an open
kernel and local constancy. Compactness of the valuation-zero units gives finite
image there; the published smooth-character norm theorem gives modulus one.
The least-level characterization of the actual principal-unit filtration proves
conductor existence, uniqueness, inversion and product laws. The assembly also
supplies the published uniformizer construction.

`Abelian.ZetaAnalysisHelpers` computes the integer-ring and unit-annulus masses
from the valuation-lattice Haar theorem and the difference of adjacent lattices.
It proves positivity, the factor `1 - q^(-1)`, meromorphic normal form of the Euler
factor and its nonvanishing at regular points.

## Actual zeta integrals and finite Laurent continuation

`Abelian.ZetaShells` obtains the Bochner change of variables from each order
shell to the units. The additive Haar factor cancels the shift by one in the
integrand. `Abelian.ZetaConvergence` uses compact shell integrability, the
Schwartz–Bruhat valuation bounds and a geometric-series bound to prove actual
integrability throughout the stated convergence half-plane.

`Abelian.ZetaFiniteFormula` sums the disjoint shells. Compact support bounds
the shells below, and local constancy at zero makes the tail coefficient
constant. `Abelian.ZetaLaurentFormula` converts the finite prefix into a finite
Laurent expression in `q^(-s)`. For an unramified character the Euler denominator
clears the geometric tail; for a ramified character the unit-character average
vanishes. This proves the finite formula for every test function.

`Abelian.ZetaMeromorphic`, `Abelian.ZetaLaurentAlgebra` and
`Abelian.ZetaContinuation` supply its analytic consequences. The Euler factor
times the finite Laurent expression is meromorphic and holomorphic at regular
points. Its meromorphic normal form supplies the continuation. The meromorphic
identity principle gives uniqueness and equality of every punctured germ.
Injectivity of finite spectral Laurent evaluation gives uniqueness of the
coefficients. Normalization preserves regular-point values, so removable
singularities do not introduce an incorrect pointwise identity.

`Abelian.ZetaEulerTest` proves that the published explicit test is a
Schwartz–Bruhat function and computes its zeta integral as the unit mass times
the Euler factor. It uses `Abelian.TateLatticeZeta` for the unramified lattice
integral and `Abelian.GaussDual` for the ramified test's local constancy and
compact support.

## Concrete Gauss expressions and duality

`Abelian.GaussEpsilon` proves the two spectral formulas, entire dependence,
uniformizer and shell independence, Haar scaling, additive-character scaling
and unramified-twist laws directly for the published expressions.
`Abelian.GaussShellVanishing` proves vanishing off the conductor shell by
unit rotation and additive translation. `Abelian.GaussDual` computes the plus
Fourier transform of the ramified unit-annulus test and applies published
Fourier inversion to obtain the Gauss product for dual Haar measures. This
proves the dual epsilon identity. Constructing a positive scalar multiple with
the required dual volume then gives nonvanishing for every Haar measure.
Complex conjugation and the dual identity give the unitary central norm under
the target's self-dual volume condition. All conductor and dual-volume conditions
are exactly those already present in the statement.

## Fourier functional equation

`Abelian.TateLatticeZeta`, `Abelian.TateGaussLattice` and
`Abelian.TateFourierZeta` compute zeta integrals on lattice cosets and Gauss
integrals over lattices. `Abelian.TateFunctionalEquation` uses the published
plus Fourier formula for a coset indicator to prove the functional equation on
the nonempty open strip where both actual zeta integrals converge. The published
single-lattice expansion and finite linearity extend this equation to every
Schwartz–Bruhat function. Fourier closure supplies the required transformed test
function. The meromorphic identity principle then gives the normalized equation
at every punctured germ for any two continuations allowed by the target.

The proof retains the plus kernel `psi(x*y)`, fixed-Haar spectral exponent
`q^(-(n+a)s)`, centered exponent `q^(-(n+a)(s-1/2))`, and inverse-character dual
relation at `1-s`. It derives the Fourier equation by finite coset expansion and
meromorphic continuation.
