# JPSS functions on the left-unipotent quotient

Worker 31 implements the scalar integral formulas of Jacquet, Piatetski-Shapiro
and Shalika, *Rankin–Selberg Convolutions* (1983), §2.4, printed page 387,
equations (1), (2), and (3), with their preceding conventions. That original
page was read directly while implementing these formulas. The source is registered as
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

For equal positive rank `n + 1`, the implemented function is
`W(g) W'(g) Φ(e_(n+1) g) |det g|^s`, where the two Whittaker functions transform
by the standard character and its inverse. The test function uses the shared
Schwartz–Bruhat space of locally constant, compactly supported functions.
The coefficient field is complex; the matrix field, its absolute value, topology,
and the complex spectral variable are explicit. Rank one is included.

The quotient is `Quotient (QuotientGroup.rightRel N)`: its classes are `N * g`.
It does not use the opposite quotient by `g * N` or assume normality.
The intrinsic descent proof cancels the two character factors, proves that
upper-unipotent matrices have determinant one, and proves they preserve the last
row under left multiplication. This gives an actual representative-independent
function, not a chosen representative formula.
`LeftUnipotentQuotient n F` is by definition the published
`QuotientIntegration.LeftQuotient (upperUnipotent (n + 1) F)`, and every
integrand is the published `QuotientIntegration.descend` applied to the proved
invariance. No JPSS-specific quotient type or descent operation is introduced.

For corank one, `corankOneIntegral` integrates
`W(diag(g,1)) W'(g) |det g|^(s - 1/2)` on the smaller group's left quotient.
The inclusion uses the group owner's actual `rankInclusion`. The construction
proves that it maps upper-unipotent matrices to upper-unipotent matrices and
preserves the first-superdiagonal character. The original page's sentence
introducing (2) prints `r = t - 1`; the displayed block matrix and the general
formula (3) instead require the first representation to have rank `t + 1`.
This implementation follows those displayed formulas and their dimension
requirements, including the final specialization sentence on that page.

For arbitrary unequal positive ranks, the smaller rank is `t = n + 1` and the
larger is `r = n + (j + k + 1) + 1`, with `j,k` arbitrary natural numbers.
Thus `r - t = j + k + 1` and `0 ≤ j ≤ r - t - 1`. These parameters cover all
the larger-first families in (3), including smaller rank one and `j = 0`.
The integration variable `x` is an actual `j` by `t` matrix over the field.
The large block matrix is constructed as the product of `diag(g,I_(j+k+1))`
with `1 + X`, where `X` has precisely the entries of `x` in rows `t` through
`t+j-1` and columns zero through `t-1`.

The diagonal inclusion is an iteration of the shared rank map; an entrywise
theorem proves that it is exactly the diagonal matrix claimed. The rectangular
matrix `X` is proved square-zero, so `1 - X` is the inverse of `1 + X`.
The equality `diag(g,I) * X = X` then proves that the resulting invertible
matrix has exactly the displayed source blocks
`[g,0,0; x,I_j,0; 0,0,I_(k+1)]`.
Multiplying `g` on the left by `u` multiplies this matrix on the left by the
diagonal inclusion of `u`, leaving `x` unchanged. Iterated character preservation
therefore proves quotient independence for each `x`. `unequalRankIntegral`
integrates `W(block(g,x)) W'(g) |det g|^(s - (j+k+1)/2)`, first in `x`,
then on the quotient. The source's zero-row specialization is proved: when
`j=k=0`, the integrand is the corank-one integrand, and integration against
unit Dirac mass on the zero-dimensional matrix space recovers the corank-one
integral.

The three `ModelIntegral` wrappers use vectors in the actual coefficient images
of specified representations and specified standard/inverse Whittaker
functionals. They do not replace a model by an unconstrained family of scalar
functions. The underlying function versions are also reusable on the full
character-equivariant spaces, without asserting smoothness or convergence for
every such function. Independent universes for the field and the two
representation carriers are retained. No topology is imposed on either carrier.

All three scalar integrals expose their measures. `EqualRankConverges` and
`CorankOneConverges` mean integrability on the quotient; `UnequalRankConverges`
means integrability on the product of the quotient and rectangular matrix
spaces. These predicates are separate because Lean's total Bochner integral is
also defined outside the convergence domain. No Fubini theorem under omitted
measure hypotheses is asserted. The measurable spaces are explicit arguments;
the usual Borel structures can be supplied.

The present module does not assert that arbitrary supplied measures are Haar,
normalized, or compatible with a Weil integration formula. Constructing the
compatible quotient measure in ranks above one, proving convergence and rational
continuation, and applying the rational zeta algebra to construct actual
normalized factors remain separate work. The smaller-first
factor convention, functional equation, and factor symmetries are also not
deduced from these scalar definitions. No rational local factor is constructed
here, and the full assigned local-factor framework remains incomplete.

The determinant absolute value `abv : AbsoluteValue F ℝ` is an explicit
argument, so the formulas apply to the generic field interface of
`Langlands.HarmonicAnalysis.Basic`. For the p-adic field interface, the
published `Langlands.PadicField.TopologicalData.determinantNorm` in
`Langlands.Group.GL.NormalizedCharacter` is the analogous residue-normalized
character `g ↦ |det g|`. This module states and proves no bridge between the
two; a consumer that needs one must prove it.

The measurable structures are explicit instance arguments. On the rectangular
matrix space the usual choice is Mathlib's `Matrix.instMeasurableSpace`, and
the published `Langlands.RankinSelberg.rectangularMeasure` in
`Langlands.Representation.RankinSelberg.Measures` supplies the shared additive
Haar product measure `ν`, including the unit Dirac mass for zero rows. In rank
one, `Langlands.Representation.RankinSelberg.RankOneQuotient` supplies a
compatible quotient measure `μ`. No compatible quotient measure is supplied
here for higher ranks.

Imports: `Langlands.Representation.Whittaker.GeneralLinear` is submitted in the
same candidate. `Langlands.Group.GL.RankMaps` (Worker 6's geometry branch) and
`Langlands.Analysis.Local.QuotientMeasure` are published Library modules,
imported unchanged by Lean name. The shared harmonic primitives reach this
module through GeneralLinear; they remain Worker 20's.

Mathlib is pinned at `5ed2965256430c3649e86755f9576b54eca72435`, Lean 4.34.0.
The construction uses `Matrix.det_of_isUpperTriangular`, entrywise matrix
operations, the published rank maps, `Quotient.inductionOn`, and Mathlib's
complex power and scalar Bochner integral. The quotient relation
`QuotientGroup.rightRel` and the descent through `Quotient.lift` are those of
the published QuotientMeasure module. The determinant theorem was inspected in
the pinned source. Existing
`MeasureTheory.Measure.Haar.Quotient` machinery does not immediately supply the
needed general nondiscrete unipotent quotient measure; this file deliberately
leaves that mathematical construction visible.
