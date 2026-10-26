# Finite Schwartz expansion from uniform compact support

Author: Worker 108.

The theorem `Langlands.RankinSelberg.unequalRankFiniteExpansion` proves exactly
`Langlands.RankinSelberg.UnequalRankFiniteExpansionStatement.{uF,uV} F T n j k`.
It retains every prime, the supplied p-adic topological data, independent field
and representation universes, all natural numbers `n`, `j`, and `k`, and the
full Whittaker-type scope of the target. Uniform compact support in the
rectangular variable remains an explicit premise. The output consists of one
finite family of Schwartz–Bruhat functions and coefficients in the original
`coefficientModel π ℓ`, chosen before both `g` and `x`. The equality is pointwise.

## Matrix and smoothness prerequisites

The mixed product of any two off-diagonal rectangular blocks vanishes:
`rectangularEntries_mul` proves this entrywise by separating the possible
intermediate column indices. Together with `rectangularEntries_add`, it proves
that `rectangularUnipotent` takes zero to the identity, addition to
multiplication, and negation to inversion. All arguments include zero rows.
The matrix and its explicit inverse are continuous entrywise, giving
`continuous_rectangularUnipotent` by the topology on units.

`exists_compactOpen_rectangular_subgroup` pulls an open subgroup back along the
rectangular unipotent map and intersects its preimage with the integral matrix
lattice. The lattice is compact and open using the supplied p-adic topological
data and the published `T.isCompact_integers` and `T.isOpen_integers` from
`Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof`. The preimage is an
additive subgroup by the matrix identities. The intersection is open and is a
closed subset of the compact lattice, so it is compact. Hausdorffness comes
from `T.fieldT2`, without replacing the supplied topology.

`unequalRank_coefficient_invariant` applies the published `model_isSmooth` to
obtain an open stabilizer of the coefficient model vector. That theorem chooses
a preimage vector in the original representation and uses equivariance of the
coefficient map. Pulling the stabilizer back and intersecting with the lattice
provides one compact open additive subgroup `U`. Evaluating the stabilizer
identity and using `u(x + a) = u(x)u(a)` shows that
`f(D(g)u(x + a)) = f(D(g)u(x))` for every `g`, `x`, and `a ∈ U`, where
`D(g) = appendIdentity n (j + k + 1) g` and
`u(x) = rectangularUnipotent j k x`.

## Finite expansion and coefficient assembly

`unequalRankFiniteExpansion_of_cosetExpansion` isolates the
representation-specific assembly. Its explicit auxiliary hypothesis is a finite
sampled-value expansion for invariant uniformly compactly supported families
on the rectangular space. Smoothness follows from the Whittaker-type premise.
Applying the expansion to
`H g x = f.val.val (unequalRankMatrix j k g x)` supplies a natural number `m`,
Schwartz functions `φ`, and sample matrices `r`, all before `g` and `x`.
The coefficient `fs i` is the actual model vector
`modelRepresentation π ℓ (rectangularUnipotent j k (r i)) f`.
Its evaluation at `D(g)` is definitionally `H g (r i)`, so the expansion gives
exactly the target's sum in the original representation and functional.

The final theorem `unequalRankFiniteExpansion` discharges that auxiliary
hypothesis with the published `Langlands.HarmonicAnalysis.exists_compactCosetExpansion`
from `Langlands.HarmonicAnalysis.CompactCosetExpansion`, using `T.fieldT2` for
the rectangular space's Hausdorff structure. This imported theorem derives
uniform local constancy of `x ↦ (g ↦ H g x)` from subgroup invariance and derives
compact support of that function-valued map from the supplied common compact
set. It uses the finitely many nonzero values of this map: the Schwartz
functions are indicators of the corresponding nonzero fibers, with a sample
chosen in each fiber. These fibers are unions of `U`-cosets; the implementation
does not require them to be individual cosets. The finite fibers partition the
nonzero support, and all summands vanish where the entire family is zero.
This is the alternative finite-fiber proof permitted by the task.

The generic imported construction was authored by Worker 180 and Worker 451.
Their module is used by Lean import; no unreviewed draft proof is copied into
this module. The final theorem has no extra expansion hypothesis. It retains
the target's nonzero functional and Whittaker-type assumptions, although the
implemented argument only needs smoothness from the latter. The zero-row,
zero-support and `m = 0` cases require no added inhabitance hypotheses. No
uniform compact support is proved here, and no measure, integral, convergence,
or almost-everywhere equality enters the conclusion.

## Original provenance

The original source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`. Worker 108 read printed
pp.385–386 and 393–394 visually. The retained scan is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Section 2.1, p.386, equation (3) gives the coefficient convention and stability
under right translations. The unequal-rank argument on p.393 uses compact
rectangular support independent of `g` and a finite reduction; p.394,
equation (7) retains coefficients of the original larger representation.

This pointwise interface was specified by Worker 329 and stated in the
Library by Worker 180. It is derived from the original argument, rather than
a separately displayed source theorem. The elementary matrix and topology
lemmas are internal supporting results; the imported nonzero-fiber argument
is an elementary alternative to enumerating compact open cosets. No registered
JPSS erratum was located in the project or Library notes. The separate uniform
compact-support theorem and the subsequent integration step are outside this
proof's scope.

## Development validation

The complete module passed a Lake build and declaration inspection in
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, check
`effb9c35-ee2b-49bb-a879-4fc23afa1d32`, with zero errors and warnings.
Inspection reports a theorem with independent universe parameters `uF`, `uV`
and only `propext`, `Classical.choice`, and `Quot.sound` as assumptions.
This development check is separate from independent semantic review and the
submission's exact-target validation.
