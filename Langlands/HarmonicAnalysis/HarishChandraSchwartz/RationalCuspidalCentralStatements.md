# The exact VIII.4 targets and the level inclusion used in VIII.5

Waldspurger (2003), VIII.4, printed p.327 (PDF p.93), defines
`p_χ f(g) = ∫ χ(a)⁻¹ f(a g) da` and states Proposition VIII.4.1.
Theorem VIII.4.2, printed pp.330–331 (PDF pp.96–97), identifies
`p_χ(°C(G))` with the algebraic sum `A₂(G)_χ`. VIII.5, printed
p.332 (PDF p.98), uses the inclusion of the bi-invariant coefficient
spaces into the projected cuspidal space at the same level. This module
states these three analytic obligations on the actual constructed
interfaces. None of the three obligations is proved here.

## Structural inputs and meaning

Each closed proposition quantifies an arbitrary nonarchimedean local
field `F : Type u` with finite residue field, an affine locally finite
type connected reductive group scheme `G`, a maximal split torus
`i : S → G`, a generic cocharacter `ν`, a compact open subgroup `K`
with the displayed minimal Iwasawa pair, and a closed matrix
representation `ρ` on a nonempty finite index set. These are the
choices defining the existing actual `RationalSchwartzSpace` with
rational Xi and matrix height. The group has its canonical
rational-point topology and Borel measurable space.

The split component `s : T → G`, its literal point-image `A_G(F)`,
a Haar measure `muA` on that image and a continuous unitary character
`χ` are also explicit. The coefficient targets additionally quantify
a Haar measure `mu` on the Borel quotient `G(F)/A_G(F)`. Normality
of the quotient subgroup is derived from the centrality of the split
component. This is precisely the quotient and square-integrability
convention used by the existing `DiscreteSeriesClass` interfaces.
These assertions require no Haar measure on the whole group; no
quotient integration formula or choice of a compatible whole-group
measure is used in their statements or in the elementary proof.

There is no characteristic-zero, split-group, quasi-split or
positive-rank restriction. The cuspidal submodule is the constructed
integrable kernel for every proper standard parabolic and all
two-sided translates. The separate closed convergence, vanishing-only
and semistandard comparison targets identify it with the source's
kernel. The recursive VIII.2 projection is still a distinct open
construction: it subtracts weighted proper-parabolic Fourier synthesis
under induction on strictly smaller semisimple rank and the preceding
isometry theorem. This module does not provide or assume that
projection or either recursive-image comparison direction.

## The three closed targets

`RationalCuspidalCentralProjectionFiniteStatement` asserts, for
every compact open `H`, both equality of the carrier of
`rationalCuspidalCentralLevelSpan` with the exact raw
`rationalCuspidalCentralLevelImage` and finite dimensionality of that
span. Thus it states that the actual integral image is a finite
dimensional complex subspace, rather than just placing its elements
in a finite dimensional container. The separate
`RationalSchwartzCentralConvergenceStatement` asserts absolute
convergence and supplies the already proved linear-map interpretation.
Neither convergence nor `CentralWeights` is a premise of the
finiteness target.

`RationalCuspidalDiscreteCoefficientStatement` asserts literal set
equality of `rationalCuspidalCentralImage` with the carrier of the
canonical `discreteSeriesCentralCoefficientSpace`. Its right side is
the algebraic sum of all the existing discrete-series coefficient
spaces with central character `χ`, with no assumed decomposition.
The full comparison uses carrier universe `max u uV`: the actual
right-translation representation on a subspace of functions on
`G(F)` has carrier universe `u`, so a comparison with representations
in an independently smaller universe cannot simply place that
function representation there. The maximum permits it and retains
an arbitrary independent additional universe `uV`. The generic sum,
its transport results and the level-lifting target keep `uV`
independent of the field universe without enlargement. No theorem
identifying coefficient sums across all carrier universes is claimed.

`RationalCuspidalFixedCoefficientLiftingStatement` asserts that for
every compact open `H`, every class in the published
`discreteSeriesCentralFixed A_G hA mu χ H`, and every actual
coefficient of its canonical representative that is bi-invariant
under `H`, the coefficient belongs to the raw
`rationalCuspidalCentralLevelImage` at that same `H`. Membership
means that there exists an actual `H`-bi-invariant cuspidal
Schwartz preimage whose central integral is that coefficient.
This is the precise inclusion used at printed p.332. The source
also uses equivariance to preserve the level; full-space equality
alone is not treated as a proof of this lifting.

No closed target has a constant-term estimate, central convergence,
reproducing kernel or vector, admissibility of a supplied translation
representation, finite dimensionality, same-rank orbit finiteness
or Plancherel as a premise.

## The proved elementary consequence

`RationalCuspidalCentralProjectionFiniteStatement.fixedCoefficientFiniteness`
assumes the two named closed finiteness and level-lifting propositions
and proves finite dimensionality of the already published least
`discreteSeriesCentralFixedCoefficientSpace`, for every displayed
structural choice. The proof applies the published
`finiteDimensional_discreteSeriesCentralFixedCoefficientSpace_iff`.
It chooses the actual projected level span as the finite dimensional
container. Every defining coefficient lies in the raw level image by
the lifting proposition and hence lies in its span by
`Submodule.subset_span`. This elementary implication does not use
Theorem VIII.4.2's full-space equality or prove either analytic input.

The conclusion retains the auxiliary Schwartz choices supplied to
the theorem; it does not assert their existence or silently discharge
the broader `RationalFixedCoefficientFinitenessStatement`. The
published fixed-span-to-orbit-finiteness reduction remains available
once the full fixed-coefficient target is established.

The targets are derived realizations of the cited source statements
on the Library's actual integrable kernel and canonical coefficient
spaces. The analytic VIII.4 proofs, the positive translation
representation, the VIII.2 symmetries and convolution identities,
and the VIII.3 estimates are not provided by this module.
