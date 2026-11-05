# Actual coefficients on coherent smooth orbit sections

Worker 200. This derived construction descends the existing actual induced
coefficient map to coherent smooth sections on a discrete-series orbit. The
source is Waldspurger V.1, printed p.288/PDF p.54, which defines `E_P^G` by
coefficients of actual normalized induction, and VI.1, printed pp.295–296/
PDF pp.61–62, which requires section coherence under all representative
equivalences. The full action used here is the one introduced in the proof of
Proposition VI.4.1, printed p.306/PDF p.72. Registered source:
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The representative descent and uniform-invariance arguments are internal
derivations from those actual objects and the published transport theorems.

## Objects and explicit hypotheses

The group, norm-character index, inducing-carrier and finite parameter-index
universes are independent. The group is locally compact, nonarchimedean,
second countable and Hausdorff, with its Borel measurable structure. The actual
subgroups `P`, `M`, `U` have a supplied semidirect decomposition, closed `U`
and `P`, and locally compact `P`. The fixed `K` is compact open, and `G = P K`
in the displayed elementwise sense. The ambient group is unimodular, and the
actual modular character of `P` is the positive radical Haar modulus. The norm
characters and Levi projection are continuous. These are the inherited explicit
premises of the actual compact-probability coefficient construction.

The inducing object `π` is irreducible admissible in the canonical smooth
category. A supplied normal central subgroup `C`, measurable quotient and Haar
measure `μ`, together with square integrability of `π` modulo that same
quotient, select the existing actual `discreteSeriesOrbit`. No Borel structure
or inversion invariance for this central quotient measure, finite central norm
quotient, compact-open cofinality, formal degree or positive inducing form is
required by this coefficient map. There is no topology, norm or dimension
assumption on the inducing carrier, and no induced irreducibility assumption.

The domain is precisely the existing `productInducedSmoothOrbitSections`: a
normalized product-induced value at every actual inducing representative,
coherent under every inducing equivalence, with finite scalar-smooth compact
restriction in the fixed torus coordinates. This unit uses the existing
section space and the existing orbit, with no replacement quotient or carrier.
No continuity of the coordinate equivalence or character-orbit measure is
needed for the map, integral formula or common bi-invariance theorem.

## The actual coefficient function and its descent

`unitaryOrbitRepresentativeCoefficientMap` is the published
`CompactInduction.coefficientMap` at each actual representative. It uses the
same compact Haar probability and the same actual induced-duality comparison.
The elementwise `P K` factorization is only rewritten into the membership
format required by that construction. No scalar prefactor is introduced.
Waldspurger V.1 defines `E_P^G(v ⊗ ℓ)(g) = ℓ(π(g)v)` under the induced tensor
identification; the imported compact coefficient map implements this through
its proved actual tensor/duality equivalence and diagonal integral.

The representative transport theorem applies the existing pointwise transport
invariance of that same coefficient map, including its inverse pullback on
smooth-dual functionals. `unitaryOrbitCoefficientMap` then chooses an inducing
representative of each actual orbit class and applies its map to the section's
value there. This is complex-linear in the section, with values in actual
locally constant functions on `G` indexed by actual orbit classes.

The representative-evaluation theorem proves choice independence. Two
representatives over the same orbit element have equal canonical smooth
classes, hence an actual inducing equivalence. Section coherence identifies
their values under that equivalence, and coefficient transport identifies the
resulting entire locally constant functions. Thus every representative gives
the same function as the auxiliary choice. The parameter theorem specializes
this equality to the literal representative at `e.symm z` and the actual
`discreteSeriesOrbitMap`.

The integral theorem identifies this descended coefficient at every actual
representative and every `g` with the integral over `K` of the contraction of
the original product-induced value at `(k*g,k)`. The measure is exactly the
published compact Haar probability. Its imported integrability theorem proves
genuine convergence for each such contraction; the formula does not rely on
an unspecified tensor expansion or a nonintegrable totalized integral.

## The full action and a common bi-invariance subgroup

For the action on smooth sections, the additional
`HasLaurentUnitaryCoordinates ν e` premise is precisely the algebraic coordinate
condition of the separate full-action construction. That construction proves
full stability rather than assuming it. The coefficient action theorem reduces
an arbitrary actual orbit class to a representative and applies the existing
fiber coefficient action identity. For `x = (x₁,x₂)` the coefficient argument
is `x₂⁻¹ * g * x₁`, with this order and these inverses unchanged.

The common bi-invariance theorem needs no Laurent premise, because it uses the
published whole-section compact stabilizer. There is one compact open `H ≤ K`
whose product fixes the entire original section, uniformly over all parameters
and representatives. At each representative, the product element `(l,k⁻¹)`
fixes the section value. The fiber coefficient action identity then gives
invariance under `g ↦ k*g*l`. The same `H` works for every actual orbit class,
every `g` and both subgroup elements. It is not an intersection of separately
chosen coefficient stabilizers.

## Remaining scope

This unit supplies the actual orbit coefficient function, its original integral,
representative and parameter comparisons, full equivariance and uniform
bi-invariance. Smoothness or continuity in the orbit parameter is a separate
consumer obligation. It constructs no wave-packet integral, density weighting,
Schwartz estimate, Fourier transform or inversion map, and proves no form of
Plancherel surjectivity or whole-task completion. The fixed compact normalization
is retained throughout; independence under changing that compact model is not
asserted here.
