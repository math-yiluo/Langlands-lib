# Local rational neighbourhoods of strictly represented subsets

`Langlands.Analytic.StrictTestDomain.LocalRationalNeighborhoodStatement` is the
proposition that the following holds for every complete ultrametric normed field
`K` (universe `u`) whose norm is nontrivial, in the form `∃ c : K, 1 < ‖c‖`.

Let `P` and `Q` be presented strict affinoid algebras over `K`, let
`i : P → Q` be a bounded `K`-algebra map, and let `U` be a subset of the Banach
spectrum `M(P)` such that `Represents K i U` holds: `U` is closed, it is the
image of the spectrum map `M(Q) → M(P)` induced by `i`, and every bounded map
from `P` to a presented strict affinoid algebra whose spectrum map lands in `U`
factors uniquely through `i`. Then for every point `x ∈ U` there is rational
data `d` in `P` (a denominator `g` and finitely many numerators `f_j` with no
common zero on `M(P)`) such that

- the unit-radius rational locus `d.locus = {z | z(f_j) ≤ z(g) for all j}` (where
  `z(f)` is the value of the seminorm `z` at `f`) is
  contained in `U`, and
- `d.locus` is a neighbourhood of `x` in the subspace topology of `U`
  (`d.locus ∈ 𝓝[U] x`).

## Provenance

This is the local form of the Gerritzen–Grauert theorem for strictly affinoid
domains over a nontrivially valued field. In M. Temkin, "A new proof of the
Gerritzen–Grauert theorem", Math. Ann. 333 (2005), 261–269, the proof of
Theorem 1.1 (§2, p.5 of the author preprint) reduces the theorem to the claim that for every point `y` of
`Y` there is a rational domain `X'` of `X` containing `x = ϕ(y)` such that
`ϕ⁻¹(X')` is a neighbourhood of `y` and `ϕ⁻¹(X') → X'` is a closed immersion.
For an affinoid domain embedding `ϕ`, such a closed immersion identifies
`U ∩ X'` with a union of connected components of `X'`, cut out by an
idempotent, so `U ∩ X'` is again a rational domain of `X` contained in `U`.
Since the closed immersion is injective on `ϕ⁻¹(X')`, the fibre `ϕ⁻¹(x)` is
`{y}`, and as `ϕ` is a closed map of compact Hausdorff spectra, `U ∩ X'` is a
neighbourhood of `x` in `U`. This derived local consequence is the statement
recorded here.

The statement here is an internal interface. Its hypothesis uses the
Library's `StrictTestDomain.Represents`, which tests the universal property
only against presented strict affinoid algebras, rather than the full
`PresentedAffinoidAlgebra.Domain` notion; and it records a relative
neighbourhood rather than a global finite cover. The finite cover of the
full-domain statement `PresentedAffinoidAlgebra.Domain.FiniteRationalCoverStatement`
is to be assembled from this local statement by compactness of `U` after a
scalar extension to a field in which all radii become strict.
