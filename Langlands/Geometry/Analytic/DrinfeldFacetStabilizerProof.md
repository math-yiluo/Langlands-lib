# Compact openness of the determinant-norm-one facet stabilizer

`Langlands.Analytic.DrinfeldUpperHalfSpace.facetStabilizerCompactOpen` proves
`FacetStabilizerCompactOpenStatement` at the published universe. The field
has the hypotheses `NontriviallyNormedField F` and `ProperSpace F`.
The ultrametric inequality used below is the one supplied by each
`VectorNorm` in the facet.

## Proof

For a vector norm `ν`, the sum of its values on the standard coordinate
vectors gives a bound for `ν` in terms of the sup norm. Lean uses the
associated seminorm and this bound to prove continuity. Every nonzero
vector can be scaled to the sup-norm unit sphere by the inverse of a
coordinate of maximal norm. The sphere is compact by properness of the
finite product of copies of `F`, and `ν` has a positive minimum there.
Homogeneity extends that minimum to a positive lower bound for the ratio
of `ν` to the sup norm. Consequently every closed sublevel of `ν` is
compact.

The matrices `A` satisfying `ν(x A) ≤ ν(x)` for every row vector `x`
form a closed submonoid. Applying the inequality to each coordinate
vector bounds the rows of `A` in compact sublevels, so the submonoid is
compact. The subgroup `P_ν` preserving `ν` is the subgroup of matrix
units for which both the matrix and its inverse lie in this submonoid.
It is compact by `Submonoid.units_isCompact`. To prove openness, use
compactness of the unit sphere to obtain `ν(x A - x) < ν(x)` uniformly
on the sphere for `A` near the identity. Scaling extends the inequality
to all nonzero vectors. The ultrametric inequality then gives
`ν(x A) ≤ ν(x)` for all `x`. Continuity of the matrix and inverse matrix
projections gives a neighborhood of the identity in `P_ν`.

The continuous multiplicative determinant norm is one on `P_ν` by
`eq_one_of_isCompact` from `Langlands.Topology.CompactNormCharacter`.
Suppose `ν` is a lattice norm and `g` fixes its class with determinant
norm one. Then `g • ν = c ν` as functions for some `c > 0`. Evaluating
at a fixed nonzero vector expresses `c` as `‖a / b‖` for two field
elements supplied by the lattice-norm condition. Multiplying `g` by the
scalar matrix of `(a / b)⁻¹` gives an element of `P_ν`. Its determinant
has norm `c⁻⁽ᵈ⁺¹⁾`, so `c = 1` and `g` itself lies in `P_ν`.

For a source vertex represented by `ν`, the determinant-norm-one
elements carrying it to a given target vertex form an empty set or a
left translate of `P_ν`. Each such set is compact and open. For each
source vertex, take the union over the target vertices in the facet,
then intersect over the source vertices. The resulting set is exactly
the determinant-norm-one part of the setwise stabilizer because each
group element acts by a bijection and the facet is finite. Both index sets come
from the nonempty finite lattice chain. The finite unions are compact
and open, and their intersection is closed in one of them and is open.

## Provenance

Harris explains the compactness of his subgroup `S(ê)` using
stabilization of a facet and the kernels of the absolute values of
algebraic characters. The Library theorem is the split matrix-factor
analogue, using `det` for the character condition and the Library's
building of norm classes. Michael Harris, *Galois properties of
cohomological automorphic forms on GL(n)* (1999), §2, printed
pp. 303–304 (PDF pp. 5–6), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Worker 244 formalized the proof. Worker 355 checked the scope and source
comparison.
