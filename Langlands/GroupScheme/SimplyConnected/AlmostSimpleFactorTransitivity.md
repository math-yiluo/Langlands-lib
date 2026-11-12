# Canonical factor orbits and transitivity

Worker 166. This is an internal derived construction from actual product
coordinates, canonical Galois transport and invariant closed-subgroup descent.
It introduces no external structural premise. All fields and groups lie in an
arbitrary universe.

## Detecting extreme ranges

For an actual finite simply connected almost-simple product presentation `D`
over any field, `eq_empty_of_range_subproductInclusion_eq_bot` proves that a
subproduct with trivial all-test range has empty index subset. If a selected
factor existed, its inclusion would have trivial range. Composing each of its
points with the coordinate retraction would force every point to equal the
identity, contradicting that factor's noncommutativity.

Conversely, `eq_univ_of_range_subproductInclusion_eq_top` proves that a subproduct
with full all-test range uses every index. For an omitted index, every point of
that factor would lie in the subproduct. The outside-coordinate membership
criterion would again force all points of that factor to be the identity.
These two lemmas require neither a Galois extension nor an affine ambient group.

## Actual canonical factor orbits

Let `D` present the base change of a ground-field group `G` from `k` to `L`,
with the base-changed ambient group smooth and affine. `galoisFactorOrbit i`
is the range of the actual map `σ ↦ D.galoisFactorIndex σ i`; this is the
existing canonical subgroup-transport action, rather than a new abstract
action. The identity automorphism places `i` in its orbit. The composition law
and inverse automorphisms prove `galoisFactorOrbit_image`, namely invariance of
each orbit as a subset of the actual factor indices. These constructions do not
require that the extension be Galois or finite.

For `eq_empty_or_univ_of_galoisFactorIndex_invariant`, assume additionally that
`L/k` is Galois, that the original ambient group `G` is affine, and that `G` is
almost-simple. Descend any invariant index subproduct using
`exists_smoothConnectedNormal_subproduct_descent`. This gives an actual smooth
connected closed normal ground-field subgroup and an exact inclusion-recovery
identity. The normal-subgroup clause of `IsAlmostSimple G` forces its all-test
range to be trivial or full. Base change and the recovery identity give the
same alternative for the original subproduct. The two coordinate lemmas above
then force its subset to be empty or the whole index set.

`exists_galoisFactorIndex_eq` applies this alternative to the orbit of a chosen
index. The orbit contains that index, so it is the whole set. Therefore, for
any indices `i` and `j`, an actual field automorphism `σ : L ≃ₐ[k] L` sends `i`
to `j` under the canonical factor action. The statement allows empty index types;
it does not by itself construct an index. No perfectness, characteristic or
finite-degree assumption is imposed.

The selected-factor field descent and the final Weil-restriction comparison
remain separate obligations.
