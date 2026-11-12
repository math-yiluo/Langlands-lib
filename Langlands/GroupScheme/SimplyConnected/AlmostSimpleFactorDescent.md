# Descent of fixed almost-simple factors

This internal construction by Worker 166 starts with an actual finite
simply connected almost-simple product presentation `D` of `G_L`, for
fields `k`, `E` and `L` in an arbitrary universe and compatible algebra
structures forming a scalar tower. The base-changed ambient group is
assumed smooth and affine. The descent additionally assumes that `G` is
affine and that `L/E` is Galois; no finite-degree assumption is made on
`L/E`.

A comparison isomorphism from `(G_E)_L` to `G_L` is supplied, together with
its compatibility with the successive projections to the original group
`G`. The chosen factor index is assumed fixed under every `E`-algebra
automorphism of `L`, viewed as a `k`-algebra automorphism. These are
explicit inputs of `exists_factor_descent_of_fixes` and
`factorDescentOfFixes`.

The construction returns an actual affine group scheme `H` over `E`, an
actual closed inclusion into `G_E`, and an isomorphism `H_L ≅ D.factor i`.
Its exact recovery equation says that the base-changed inclusion equals
the recovery isomorphism followed by the original factor inclusion and
the inverse comparison. Thus it retains the embedding of this specific
factor in the original base-changed group, not merely its isomorphism
class. `factorDescentOfFixes` chooses these data from the proved existence
result.

The supporting `descentPoint_left_fst` lemma shows that changing a test
scheme's structure along a base endomorphism preserves its projection
to the original group. `descentPoint_comp_of_fst` uses this fact to show
that a homomorphism preserving the two projections intertwines the
changes of test-scheme structure. All these assertions quantify over
every relative test scheme. Extensionality and the published membership
criterion then prove `SubgroupFunctor.descentTransport_comap_of_fst`.

For the descent proof, the range of the original factor inclusion
followed by the inverse comparison is its inverse image under the
comparison. The preceding transport lemma and the published canonical
factor-range formula prove that this range is Galois invariant. The
published arbitrary-Galois closed-subgroup descent theorem supplies the
actual model, inclusion and recovery equation. This is a derived
construction from the existing transport and descent interfaces; it
introduces no classification premise.

This module does not itself construct the tower comparison or a
stabilizer field, discharge the fixed-index hypothesis for that field,
reflect geometric or simple-connectedness properties, or prove the
final Weil-restriction statement. Those remain separate obligations of
the host task.
