# Difference cocycles for homomorphisms with equal quotient maps

This is an internal construction from the published all-test kernel,
normalized-conjugation action, cocycle and rational-conjugacy interfaces.
Its provenance is the elementary identity relating the difference of two
group homomorphisms to a cocycle; it asserts no additional structural
theorem from the literature.

Let `S` be any base scheme. Let `n : N → G` and `q : G → Q` be actual
group-scheme homomorphisms such that the all-test range of `n` equals the
range of the actual kernel inclusion of `q`. Let `i₀,i₁ : H → G` satisfy
`i₀ ≫ q = i₁ ≫ q` as homomorphisms, with the same source `H`.

`normalized` proves that the range of `n` is normalized by the range of
`i₀`: membership in the kernel is preserved by conjugation, as checked
on every relative test scheme. `exists_difference` applies the same
kernel membership criterion to the actual morphism `i₁ i₀⁻¹` on `H`.
The equality of quotient maps makes its composite with `q` the identity.
`difference` chooses the resulting morphism `H → N`, and
`difference_comp` and `comp_difference_comp` give its exact composite
with `n`, both universally and at every test point. These constructions
do not require that `n` be a monomorphism.

For the remaining declarations the underlying map of `n` is assumed
monic. `action` is the published actual normalized-conjugation action of
`H` on `N`, induced by `i₀`. `action_act_comp` expresses this action after
composition with `n`. `cocycle` constructs an actual cocycle with parameter
scheme `S`: its morphism on `S ×_S H` is the second projection followed
by `difference`. Its identity and cocycle equations follow by monic
cancellation against `n`, the displayed difference formula, and group
identities on each test scheme. `cocycle_eval` identifies its evaluation
with the pullback of `difference`.

For any supplied base point `v` of `N`, `cocycle_eq_coboundary_iff` proves
that this cocycle equals `action.coboundary v` exactly when conjugation
by the image of `v` carries `i₀` to `i₁` as actual homomorphisms. In each
direction the proof evaluates the cocycles, composes with `n`, and uses
the group identity

`b a⁻¹ = v (a v⁻¹ a⁻¹)  ↔  v a v⁻¹ = b`.

The forward direction uses the all-test extensionality of group-scheme
homomorphisms. The reverse direction uses monic cancellation and the
all-test extensionality of actual cocycle morphisms. The unique map from
each test scheme to `S` identifies the parameter point with the
pullback used in `constantPoint`.

Finally, `subgroupConjugate_of_coboundary` uses the image of `v` as the
base-point conjugator and the identity isomorphism of `H` to produce the
existing `SubgroupConjugate i₀ i₁` predicate. Over a field this is rational
conjugacy. The module does not assert that every cocycle is a coboundary,
that a vector-group or torus structure exists, or that full maximal-torus
conjugacy has been proved. Those remain separate obligations.
