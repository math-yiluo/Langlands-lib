# Full maximality through quotients with supplied torus lifts

This internal adapter constructs
`IsMaximalTorus.quotientFactorIsoOfTorusLifts`, an actual isomorphism from
the source of a maximal torus to the source of any closed torus through
which its quotient map factors. Its homomorphism is exactly the proposed
factor map.

## Explicit premises and full maximality

The source inclusion `i : T ⟶ G` is maximal in the existing full
`IsMaximalTorus` sense. The ambient groups are affine and `G` is locally
of finite type. The homomorphism `q : G ⟶ Q` has three supplied properties:

- The composite `i ≫ q` is a closed subgroup inclusion.
- Every closed torus `i' : T' ⟶ Q` admits a homomorphism
  `j : T' ⟶ G` with `j ≫ q = i'`.
- For every homomorphism `a : T ⟶ G` with the same quotient map as `i`,
  the maps `i` and `a` are rationally subgroup-conjugate.

Neither full maximality after `q` nor lift existence is inferred from
closedness. Torus lifts and equal-map conjugacy are explicit premises.
No scheme section is converted into a homomorphic lift.

For any proposed factorization `f ≫ i' = i ≫ q`, choose a supplied
lift `j` of `i'`. Its composite with `q` is monic, so `j` is monic.
Affineness of `T'` follows from the closed inclusion into affine `Q`.
The closedness theorem for affine torus monomorphisms makes `j` a closed
torus in `G`. The maps `i` and `f ≫ j` have equal quotient maps.
The comparison premise transfers maximality from `i` to `f ≫ j`.
Applying maximality to its factorization through the closed torus `j`
shows that `f` is invertible. This proves
`IsMaximalTorus.comp_of_torus_lifts` and constructs the stated actual
isomorphism.

## Vector-kernel specialization

In addition to the general ambient hypotheses, assume that `Q` is locally
of finite type over `k`. Suppose the actual all-test range of a monomorphism `n : N ⟶ G`
equals the full kernel range of `q`, and `N` is a vector group of
supplied finite dimension. The theorem
`IsMaximalTorus.comp_of_vector_kernel_torus_lifts` retains the explicit
premises `UnipotentClosedSubgroupStatement`,
`TorusVectorActionLinearizationStatement`, and the existence of
homomorphic lifts of all closed tori of `Q`.

Intrinsic vector-group geometry supplies affineness and smoothness,
and the vector-group unipotence theorem supplies unipotence. The
conditional unipotent-kernel closedness adapter proves that `i ≫ q`
is closed. Linearizing the kernel conjugation action along `i` supplies
coordinates for the published torus vector-cocycle vanishing theorem.
Its equal-map lift-conjugacy consequence discharges the comparison
premise. The general maximality argument applies.

All fields in universe `u`, all characteristics, and nonsplit source
and target tori are included. The module does not prove closed-subgroup
unipotence, linearization, torus lift existence, or the full solvable
maximal-torus conjugacy statement.

## Provenance

This is an internal deduction using the existing full maximality and
conjugacy predicates, torus geometry, the conditional quotient-closedness
adapter, and the vector-kernel conjugacy construction. It makes no new
literature assertion and adds no axiom.
