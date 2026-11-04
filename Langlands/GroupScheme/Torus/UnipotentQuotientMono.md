# Tori in quotients with unipotent kernel

This internal adapter constructs
`IsUnipotent.torusQuotientPointEmbedding`. It is conditional on the existing
proposition `UnipotentClosedSubgroupStatement`; it does not prove that
proposition.

Let `k : Type u` be any field. Let `N`, `T`, `G`, and `Q` be group schemes over
`Spec k`. Assume `N` is affine, locally of finite type, and unipotent in the
existing representation-theoretic sense. Assume `T` is a torus and
`i : T ⟶ G` is a closed subgroup. Let `n : N ⟶ G` be any homomorphism.
Then, assuming closed-subgroup unipotence, the all-test subgroup functors
`range n` and `range i` have trivial intersection. In particular, no
monomorphism or closedness assumption on `n` is needed.

For any homomorphism `q : G ⟶ Q` whose full scheme-theoretic kernel range
is contained in `range n`, the composite `i ≫ q` is a monomorphism over
`Spec k`. The definition packages its map on each test scheme as an actual
function embedding. The application theorem identifies its value with
composition by `i` and `q`, and the naturality theorem proves compatibility
with every test-scheme restriction.

The assumptions impose no splitting of the torus, perfectness or infinitude
of the field, or characteristic restriction. Neither `G` nor `Q` needs to
be affine, smooth, connected, or solvable. The map `q` need not be an fppf
quotient for this injectivity conclusion.

## Implemented proof and provenance

The proof uses the actual group-scheme pullback
`W = subgroupIntersection n i`. Its first projection `W ⟶ N` is a closed
immersion, since it is the base change of the closed torus inclusion `i`.
Thus `W` is affine. The explicit `UnipotentClosedSubgroupStatement` premise
applied to this first projection proves `IsUnipotent W`. The arbitrary-torus
vanishing theorem from `Torus/UnipotentHomNonsplit` makes the second projection
`W ⟶ T` zero. The pullback equation then makes the intersection homomorphism
`W ⟶ G` zero. Its published range comparison proves trivial intersection
on every scheme test, including nonreduced tests.

The preliminary lemma
`mono_comp_of_kernel_range_le_of_inf_eq_bot` works over any base scheme.
If two points `x` and `y` of a monic subgroup have the same image under `q`,
the image of `x⁻¹ * y` belongs to both that subgroup and the full kernel
of `q`. Kernel-range containment and the assumed trivial intersection make
this image the identity. Cancelling the subgroup monomorphism proves
`x = y`. The field-specific result applies this lemma to the intersection
calculation above. The point embedding is composition by the resulting
monomorphism; associativity gives its naturality.

These are internal deductions from the published subgroup pullback and
kernel point APIs and the separately supplied nonsplit-target vanishing
helper. There is no additional literature assertion.

This unit supplies injectivity only. It does not establish closedness or
maximality of the image in `Q`, surjectivity of a torus onto a quotient, a
homomorphic section, existence of a torus lift, or rational conjugacy of
maximal tori. Closed-subgroup unipotence and those further structural
obligations remain separate.
