# Kernel cocycles obstructing lifts of quotient points

This internal construction uses the published actual group-scheme kernel,
all-test cover cocycles, and effective-epimorphism descent. It is an auxiliary
exactness result for the local Kneser--Tits proof task, not an arithmetic
vanishing theorem.

Let `n : N → G` and `q : G → Q` be homomorphisms of actual group schemes over
an arbitrary scheme `S`. Assume the underlying map of `n` is a monomorphism
and its full range subfunctor equals the range of the scheme-theoretic kernel
of `q`. Fix a point `y` of `Q` over `S`, an object `U` over `S`, and a
morphism `g : U → G` lifting the restriction of `y`.

`obstruction` is an actual `Cocycle N U`. On every test scheme and every pair
`a,b : Z → U`, its image under `n` is `g(a) g(b)⁻¹`.
The quotient kills this difference because both quotient images are the
restriction of `y`. The existing `Cocycle.lift` constructs the unique
kernel-valued cocycle from these all-test factorizations.

If `U → S` is an effective epimorphism, `isTrivial_iff_exists_lift` proves that
this cocycle is trivial exactly when there is a point `x` of `G` over `S`
with `q(x)=y`. For the forward direction a trivializing cochain `f : U → N`
corrects `g` to `n(f)⁻¹ g`. Its two restrictions to any test scheme agree,
so the published `exists_section_of_forall_eq` descends it. The quotient
of the correction is the identity; epimorphy verifies that the descended
point still maps to `y`. For the reverse direction `g x⁻¹` lies in the
full kernel over `U`; its factorization through `n` is a trivializing
cochain. Cancellation after the monomorphism verifies its coboundary
equation on every test scheme.

`surjective_of_local_lifts` applies this construction to every base point
on one fixed effective-epimorphism cover. If every such point has a lift on
that cover and every `N`-valued cocycle on that cover is trivial, then the
map from `G`-points over `S` to `Q`-points over `S` is surjective. Its proof
constructs the obstruction of each local lift, applies the supplied
vanishing hypothesis, and uses the forward exactness implication. The
cover is arbitrary; no finite-separability or local-field hypothesis is
needed for this conditional deduction.

The theorem assumes a supplied local lift. It proves neither existence of
such lifts nor vanishing of kernel cocycles. It constructs no Galois
cohomology set and asserts no comparison with one. In particular the
unconditional local Kneser--Tits statement remains unproved.
