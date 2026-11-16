# Affine cocycle reductions over arbitrary base schemes

This internal helper extends the cocycle reduction interface of
`SplitUnipotentAffineTorsorProof` from spectrum bases to arbitrary schemes.
The existing declarations remain unchanged. The base scheme and all test
schemes are in an arbitrary universe `u`.

`AffineCocycle.CocyclesVanish H` means that after base change to every affine
test scheme over the base, each cocycle on an affine flat surjective cover
is trivial. On `Spec R` this is definitionally the existing
`SplitUnipotentAffineTorsor.CocyclesVanish` predicate. No filtration or
vanishing assertion is built into the predicate.

The trivial-group case follows from the all-test equality of the identity
image with the trivial subgroup functor. For the two step lemmas, the kernel
inclusion is a monomorphism whose image is exactly the quotient kernel.
The quotient-section lemma assumes both source and quotient schemes are
affine and the quotient map is flat, surjective and locally of finite
presentation. It uses vanishing for the kernel on the quotient itself.
Its coboundary lifts into the kernel; trivializing the lift supplies an
invariant corrected point, which descends along the effective epimorphism
to a section of the quotient map.

Given any section of the quotient map, `cocyclesVanish_of_section` applies
vanishing for the quotient to an arbitrary cocycle, lifts its primitive
using that section, and twists. The twisted cocycle lies in the kernel.
Vanishing there and the published untwisting lemma give triviality in the
original group. Both proofs reuse the published arbitrary-base kernel
lemmas and retain their actual subgroup-image hypotheses.

`exists_section_of_cocyclesVanish` extracts a section of a torsor after an
affine test base change. Quasi-compactness supplies compactness of its
total scheme over the affine base, allowing one affine flat surjective
cover; the torsor cocycle is trivial on that cover and its corrected point
descends. `cocycle_isTrivial` applies the same vanishing predicate at the
identity map and uses the published group identity-base-change isomorphism
to transport its primitive back to the original group.
`exists_section_of_cocyclesVanish_at_base` combines this with the same cover
construction for a torsor under the original group.

The implemented proofs generalize the existing spectrum-base reductions;
their descent and kernel calculations require no spectrum presentation of
the original base. This explains their internal provenance. The module
provides no vector-bundle base-change theorem, no series induction,
no radical filtration or Levi torsor construction, and no unconditional
proof of affine Levi existence.
