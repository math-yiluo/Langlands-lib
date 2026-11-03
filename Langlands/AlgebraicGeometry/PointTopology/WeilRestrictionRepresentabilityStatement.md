# Representability on arbitrary test schemes

Worker 105 states the all-test-scheme universal property of the actual affine
finite-type Weil restriction used in Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), Example 2.4, printed page 3.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The source invokes the affine finite-type representing scheme. This target
spells out the universal property implicit in that terminology.

For commutative rings `A` and `B` with an `A`-algebra structure on `B`, assume
that `B` is finite and projective as an `A`-module. Let `X` be an actual
affine scheme over `Spec B`, with locally finite-type structure morphism.
Its affine structure morphism is quasi-compact, so this is full finite type.
`WeilRestrictionRepresentabilityProperties A B` asserts that, for every
actual scheme `T` over `Spec A`, the existing canonical map

`Hom_A(T, affineWeilRestriction A B X) → Hom_B(T ×_{Spec A} Spec B, X)`

is bijective. This specific map is `affineWeilRestrictionComparison`: it
pulls back the test morphism and composes with the constructed universal
counit. Its naturality in every test-scheme morphism is already an intrinsic
law of that construction.

The target imposes no affineness, quasi-compactness, quasi-separatedness,
separatedness or finiteness condition on `T`. It adds no topology,
Noetherianity, finite presentation, field or faithful-module hypothesis.
As in the preceding algebraic construction, this extends the source's
ring-extension setting to arbitrary finite projective coefficient algebras:
the algebraic universal point and tensor presentation do not require
injectivity of `A → B`. This extension asserts no coefficient embedding.

This is a Prop-valued statement target. The imported construction already
gives the actual-pullback equivalence on every relative spectrum test and
identifies its forward map with the canonical comparison. The extension to
all test schemes requires a separate proof; neither that proof nor the
topological and whole-paper conclusions is claimed by this statement unit.
