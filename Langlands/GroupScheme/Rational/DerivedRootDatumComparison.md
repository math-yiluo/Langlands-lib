# Integral root data through the actual derived inclusion

This internal construction compares supplied actual integral root data for an
affine smooth group `G` over a field and its actual derived subgroup `d : D ⟶ G`,
where `D` is affine and locally of finite type. The actual torus square is
`j ≫ d = groupHom e ≫ i`. The tori `T`, `S`, and `A` are split, and a supplied
`c : A ⟶ S` has central composite into `G`. The product of `e` and `c` is flat
and scheme-surjective. The ambient torus map is a monomorphism and has finite
full Weyl image.

`IsRootDatumOf.coroot_comp_of_centralComplement` first proves that whenever an
ambient root restricts to a specified source root, its actual integral coroot is
the source coroot followed by `e`. This lemma only needs the affinity, local finite type of `G`, splitness,
central-product and finite-Weyl-image hypotheses; smoothness, the derived-subgroup
condition, and local finite type of `D` are used for the subsequent root bijection.
Centrality forces the ambient root to vanish on `c`. The actual reflection
transport in `DerivedCorootReflection` then realizes the reflection with the
transported source coroot by an ambient normalizer point. Worker 1577's generic
normalizer-reflection uniqueness theorem identifies that cocharacter with the
ambient coroot.

The actual root comparison in `DerivedRelativeRoots` proves that literal
character restriction is a bijection on the two root ranges. Combining it with
the coroot law and the actual composition pairing gives
`IsRootDatumOf.derivedRootDatumHom : RootPairing.Hom P Q`. Its weight map is
`α ↦ e ≫ α`, its contravariant coweight map is `ν ↦ ν ≫ e`, and its index map
is a bijection of the actual root indices.

`IsRootDatumOf.map_corootSpan_derived` shows that the image of the full integral
source coroot span is exactly the full integral ambient coroot span. It applies
the coroot law of the constructed morphism and its bijection of root indices,
then uses that linear maps carry spans to spans of images. This is an equality
over `ℤ`, without passing to rational or real spans.

The provenance is internal: the construction assembles existing actual-root,
normalizer-reflection, perfect-pairing and lattice-map interfaces. The root data,
finite full Weyl image, and central complement remain explicit supplied inputs.
This module does not assert root-datum existence, reductivity of centralizers, or
the full split-torus-centralizer comparison without those inputs.
