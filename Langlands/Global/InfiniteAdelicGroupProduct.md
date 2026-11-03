# Actual archimedean point groups as products over infinite places

For a field `F` (in particular any number field) and an affine group scheme `G` over `F`,
`InfinitePlaceGroupPoints F G v` is the actual point group of `G` over the
actual completion `v.Completion` at an infinite place. Its topology is the
existing global regular-function evaluation topology.

`InfiniteAdelicGroupPoints.completions` identifies the existing infinite
adelic point group with the product of these local point groups as a
multiplicative homeomorphism. It specializes
`GroupScheme.affinePointsPiHomeomorph` to the dependent family
`v ↦ v.Completion`. Mathlib's actual `InfiniteAdeleRing F` is this dependent
product, with its componentwise algebra and product topology.
`atPlace` and `assemble` give continuous projection homomorphisms and the
inverse assembly map. Their inverse laws, the assembly multiplication law,
and both regular-function evaluation identities are proved for the existing
point carriers and operations.

For the actual general linear group scheme, `infinitePlaceHomeomorph` gives
the existing invertible-matrix group over each completion, preserving its
topology. `infinitePlaceHomeomorph_atPlace` proves that the completion
projection agrees with applying the coefficient evaluation ring homomorphism
to the original infinite adelic matrix group. It follows directly from the
published naturality theorem for actual general-linear points.

This is an internal derived specialization of the universal property of
dependent products and the existing actual general-linear comparison.
It does not use a norm on the infinite adele ring, or require smoothness,
reductivity or finite type of `G`. It supplies no manifold, Lie group,
differential, measure or reduction theorem.
