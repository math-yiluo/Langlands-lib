# Arbitrary base change of integer torsion

For any scheme map `b : S' ⟶ S`, commutative group scheme
`G : Grp (Over S)`, and integer `n`, `torsionBaseChangeIso b G n` is
the canonical group-object isomorphism

```text
b*(G[n]) ≅ (b*G)[n].
```

The construction uses the published `kernelBaseChangeIso` for
`multiplication G n`, followed by equality transport along the published
`multiplication_baseChange` identity. The private `kernelCongr` implements
that transport; its inclusion equation follows by equality elimination.
These constructions impose no separatedness, flatness, finiteness,
nonzero, positivity, or invertibility hypothesis.

`torsionBaseChangeIso_hom_ι` says that composing the forward comparison
with the new torsion inclusion is the pullback of the old inclusion.
Its proof combines the kernel comparison equation with the equality
transport equation. The inverse equation follows by cancellation with
the isomorphism. `torsionBaseChangeIso_hom_unique` proves that the
forward equation uniquely determines the comparison morphism, using
the monomorphic underlying inclusion and group-homomorphism extensionality.

For every `T : Over S'`, `baseChangeTorsionPointsEquiv b G n T`
identifies the actual torsion subgroup of the points of `b*G` over `T`
with the actual torsion subgroup of the points of `G` over the composite
`T → S' → S`. Its forward and inverse maps restrict the multiplicative
pullback-adjunction equivalence `baseChangePointsEquiv`. They preserve
membership because a multiplicative equivalence preserves integer powers
and one, and torsion membership is exactly `x ^ n = 1`. The inverse and
multiplication laws follow from those of that equivalence.

`baseChangeTorsionPointsEquiv_val` exposes the underlying point map.
`baseChangeTorsionPointsEquiv_naturality` proves compatibility with
every map of test schemes by the naturality of the unrestricted point
equivalence. `torsionBaseChangeIso_points` states that the scheme
comparison and this subgroup comparison agree under
`torsionPointsEquiv`: either route gives the same torsion point over
`T → S`. Its proof reduces to the inclusion equation by subtype
extensionality and compatibility of `baseChangePointsEquiv` with
postcomposition.

This module is an internal consequence of the published `KernelBaseChange`,
`Multiplication`, and `Torsion` constructions. It introduces no additional
literature claim. The provenance of the underlying kernel, integer
multiplication, and arbitrary-base group-scheme constructions is documented
in their paired Markdown. No finite or etale property is asserted here;
those are separate geometric theorem obligations.
