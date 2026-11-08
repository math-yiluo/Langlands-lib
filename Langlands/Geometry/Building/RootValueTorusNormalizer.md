# Common actual normalizers and torus-restricted root functions

This internal prerequisite concerns the actual subgroup and scalar constructions
of `RootDepthTorusRestriction` and `RootValueTorusRestriction`. The field has
arbitrary universe `u`. Let `f : S ⟶ T` be a morphism of actual commutative group
schemes and `i : T.toGrp ⟶ G` a monomorphic embedding. Write `j` for
`CommGroupScheme.groupHom f ≫ i`. The upper embedding has the instance
`Mono i.hom.hom.left`. The lower embedding has `Mono j.hom.hom.left` for the
character and restricted-filtration conclusions below.

The normalizers are the existing subgroups of the original `rationalPoints G`.
Supply `nS : normalizerPoints j` and `nT : normalizerPoints i` whose ambient
points are equal. This equality is an explicit premise. The result does not
assert that every lower normalizer preserves the upper torus.

## Transport and character compatibility

`RootFunctionFamily.transportEquiv_normalizer` identifies the original action
`n • φ` with transport by the actual torus automorphism `normalizingAut i n`
and ambient scheme automorphism `G.innerIso n`. With `G` affine and an existing
upper valuation `hφ : IsRootDatumValuation i φ`, the theorem
`IsRootDatumValuation.normalizer_smul` proves that `n • φ` is again an upper
root-datum valuation. No smoothness or splitness is required here.

For the common normalizers, `commonNormalizer_normalizingAut_comp` proves

```
(normalizingAut j nS).hom ≫ f = f ≫ (normalizingAut i nT).hom.
```

This square only needs the upper monomorphism. With the lower monomorphism,
`commonNormalizer_weylAction_comp` proves, for every upper character `χ`,

```
f ≫ weylAction i nT χ = weylAction j nS (f ≫ χ).
```

`commonNormalizer_restrict_eq_nsmul_iff` then preserves and reflects the
restriction equation `f ≫ χ = m • α` for every natural multiplier `m`,
including zero. These character results require no affineness premise.

## Canonical filtration and original points

Assume `G` affine and retain the existing upper valuation. Write
`H(φ,f,α,r)` for `torusRestrictedRootDepthSubgroup hφ f α r`, a literal
subgroup of `rationalPoints G`. For every lower character `α` and real depth
`r`, `torusRestrictedRootDepthSubgroup_normalizer_smul` proves

```
H(nT • φ, f, weylAction j nS α, r)
  = (H(φ,f,α,r)).map (MulAut.conj nT).toMonoidHom.
```

`mem_torusRestrictedRootDepthSubgroup_normalizer_smul_iff` expresses this as
membership equivalence under `g ↦ nT * g * nT⁻¹`.
`torusRestrictedRootDepthNormalizerPointsEquiv` is the induced multiplicative
equivalence between these exact subgroup subtypes. Its `_val` theorem proves
that its underlying point is precisely `nT * g.val * nT⁻¹`. These conclusions
have no root-occurrence premise, no depth sign restriction, and no splitness
or smoothness assumption.

## Whole scalar families and shifts

Additionally suppose both tori are split, `G` is smooth, and the existing
upper predicate `RelativeRoot.HasOppositeFactorPairs i` holds. These are the
original premises of the scalar construction. The theorem
`torusRestrictedRootFunctionFamily_normalizer_smul` proves

```
torusRestrictedRootFunctionFamily hS hT hE (hφ.normalizer_smul nT) f
  = nS • torusRestrictedRootFunctionFamily hS hT hE hφ f.
```

This is equality on every lower character and every ambient rational point,
including the normalized top-valued cases. For any lower real cocharacter
vector `v`, `torusRestrictedRootFunctionFamily_normalizer_shift` consequently
transfers the supplied upper shift equation

```
nT • φ = cocharacterMapReal f v +ᵥ φ
```

to the exact lower shift equation `nS • ψ = v +ᵥ ψ`, where `ψ` is the
constructed lower scalar family. The upper shift equation remains a premise.

## Implemented proof and provenance

The normalizer transport identity follows by comparing the inverse torus
character action and actual inverse inner-automorphism point map. The
existing isomorphism-transport theorem for valuations then supplies the
upper valuation action. For common normalizers, the two original normalizing
squares agree after composition with `i`. Monomorphy cancels `i`, producing
the torus square. Its inverse square gives Weyl covariance, and injectivity
of the lower Weyl action gives the restriction-multiplier equivalence.

For an upper root, intrinsic root-group conjugation and the family action
give equality of the actual upper filtration subgroups under conjugation.
The canonical restricted subgroup is a supremum indexed by upper roots,
positive natural multipliers, and restriction equations. Conjugation maps
suprema to suprema. Weyl bijectivity and the restriction-multiplier
equivalence reindex those generators in both directions. `subgroupMap`
followed by `subgroupCongr` gives the claimed point equivalence and its
literal conjugation value law.

For the scalar equality, reindex every character by the lower Weyl action
and every point by conjugation. Intrinsic root-group conjugation preserves
and reflects root membership. On actual root points, the exact finite
level-set theorem and subgroup membership equivalence compare every real
lower bound; extensionality in `WithTop ℝ` proves equality of the scalar
values. Off the root set or root group both normalized values are top.
The shift consequence uses equality substitution and proof irrelevance to
identify the restricted constructions for the equal upper families, then
applies the imported torus-translation theorem.

This is an internal derivation from the imported actual normalizer,
root-subgroup, isomorphism-transport, canonical filtration, scalar level-set
and translation interfaces. It asserts no new original-literature result.
Common upper representatives and compatible upper shifts are not constructed.
The lower reflection and opposite laws, initial compatible valuation and
apartment, metric building, supplied-model stabilizer and unique fixation
remain open. The full `BuildingComparisonStatement` remains unproved.
