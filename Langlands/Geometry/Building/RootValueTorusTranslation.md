# Translations of actual torus-restricted root functions

This internal prerequisite concerns the actual canonical filtration and scalar
family constructed in `RootDepthTorusRestriction` and `RootValueTorusRestriction`.
The field has arbitrary universe `u`. Let `f : S ⟶ T` be a morphism of actual
commutative group schemes and `i : T.toGrp ⟶ G` a monomorphic map into an affine
group scheme. An existing upper root-datum valuation `hφ` remains a premise.
No monomorphism of `f` is required.

For a real lower cocharacter vector `v`, its actual upper image is
`cocharacterMapReal f v`. Write `H(φ,f,α,r)` for
`torusRestrictedRootDepthSubgroup hφ f α r`. The theorem
`torusRestrictedRootDepthSubgroup_vadd` proves

```
H(cocharacterMapReal f v +ᵥ φ, f, α, r)
  = H(φ, f, α, r - eval S α v).
```

This holds for every lower character `α`, every real depth `r`, and every
vector `v`. It requires no splitness or smoothness premise beyond those
already stated for this subgroup identity. These are equal subgroups of
the original `rationalPoints G`.

`torusRestrictedRootDepthTranslationPointsEquiv` is the multiplicative
equivalence induced by this equality. Its `_val` theorem states that it
preserves the underlying ambient rational point exactly.

With both tori split, `G` smooth, and the existing upper opposite-factor-pair
predicate, the scalar family is available. The theorem
`torusRestrictedRootFunctionFamily_vadd` proves the equality of families

```
torusRestrictedRootFunctionFamily hS hT hE
    (hφ.vadd (cocharacterMapReal f v)) f
  = v +ᵥ torusRestrictedRootFunctionFamily hS hT hE hφ f.
```

The equality holds on every character and every ambient rational point.
There is no root-occurrence premise or sign restriction on the depth.

## Implemented proof

The canonical subgroup is the supremum of the original upper filtration
subgroups at depths `m*r`, for actual upper roots `χ` whose restrictions
satisfy `f ≫ χ = m • α`, with positive natural `m`. Character/cocharacter
adjunction gives
`eval T χ (cocharacterMapReal f v) = eval S (f ≫ χ) v`.
The published character-scaling lemma then gives `m * eval S α v`.
For a value `q : WithTop ℝ`, the inequality
`r ≤ q + c` is equivalent to `r-c ≤ q`; the private helper proves this by
separating `⊤` from a finite real value. Real distributivity changes each
upper depth to `m*(r-eval S α v)`. Thus every generator is the corresponding
generator for the shifted lower depth, and the suprema are equal. The point
equivalence is `MulEquiv.subgroupCongr`, using its reflexive value law.

For an actual lower root and a point in its root group, the exact finite
level-set theorem identifies each scalar lower bound with membership in
the canonical subgroup. The subgroup translation identity therefore gives
all real lower bounds of the translated scalar value. Real lower-bound
extensionality in `WithTop ℝ` proves equality, including the identity point.
For a point outside the root group, or a character outside the actual root
set, both normalized scalar values are `⊤`; addition of the finite character
evaluation preserves `⊤`.

## Provenance and remaining obligations

This is an internal derivation from the imported actual filtration,
scalar-level-set, valuation-translation and character-pairing interfaces.
It makes no new original-literature assertion. The upper valuation and
the scalar construction's geometric and opposite-pair premises remain
explicit.

The result does not prove the reflection or opposite axioms for the lower
family, or construct an initial compatible valuation or apartment.
Common-normalizer compatibility, the metric building, and the supplied-model
stabilizer and unique-fixation comparison remain separate obligations.
In particular, the full `BuildingComparisonStatement` remains unproved.
