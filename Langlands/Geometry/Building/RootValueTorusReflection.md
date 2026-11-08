# Reflection transport for actual torus-restricted root functions

This internal construction applies the common-normalizer and translation
identities to a supplied reflecting representative. It gives an exact conjugation
equivalence of the canonical restricted filtration subgroups and the scalar
reflection formula. The existence of the common representative and the compatible
upper shift remains a hypothesis.

Work over an arbitrary field `k : Type u`, with commutative group schemes `S`
and `T`, an ambient group scheme `G`, and a monomorphic map `i : T.toGrp ⟶ G`.
The character and real cocharacter spaces, normalizer points, Weyl actions and
rational points are the existing Library objects.

## A reflection formula for any root-function family

`RootFunctionFamily.reflection_eq_of_normalizer_shift` applies to any family
`φ : RootFunctionFamily T G`, character `a`, actual normalizer point `n`, and
vector `v : V T`. Its hypotheses are

```text
weylAction i n a = -a,
n • φ = v +ᵥ φ.
```

For every ambient rational point `g` it proves

```text
φ a g = φ (-a) (n * g * n⁻¹) + coe (-eval T a v).
```

The values lie in `WithTop ℝ`. There is no root-occurrence, nonidentity,
valuation, affineness, smoothness or splitness hypothesis in this lemma.

The proof evaluates the supplied family equality at the character `-a` and
the conjugated point. The inverse Weyl action sends `-a` to `a`, inverse
conjugation returns `g`, and character evaluation at `-a` gives the displayed
negative constant.

## Exact subgroups and conjugation on their points

Now assume that `G` is affine, fix `f : S ⟶ T`, and assume that the composite
`CommGroupScheme.groupHom f ≫ i` is monomorphic. Supply an upper valuation
`hφ : IsRootDatumValuation i φ` and actual normalizer points

```text
nS : normalizerPoints (CommGroupScheme.groupHom f ≫ i),
nT : normalizerPoints i
```

whose underlying ambient rational points are equal. For a lower character `α`
and vector `v : V S`, assume

```text
weylAction (CommGroupScheme.groupHom f ≫ i) nS α = -α,
nT • φ = cocharacterMapReal f v +ᵥ φ.
```

Write `H(α,r)` for the existing canonical subgroup
`torusRestrictedRootDepthSubgroup hφ f α r` in the original `rationalPoints G`.
For every real depth `r`,
`torusRestrictedRootDepthSubgroup_reflection_shift` proves

```text
H(-α, r + eval S α v) = map (conj nT) (H(α,r)).
```

There is no root-occurrence or depth-sign hypothesis. No splitness, smoothness
or opposite-factor-pair hypothesis is needed for this subgroup identity.

`torusRestrictedRootReflectionPointsEquiv` is the multiplicative equivalence
from the actual subgroup `H(α,r)` to the actual subgroup
`H(-α,r + eval S α v)`. Its `_val` theorem identifies the underlying ambient
point of the image of `g` as exactly `nT * g.val * nT⁻¹`. Thus the equivalence
uses the original conjugation map and the original filtered subgroups.

The proof first applies the previously constructed cocharacter translation
identity at `-α`. Substituting the supplied equality of upper families and the
lower Weyl-negation equation then reduces the result to the common-normalizer
subgroup identity. The point equivalence composes the subgroup map of the
conjugation automorphism with the proved equality of subgroups.

## Scalar reflection and its conditional V2 consequence

For the scalar construction, additionally assume that `G` is smooth, both
`S` and `T` are split tori, and `i` has the existing upper
`RelativeRoot.HasOppositeFactorPairs` property. Let `ψ` be the actual family
`torusRestrictedRootFunctionFamily hS hT hE hφ f`.
`torusRestrictedRootFunctionFamily_reflection_shift` proves, for every lower
character and every ambient rational point,

```text
ψ α g = ψ (-α) (nS * g * nS⁻¹) + coe (-eval S α v).
```

It uses the common-normalizer shift-transfer theorem to obtain
`nS • ψ = v +ᵥ ψ`, then applies the generic reflection formula above.

`torusRestrictedRootFunctionFamily_reflection_of_common_lifts` gives exactly
the existing V2 conclusion for `ψ` under the following structural premise:
for every actual lower relative root `α` and every lower normalizer `nS`
satisfying the existing `RealizesReflection` predicate, there are an upper
normalizer `nT` with the same ambient point and a lower vector `v` satisfying
the displayed upper shift equation. For each such `nS`, the proof chooses
`c = -eval S α v` and specializes the preceding formula to the required
nonidentity points of the original lower root group. The shift may depend on
the root and representative.

This structural premise is retained explicitly. An arbitrary lower normalizer
need not preserve the chosen upper torus, and this file does not assert that
common representatives or compatible shifts exist.

## Provenance and remaining construction

These are derived identities of the existing normalizer actions, canonical
subgroups and scalar families, rather than a translation of a new claim from
the literature. The implemented proofs use
`RootValueTorusNormalizer`, its imported torus-translation identities, and the
original Weyl and character-evaluation definitions.

This file supplies no unconditional lower V2 or opposite law V5, initial
valuation, metric building, or supplied-model stabilizer and unique-fixation
comparison. The full `BuildingComparisonStatement` remains unproved.
