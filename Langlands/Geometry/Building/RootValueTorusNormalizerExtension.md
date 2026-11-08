# Extending shifts through the actual lower centralizer

This internal construction combines full-centralizer scalar covariance with
centralizer correction of nested-torus normalizers. It chooses a shift vector
for every actual lower normalizer and derives the exact lower V2 reflection
conclusion. The structural centralizer and covariance premises, and compatible
shifts for common normalizers, remain explicit hypotheses.

Work over an arbitrary field `k : Type u`, using the existing rational points,
normalizer and centralizer subgroups, character evaluations, and real
cocharacter spaces. All point equalities and conjugations are in the original
ambient group `rationalPoints G`.

## From centralizer covariance to a total-family translation

Let `i : S.toGrp ⟶ G` be monomorphic, with `S` commutative and `G` affine.
For `ψ : RootFunctionFamily S G`, assume these two normalization laws:

- if `α ∉ relativeRoots i`, then `ψ α g = ⊤` for every `g`;
- if `α ∈ relativeRoots i` and `g ∉ rootGroupPoints i α`, then `ψ α g = ⊤`.

Supply `z : centralizerPoints i` and `w : V S`. Assume, for every actual root
`α` and every `g` of its original root group,

```text
ψ α (z⁻¹ * g * z) = ψ α g + coe (eval S α w).
```

`RootFunctionFamily.centralizer_smul_eq_vadd` proves equality of entire
families:

```text
inclusion(z) • ψ = w +ᵥ ψ.
```

The inclusion is the existing inclusion of the full centralizer points into
normalizer points. Its inverse Weyl action is trivial. On an actual root group,
the desired equality is the supplied covariance law. Outside that root group,
normalizer conjugation preserves nonmembership and both values are top.
For a nonroot, the first normalization law gives top on both sides. Addition
of a finite real number preserves top.

No lower root-datum valuation is assumed in this lemma. In particular, it does
not derive covariance from V2.

## Composing an exact centralizer factorization

`RootFunctionFamily.normalizer_shift_of_centralizer_factor` applies to any
family for a monomorphic commutative map `i`, without an affineness premise.
Let `n,m : normalizerPoints i`, `z : centralizerPoints i`, and suppose

```text
(n : G(k)) = (z : G(k)) * (m : G(k)),
inclusion(z) • ψ = w +ᵥ ψ,
m • ψ = v +ᵥ ψ.
```

It proves

```text
n • ψ = (v + w) +ᵥ ψ.
```

The exact ambient factorization is an equality of normalizer points by subtype
extensionality. The centralizer factor acts trivially on `V S`. Associativity
of the normalizer action and its compatibility with translation therefore
compose the two shifts in the displayed order. No uniqueness or additivity
of chosen shifts is asserted.

## The chosen shift for every lower normalizer

Now let `i : T.toGrp ⟶ G` and `f : S ⟶ T`, and write
`a = CommGroupScheme.groupHom f ≫ i`. Assume the upper and lower maps are
monomorphic, `G` is affine and smooth, `S` and `T` are split tori, and `i`
has `RelativeRoot.HasOppositeFactorPairs`. Supply an upper valuation
`hφ : IsRootDatumValuation i φ`, and write

```text
ψ = torusRestrictedRootFunctionFamily hS hT hE hφ f.
```

Retain the following additional premises:

- `hi : IsMaximalSplitTorus i`;
- `j : H ⟶ G` represents the actual full subgroup functor
  `torusCentralizer a` and is a closed subgroup;
- `MaximalSplitToriAreConjugate H`;
- a function `ν : centralizerPoints a → V S`, with the covariance law
  `ψ α (z⁻¹ * g * z) = ψ α g + coe (eval S α (ν z))` for every
  `z`, every actual lower root `α`, and every `g ∈ rootGroupPoints a α`;
- for every `nT : normalizerPoints i` whose ambient point also normalizes
  `a`, there exists `v : V S` with
  `nT • φ = cocharacterMapReal f v +ᵥ φ`.

The covariance hypothesis is about every point of the full lower centralizer.
The function `ν` is supplied as a function; no homomorphism property is needed
or concluded. The common-normalizer shift premise requires a vector in the
image of the original lower cocharacter map.

`exists_torusRestrictedNormalizerShift` proves that for every original
`nS : normalizerPoints a` there exists `vS : V S` with

```text
nS • ψ = vS +ᵥ ψ.
```

The previously constructed `exists_centralizer_mul_commonNormalizer` supplies
`nS = z * nT`, where `z` lies in the full lower centralizer and `nT` normalizes
both maps. Choose the compatible upper shift `v` of `nT`. The common-normalizer
transfer theorem gives its lower shift by `v`. The two existing normalization
laws for the canonical restricted family allow the first lemma above to give
the shift of `z` by `ν z`. The composition lemma gives the witness
`vS = v + ν z`.

The primary definition `torusRestrictedNormalizerShift` chooses such a vector.
Its dependent pair retains the total-family equality for the supplied arbitrary
lower normalizer. The original `nS` is not required to preserve the upper torus.
The choice is not claimed canonical, unique, or multiplicative.

## Exact conditional V2 and retained obligations

`torusRestrictedRootFunctionFamily_reflection_of_centralizer_correction`
has precisely the conclusion of the existing lower
`IsRootDatumValuation.reflection` field: for each actual lower root `α` and
each original lower normalizer `nS` satisfying `RealizesReflection a α nS`,
there is `c : ℝ` such that, for every nonidentity `g` in the original lower
root group,

```text
ψ α g = ψ (-α) (nS * g * nS⁻¹) + coe c.
```

The proof chooses the total-family shift `vS` above, takes
`c = -eval S α vS`, and applies the generic reflection formula from
`RootValueTorusReflection`. It uses the Weyl-negation component of
`RealizesReflection` and specializes the resulting all-point equality.

This is an internal derivation from the existing family actions and the
`RootValueTorusReflection` and `NestedTorusNormalizerFactorization` interfaces.
It asserts no new original-literature result. It establishes neither the
centralizer representation and conjugacy hypotheses nor full-centralizer
covariance or compatible common-normalizer shifts for a new class of groups.
It assumes no lower root-datum valuation.

Unconditional lower V2, opposite V5, adapted upper valuation existence, the
initial apartment and metric building, and the special-vertex stabilizer and
unique-fixation assertions for the originally supplied integral model remain
unproved. The unchanged `IntegralModel.BuildingComparisonStatement` remains
the host task's open goal.
