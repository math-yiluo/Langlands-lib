# Actual local realizations and tensor-slice images

This module constructs locally invariant subspaces inside the published
automorphic form space and applies them to the published tensor slices. It
constructs equivalences between the images of slices at nonzero complementary
vectors, proves equality of their smooth representation classes, and transports
the supplied integral reference vector to an actual nonzero fixed form.

## Actual local subspaces

The number field `F : Type uF` is arbitrary, the rank `n : ℕ` includes zero, and
coefficients are complex. For an actual finite place `v`, the group is
`FiniteLocalGL F n v`, with its existing completion topology. A model vector
space can live in an independent universe `uV`; it needs an additive commutative
group and complex module structure, with no finite-dimensionality or carrier
topology assumption.

In `Langlands.Automorphic`, `LocalRealization F n v` abbreviates
`Subrepresentation (automorphicLocalRightAction F n v)`. Thus its elements are
subspaces of actual automorphic forms stable under the indicated completed-local
group. They are not required to be stable under the entire finite adelic group.
The namespace `LocalRealization` supplies:

- `Space`, the actual subspace carrier, and `Action`, its representation type;
- `representation`, the restricted local action, and `inclusion`, its
  form-valued intertwiner;
- `inclusion_injective` and `isSmooth`, the latter obtained by injective
  transfer from the published smooth local form action;
- `smoothRepresentation`, an object of the existing `SmoothRep` category;
- `isoClass`, its quotient class at carrier universe `uF`;
- `isoClass_eq_iff`, identifying class equality with existence of an
  equivariant linear equivalence between the actual subspace actions;
- `toContinuous`, the faithful continuous adelic function map, its injectivity,
  and `evaluate_representation`, the evaluation identity below.

For `f` in the subspace, this identity is

```text
(g · f)(a) = f(a * ofFinite(localInclusion(v,g))).
```

All evaluations pass through `automorphicToContinuous`. The formula uses
positive right translation, and follows definitionally from the published
action. Inclusion and function-map injectivity follow from subtype injectivity
and the existing faithful map on forms. The smoothness proof uses
`Langlands.isSmooth_of_injective`. Class equality is the existing quotient
criterion together with `SmoothRep.mkIso` and `SmoothRep.equivOfIso`. An
equivalence does not imply equality of embedded subspaces.

`FiniteRealization.toLocal` restricts a finite adelic invariant subspace to the
local group without changing its underlying submodule. Stability follows by
applying the finite stability condition to `localInclusion`. `mem_toLocal`
is the identical membership criterion. `toLocal_representation` identifies
this action with the previously published `FiniteRealization.localRepresentation`.
In particular, local restriction retains the entire finite realization carrier.

## Character and cusp conditions on embedded forms

`LocalRealization.HasCentralCharacter χ` means containment in the local
restriction of `centralCharacterAutomorphicSubrepresentation F n χ`.
Here `χ` is the same continuous complex unit-valued character of the actual
idele-class group used by the published form definitions.
`centralCharacter_evaluate` recovers its scalar transformation law:

```text
f(scalar(z) * a) = centralIdeleCharacter(F,χ)(z) * f(a).
```

Under the explicit existing hypothesis `CompactSpace (AdeleQuotient F)`,
`LocalRealization.IsCuspidal` means containment in the local restriction of
the actual cusp subspace. `constantTerm_eq_zero` recovers vanishing for every
split `a + b = n` with both `a` and `b` positive, at every adelic group element.
Both proofs apply the containment hypothesis to the form's membership proof.

These conditions concern the embedded adelic functions. The module does not
assert that they descend to local representation classes. An equivalence for
one completed-local group alone does not encode the full global character or
all adelic constant terms.

## Images of actual local maps

`LocalRealizationMap F n ρ` is the type of intertwiners from a specified local
representation `ρ` to the actual local action on forms.
`LocalRealizationMap.IsInjective` is ordinary function injectivity.
`LocalRealization.Equivalence` names the type of representation equivalences
from a model to a specified local realization.

`localRealizationImage` takes the actual invariant range of the intertwiner.
Under injectivity, `localRealizationImageEquiv` constructs a genuine
representation equivalence from the model to this range: its linear
equivalence is Mathlib's `LinearEquiv.ofInjective`, and equivariance is the
original intertwining law, checked after subtype inclusion.
`inclusion_localRealizationImageEquiv` proves that the resulting range vector
has exactly the original form-valued image. These constructions do not assert
the existence of such a map for an arbitrary local model.

## Tensor-slice images

The remaining names are in `Langlands.Automorphic.FiniteTensorRealization`.
They use the published tensor data `ρ`, finite exceptional set `E`, and
reference family `e`. The hypothesis `he` imposes integral fixedness outside
`E`, and `hne` imposes nonzeroness outside `E`. There is no nonzero condition
on the reference family at exceptional places. `T` is a supplied map from
the actual finite adelic tensor representation into forms.

At a place `v`, let `Y = LocalTensorTail F E v e`, let
`q = localTensorSeparation F n ρ E e he hne v`, and let `y : Y`.
The existing local slice sends

```text
x ↦ T(q.symm(x ⊗ y)).
```

`sliceRealization T v y` is its actual local invariant range.
`sliceRealization_le` places this range in the local restriction of
`finiteRealizationImage F n T`. Its proof uses the published `mem_image_iff`
on the elementary tensor `x ⊗ y`. It does not require injectivity of `T` or
nonzeroness of `y`. The lemmas `sliceRealization_hasCentralCharacter` and
`sliceRealization_isCuspidal` compose this containment with the corresponding
condition on the full finite image. Their conclusions consequently apply to
the actual slice forms, including their scalar law and vanishing constant
terms.

`TailNonzero F E e v y` abbreviates exactly `y ≠ 0`. It keeps the large
complementary-space zero instance out of displayed declaration types; it adds
no mathematical condition.

For injective `T` and nonzero `y`, `sliceEquiv` constructs an equivalence

```text
ρ(v) ≃ (sliceRealization T v y).representation.
```

It applies `localRealizationImageEquiv` to the previously proved injective
`localSlice`. `inclusion_sliceEquiv` identifies the resulting actual form
with `localSlice T v y x`.

For two supplied injective realizations `T`, `T'` of the same specified
tensor data, and two nonzero complementary vectors `y`, `y'`,
`SliceChangeEquivalence` names the equivalence type between their slice
images. `sliceChangeEquiv` constructs it by composing
`(sliceEquiv T y).symm` with `sliceEquiv T' y'`.
`sliceChangeEquiv_apply` proves that it sends the image of `x` in the first
slice to the image of the same `x` in the second. The proof cancels the
intermediate inverse equivalence. `slice_isoClass_eq` then applies
`LocalRealization.isoClass_eq_iff`. Both subspace carriers live in `uF`,
even when the specified model has carrier universe `uV`, so this compares
classes in the same existing quotient without resizing the model.

This independence result varies the form-valued embedding and complementary
vector for fixed tensor data. It is not uniqueness of factors across different
tensor decompositions. It does not equate the embedded subspaces.

## Nonzero integral-fixed forms and remaining scope

If additionally `v ∉ E`, `slice_exists_integral_fixed` constructs a nonzero
vector in the actual slice image fixed by every element of
`localIntegral F n v`. Take `sliceEquiv T y (e v)`. Its nonzeroness follows
from injectivity of the equivalence and `hne v hv`. Its fixedness follows by
applying the equivariance identity to `e v` and substituting `he v hv g hg`.
The theorem includes all three necessary hypotheses: injectivity of `T`,
nonzeroness of the complementary vector, and membership outside `E`.
It does not assert that the fixed space is one-dimensional or that the local
action is irreducible or admissible.

The provenance is internal: this module specializes Mathlib subrepresentations,
invariant ranges and image equivalences to the published actual local form
action, then composes them with the published tensor slices. Its proofs are
the constructions described above. It introduces no new external literature
claim, existence assumption, or substitute form carrier.

No nonzero form or complementary vector is asserted to exist independently
of the stated data. No arbitrary automorphic representation is factored.
The equivalence onto the whole finite image remains the published
`localImageEquiv`, whose source is `V v ⊗ LocalTensorTail`; its complementary
multiplicity is unchanged. Local-component uniqueness across factorizations,
irreducibility, admissibility, Satake identification, and the full archimedean
automorphic category remain separate obligations.
