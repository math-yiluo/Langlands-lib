# Local comparison for finite tensor realizations

This module composes the published local tensor separation with an actual
form-valued intertwiner. It constructs a local equivalence onto the realized
image when that intertwiner is injective, while retaining the complementary
tensor space. All names below are in
`Langlands.Automorphic.FiniteTensorRealization` unless qualified.

## Parameters and supplied realization

The number field `F : Type uF` and the family of complex local vector spaces
`V : FinitePlace F → Type uV` have independent universes. The rank `n : ℕ` is
unrestricted. Each `ρ v` is a representation of the actual completed-local
group `FiniteLocalGL F n v` on `V v`. There are no finite-dimensionality or
topology assumptions on these vector spaces.

The finite exceptional set `E` and reference family `e` define the existing
algebraic restricted tensor space `Space ℂ V E e`. The hypothesis `he` says
that each reference vector outside `E` is fixed by the local integral subgroup;
`hne` says that these reference vectors are nonzero. There is no nonzero
condition at the exceptional places. The complementary space at `v` is exactly
`LocalTensorTail F E v e`, with exceptional set `tailSet {v} E`.

`Map F n ρ E e he` abbreviates the existing type of intertwiners from
`tensorRepresentation F n ρ E e he` to the actual finite adelic action on
`AutomorphicForms F n`. A map `T` is supplied; its existence is not assumed
universally or proved here. `IsInjective` abbreviates ordinary function
injectivity. These aliases introduce no new realization structure or axioms.

## Local map and actual image

`LocalMap` is the type of intertwiners from the separated representation
`ρ v ⊗ trivial(LocalTensorTail)` to `automorphicLocalRightAction F n v`.
Let `q = localTensorSeparation F n ρ E e he hne v`. The construction is

```text
localMap(T,v)(z) = T(q.symm(z)).
```

The proof first restricts `T` along the actual local inclusion. Its
intertwining equation is exactly the equation for `T` at that included group
element. It then composes this restricted map with the published inverse
representation equivalence `q.symm`.

`localMap_apply` proves the displayed formula. `localMap_separate` proves
`localMap(T,v)(q(x)) = T(x)`, using the inverse identity of `q`.
`mem_image_iff` identifies the image with the original actual subspace
`finiteRealizationImage F n T`; it holds even when `T` is not injective.
`image_le_iff` consequently identifies containment of this image in any
`S : FiniteRealization F n` with membership of every separated image vector in
`S`. In particular, one can take `S` to be the published prescribed-character
subspace, or the cusp subspace under its existing compactness hypothesis.
These are statements about the embedded form subspace, with no assertion that
such conditions descend to finite representation isomorphism classes.

`localMap_injective_iff` proves that the separated map is injective exactly
when `T` is injective. One direction composes injective maps; the other applies
the injectivity of `q` and uses `localMap_separate`.

## Equivalence onto the local restriction

For injective `T`, `LocalImageEquivalence` names the type

```text
(ρ v ⊗ trivial(LocalTensorTail)) ≃
  (finiteRealizationImage F n T).localRepresentation v.
```

`localImageEquiv` constructs this genuine representation equivalence. It
composes `q.symm` with the local restriction of the published
`finiteRealizationImageEquiv F n T hT`. The underlying linear equivalence is
therefore reassembly followed by the equivalence of an injective map with its
actual range. No inverse or image-equivalence hypothesis is added.
`inclusion_localImageEquiv` proves that inclusion into forms recovers
`localMap` pointwise.

`separated_isSmooth` transfers the already proved smoothness of the actual
local form action along the injective `localMap`. It needs `hne` and
injectivity of `T`, but does not assume smoothness of the supplied local
representations. The smoothness conclusion concerns the separated tensor
representation, including its complementary space.

`evaluate_localMap_tmul` gives the actual function identity

```text
localMap(T,v)(ρ(v)(g)x ⊗ y)(a)
  = localMap(T,v)(x ⊗ y)(a * ofFinite(localInclusion(v,g))).
```

Evaluation here includes the published `automorphicToContinuous` map. The
identity follows from the intertwining equation and the positive right
translation formula on forms. The complementary vector `y` is unchanged.

## Slices with a chosen complementary vector

For any complementary tensor `y`, `localSlice T v y` is the form-valued local
intertwiner `x ↦ localMap T v (x ⊗ y)`. It composes `localMap` with the
Mathlib tensor-product bilinear map, fixing its second coordinate.
Equivariance follows because the local group acts trivially on that coordinate.
`localSlice_apply` gives the exact formula.

If `T` is injective and `y ≠ 0`, `localSlice_injective` proves that this slice
is injective. After injectivity of `localMap` reduces the problem to equality
of elementary tensors, `Module.Projective.exists_dual_eq_one` supplies a
linear functional `φ` on the complementary vector space with `φ(y) = 1`.
Applying `TensorProduct.map id φ` and the right-unit equivalence recovers the
original local vector. This uses the existing projectivity of vector spaces
over a field and requires no finite dimension. `localFactor_isSmooth` then
transfers local smoothness from forms along this injective slice.

A nonzero complementary vector is an explicit hypothesis in these last two
results. The module neither chooses one canonically nor asserts that every
complementary space is nonzero. A slice is a copy of the factor inside the
local form space; the equivalence onto the whole realized image still has
source `V v ⊗ LocalTensorTail`.

## Provenance and limits

This is internal construction infrastructure from the published
`FiniteRealization`, `LocalAction`, and `LocalTensorSeparation` modules, using
Mathlib's intertwiner composition, representation equivalences, tensor maps,
and dual functional existence. The proof routes above describe the implemented
Lean. No new claim from external literature is introduced.

The constructions apply to a specified tensor representation and a supplied
map into actual forms. They do not construct automorphic tensor factorization,
prove occurrence of arbitrary local data, establish admissibility or
irreducibility, select unique local components, or construct the full
archimedean automorphic category. The complementary tensor multiplicity space
is retained throughout the image equivalence.
