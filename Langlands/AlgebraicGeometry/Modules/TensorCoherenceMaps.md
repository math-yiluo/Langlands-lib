# Tensor coherence comparison maps

This module constructs the maps needed to relate the explicit sheafified
tensor in `Tensor` to the published symmetric monoidal structure in
`TensorMonoidal`. It works on actual scheme-module sheaves in an arbitrary
universe, without geometric or coherence hypotheses.

## Explicit associator

For `M,N,P : X.Modules`, `tensorAssociator M N P` is an isomorphism
from `tensorObj (tensorObj M N) P` to `tensorObj M (tensorObj N P)`.
Let `c(M,N)` denote `localizedTensorIso X M N`, whose direction is
from the localized tensor `M ⊗ N` to the explicit `tensorObj M N`.
The associator is the following composite of five isomorphisms:

1. Apply the inverse of `c(tensorObj M N,P)`.
2. Tensor the inverse of `c(M,N)` with the identity of `P`.
3. Apply the associator of the published monoidal structure on `X.Modules`.
4. Tensor the identity of `M` with `c(N,P)`.
5. Apply `c(M,tensorObj N P)`.

This fixes a specific associator on the existing explicit tensor objects.
Its inverse is supplied by the composition of isomorphisms. This unit
does not separately prove its pentagon or its compatibility with the
previously defined explicit unitors and swap.

## Localized pullback comparisons

For every scheme morphism `f : X ⟶ Y`, write `F` for the existing
`Scheme.Modules.pullback f`. The natural transformation
`localizedPullbackTensorComparison f` has source
`tensor Y.Modules ⋙ F` and target `(F.prod F) ⋙ tensor X.Modules`.
It is obtained by whiskering the published natural comparison
`localizedTensorNatIso` and composing with the fixed canonical
`pullbackTensorComparison`.

Its component `localizedPullbackTensorComparisonApp f M N` is the map
from `F(M ⊗ N)` to `FM ⊗ FN` given by

`F(c_Y(M,N).hom) ≫ pullbackTensorComparisonApp f M N ≫ c_X(FM,FN).inv`.

The lemma `localizedPullbackTensorComparisonApp_eq` proves this formula
by definitional equality. Naturality is part of the constructed natural
transformation, inherited by whiskering and composing natural maps.
No invertibility of the canonical tensor comparison is assumed or proved.

The unit comparison uses the published `pullbackUnitIso f` directly,
viewed as an isomorphism `F(𝟙_ Y.Modules) ≅ 𝟙_ X.Modules`.
This works because the localized monoidal unit is definitionally the
structure sheaf.

## Provenance and scope

Worker 59 authored these internal categorical constructions. They use the
published `Tensor`, `TensorMonoidal`, `PullbackTensor`, and `PullbackUnit`
interfaces, together with Mathlib's composition and tensor product of
isomorphisms and whiskering of natural transformations. The underlying
sheaf-theoretic provenance is recorded in those imported modules.
This module claims no new translation of a literature theorem.

The parent task retains the explicit-unitors/swap comparison, associativity
and other coherence laws for these fixed maps, canonical tensor-comparison
invertibility, and strong symmetric monoidal pullback with the existing
identity and composition comparisons. No monoidal pullback instance is
introduced by this definition unit.
