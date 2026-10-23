# Tensor products of rigidified line bundles

For an arbitrary scheme morphism `ε : S ⟶ X`, this module constructs the
tensor bifunctor on `RigidifiedLineBundle ε`. These are actual locally
free rank-one module sheaves on `X` with an isomorphism from `O_S` to
their pullback along `ε`.

The explicit premise
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement`
asserts invertibility of the fixed canonical pullback tensor comparison
for every scheme morphism in the given universe. The construction uses
that premise both for the rigidification and for local rank-one closure.
Its proof remains a separate obligation.

## Construction and implemented proofs

`tensor preservation L M` uses `RigidifiedModule.tensorObj` for its
underlying rigidified module and `IsLocallyFreeRankOne.tensor` for the
rank-one property. Thus its carrier is the sheafification of the sectionwise
tensor, and its rigidification is the composite

```
O_S → O_S ⊗ O_S → ε*L ⊗ ε*M → ε*(L ⊗ M).
```

These arrows are respectively the inverse explicit left unitor, the
tensor of the two rigidifications, and the inverse canonical pullback
tensor comparison. Rank-one closure was proved in `LineBundleTensor`
by intersecting trivializing neighborhoods.

`tensorFunctor` lifts the rigidified-module tensor bifunctor to the full
subcategory of rank-one objects. Its morphisms are the actual tensor maps
with the compatibility equations already proved in `RigidificationTensor`;
the full-subcategory lift supplies the functor laws. `tensorFunctor_obj`
identifies its object part with `tensor` by reflexivity.

`tensorForgetToRigidifiedIso` identifies forgetting rank one with applying
the rigidified-module tensor after forgetting rank one in both inputs.
It is an identity natural isomorphism. `tensorForgetIso` identifies
forgetting rigidification with applying the ordinary line-bundle tensor;
it has identity components and naturality follows from the identical
underlying tensor maps.

`tensorIso` applies the bifunctor to a pair of compatible isomorphisms.
For a morphism `f : X ⟶ S` and section `ε` with `ε ≫ f = 𝟙 S`,
`classesTensor` descends the tensor to the existing relative isomorphism
classes `Classes f ε section_eq T`. The quotient construction is
well-defined because `tensorIso` maps isomorphic representatives to
isomorphic tensor bundles. `classesTensor_classOf` identifies the result
on representatives by reflexivity. No pullback coherence premise is
needed for this operation at an individual test scheme.

## Provenance and scope

Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft,
Chapter VI, paragraph (6.2), printed p.88 (PDF p.92), gives the tensor
rigidification and tensor operation on isomorphism classes. The registered
source is `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
This module derives the full-subcategory lift and quotient operation
from that formula and the previously constructed tensor and local
rank-one interfaces. The formula itself does not require the extra
hypotheses in EGM's condition (*).

This supplies a bifunctor and a binary operation on relative rigidified
classes. Associativity, commutativity, unit and inverse laws, compatibility
with relative pullback, and the resulting abelian-group-valued presheaf
remain separate steps.
