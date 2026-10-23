# Tensor products of rigidified module sheaves

For any morphism of schemes `ε : S ⟶ X`, this module constructs a bifunctor
on the existing category `Langlands.SchemeModule.RigidifiedModule ε`.
Its underlying objects are actual sheaves of modules on `X`; a rigidification
is an isomorphism from the structure module of `S` to their pullback along `ε`.
No assumption that `ε` is a section is needed for this construction.

Every construction takes the explicit premise
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement`.
This published proposition says that the canonical tensor comparison for
pullback is invertible along every scheme morphism in the given universe.
Here it is used only at `ε`. Its proof is a separate obligation; this
module does not prove it or add it as an axiom.

## Construction

`RigidifiedModule.tensorObj preservation M N` has underlying module
`Langlands.Scheme.Modules.tensorObj M.carrier N.carrier`, the sheafification
of the sectionwise tensor product. Its rigidification is the composite

```
O_S → O_S ⊗ O_S → ε*M ⊗ ε*N → ε*(M ⊗ N).
```

The first arrow is the inverse of the published explicit left unitor,
the second is the tensor of the two input rigidifications, and the last
is the inverse of the canonical pullback tensor comparison. The two
published names `structureModule S` and `structureSheaf S` denote the
same structure sheaf as a module.

`tensorObj_rigidification_comp` proves that postcomposing this
rigidification with the comparison gives the first two arrows.
`tensorMap_compatibility` proves that tensoring two compatible module maps
preserves the new rigidification: postcompose by the invertible comparison,
apply its naturality, then apply functoriality of the sheaf tensor and the
two given rigidification equations.

`tensorMap` packages that actual map as a morphism of rigidified modules.
`tensorFunctor preservation ε` packages the object and morphism constructions
as a bifunctor. Its identity and composition laws follow from those of the
published sheaf tensor after taking underlying module maps.
`tensorForgetIso` is a natural isomorphism with identity components:
forgetting the output rigidification agrees with forgetting the two input
rigidifications and applying the published tensor bifunctor. The forgetful
functor is the already published faithful functor.

## Source and scope

Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft,
Chapter VI, paragraph (6.2), printed p.88 (PDF p.92), defines compatible
morphisms of rigidified line bundles and gives their tensor product
rigidification by precisely the composite above, suppressing the canonical
unit and pullback identifications. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
This module isolates the module-sheaf construction underlying that formula.
Its extension to arbitrary rigidified module sheaves is derived from the
same composite; it needs only the explicit comparison-invertibility premise.

The result is a bifunctor on rigidified module sheaves. It does not establish
closure of locally free rank-one modules under tensor, construct tensor
inverses, prove monoidal unit or associator coherence, or supply a group
structure on rigidified line-bundle classes. Those remain separate steps.
