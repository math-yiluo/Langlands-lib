# Invertibility of the canonical sheaf pullback tensor comparison

The theorem `Langlands.Scheme.Modules.pullbackTensorComparisonIsIso` has
exactly the published type
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement.{u}`.
For arbitrary schemes `X Y : AlgebraicGeometry.Scheme.{u}` and a morphism
`f : X ⟶ Y`, it proves invertibility of the fixed natural transformation
`pullbackTensorComparison f`. Its component is the published canonical map
from `f^*(tensorObj M N)` to `tensorObj (f^*M) (f^*N)`.
There are no extra hypotheses or parameters.

The implementation imports the statement and comparison unchanged. It
transfers the unconditional presheaf comparison theorem from
`PresheafPullbackTensorProof` through sheafification, retaining the
specified sheaf comparison throughout.

## Sheafification of the pullback unit mates

Write `L` for presheaf pullback along `f.toRingCatSheafHom.hom`, `S_X` and
`S_Y` for module sheafification, and `f^*` for scheme-module sheaf
pullback. The private map `pullbackUnitMate f M`, denoted `k_M`, is

```text
L.obj M.val ⟶ (f^*M).val.
```

It is the inverse image, under the presheaf pullback adjunction's hom
equivalence, of the underlying map of the sheaf pullback adjunction unit.
`Adjunction.homEquiv_leftAdjointUniq_hom_app` identifies `k_M` with the
sheafification unit at `L.obj M.val` followed by the underlying map of
`(SheafOfModules.pullbackIso f.toRingCatSheafHom).symm.app M`.
Consequently `S_X.map k_M` is invertible: sheafification inverts its unit,
and the second factor is an isomorphism.

The lemma `sheafify_tensor_map_isIso` uses
`Functor.Monoidal.map_tensor` to show that sheafification also inverts
`k_M ⊗ₘ k_N`. The monoidal structure on sheafification comes from the
imported `TensorMonoidal` module and its tensor-localization construction.
This structure is unconditional and does not use pullback tensor
invertibility or a monoidal structure on pullback.

## Identifying the fixed sheaf comparison

Mathlib's `SheafOfModules.sheafificationCompPullback` supplies the
isomorphism

```text
S_Y ⋙ f^* ≅ L ⋙ S_X.
```

The private name `sheafifyPullbackIso f` denotes this isomorphism. Suppose
`d` is an invertible map

```text
L.obj (M.val ⊗ N.val) ⟶ L.obj M.val ⊗ L.obj N.val
```

whose presheaf-adjunction mate sends each pure tensor to the tensor of
the presheaf adjunction units. The lemma
`canonical_comparison_isIso_of_presheaf` proves that the exact published
`pullbackTensorComparisonApp f M N` equals

```text
(sheafifyPullbackIso f).hom.app (M.val ⊗ N.val)
  ≫ S_X.map (d ≫ (k_M ⊗ₘ k_N)).
```

To prove this equality, it applies the injective hom equivalence of the
composite adjunction consisting of sheafification on `Y` followed by
sheaf pullback. The lemma `composite_homEquiv_comparison` computes the
mate of the published comparison using
`homEquiv_pullbackTensorComparisonApp`,
`tensorHomEquiv_tensorMap_comp`, and
`tensorHomEquiv_pushforwardTensorApp`. This mate is the tensor of the
underlying sheaf pullback adjunction units followed by
`pushforwardTensorPresheafHom`.

For the displayed composite, `homEquiv_sheafifyPullbackIso` changes the
composite adjunction to presheaf pullback followed by sheafification.
The sheafification unit formula and its naturality reduce its mate to
the assumed pure-tensor formula for `d`. The defining mate equations
for `k_M` and `k_N` then give the same tensor of sheaf adjunction units.
Presheaf morphism extensionality and module tensor extensionality prove
equality. The ring and scalar-restriction conventions are those of the
imported scheme constructions.

Every factor in this displayed composite is invertible: the first is
an isomorphism, `S_X.map d` is invertible by functoriality, and
`S_X.map (k_M ⊗ₘ k_N)` is invertible by the preceding argument.
This proves invertibility of the specified sheaf comparison component.

## Discharging the presheaf input

The private lemma `pullbackTensorComparisonIsIso_of_presheaf` applies
the reduction to `presheafPullbackTensorComparisonApp f M.val N.val`.
Invertibility of that component follows by evaluating invertibility of
the presheaf natural transformation. Its required pure-tensor formula
is exactly the imported
`homEquiv_presheafPullbackTensorComparisonApp_app_tmul`.
`NatIso.isIso_of_isIso_app` assembles the sheaf component results into
invertibility of `pullbackTensorComparison f`.

The public theorem supplies this lemma with the unconditional theorem
`presheafPullbackTensorComparisonIsIso`. Thus the intermediate
presheaf hypothesis is discharged, and no assumed instance of the
desired sheaf comparison is introduced.

## Provenance and scope

This sheafification argument is internal derived content implemented by
Worker 150, using the pinned Mathlib adjunction and sheafification APIs
and the existing Library tensor constructions. The presheaf maps and
their pure-tensor formula, the unconditional presheaf invertibility
proof, and the unconditional monoidal sheafification structure are
imported by Lean name.

The original motivating result is Stacks Lemma 17.16.4, tag 01CD,
in the retained source `stacks-module-tensor-products-2026-10-21`, as
cited in `PullbackTensorStatement.md`. That source omits its proof;
this module makes no attribution of the implemented argument to it.
No flatness, quasicoherence, local freeness or affineness condition is
used. Associativity, unit, symmetry, and pullback identity/composition
coherence are separate obligations of the monoidal-pullback development.
