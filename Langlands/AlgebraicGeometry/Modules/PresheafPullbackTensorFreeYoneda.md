# Presheaf pullback tensor comparison on free Yoneda generators

For schemes `X Y : AlgebraicGeometry.Scheme.{u}` in arbitrary universe `u`,
a morphism `f : X ⟶ Y`, and opens `V W : Y.Opens`, write

```
A_Z(U) = (PresheafOfModules.free Z.ringCatSheaf.obj).obj (yoneda.obj U)
L = presheafPullback f
F = TopologicalSpace.Opens.map f.base
```

This module constructs, in namespace `Langlands.Scheme.Modules`,

```
presheafPullbackTensorComparisonFreeYonedaIso f V W :
  L.obj (A_Y(V) ⊗ A_Y(W)) ≅ L.obj A_Y(V) ⊗ L.obj A_Y(W).
```

The lemma `presheafPullbackTensorComparisonFreeYonedaIso_hom` identifies
its hom exactly:

```
(presheafPullbackTensorComparisonFreeYonedaIso f V W).hom =
  presheafPullbackTensorComparisonApp f A_Y(V) A_Y(W).
```

These declarations have no additional parameters or assumptions. The tensor
is the sectionwise tensor over the structure ring presheaf. It is supplied by
the file-local instance `presheafPullbackTensorFreeYonedaMonoidalCategory X`,
which has the same definition as the local instance in
`PresheafPullbackTensor`: `inferInstanceAs` applied to the monoidal instance
on `PresheafOfModulesOfCommRing X.presheaf`. This instance was first
published anonymously. Its explicit name is an integration-only correction.
Its generated name and auxiliary declarations coincided with those of the
anonymous local instance in
`Langlands.AlgebraicGeometry.Picard.RigidifiedTensorSymmetry`, so the two
modules could not be imported together. The instance body and the source
text of every other declaration are unchanged. The construction uses the
existing presheaf pullback functor and its adjunction.

Let `p_U = presheafPullbackFreeYonedaIso f U`, the isomorphism
`L.obj A_Y(U) ≅ A_X(F.obj U)`. Let

```
eY = freeYonedaInfTensorIso V W
eX = freeYonedaInfTensorIso (F.obj V) (F.obj W).
```

The inverse image of an intersection is definitionally the intersection of
the inverse images in the pinned Mathlib. Thus `eX` also has source
`A_X(F.obj (V ⊓ W))`, with no equality transport needed. The public
isomorphism is the composite

```
L.mapIso eY.symm ≪≫ p_(V ⊓ W) ≪≫ eX ≪≫ (tensorIso p_V p_W).symm.
```

This composite is implemented by the private
`tensorGeneratorPullbackIsoAux`. Its inverse, in the order of application, is

```
(tensorIso p_V p_W).hom ≫ eX.inv ≫ p_(V ⊓ W).inv ≫ L.map eY.hom.
```

The two inverse identities are supplied by composition of isomorphisms:
the inverse maps cancel the four factors in reverse order. The functorial
and tensor isomorphisms already carry the corresponding inverse laws.
Consequently the result is an actual isomorphism of presheaves of modules,
with both `hom_inv_id` and `inv_hom_id`.

To identify the specified hom, the private
`tensorGeneratorPullbackDiagram` proves

```
L.map eY.hom ≫ presheafPullbackTensorComparisonApp f A_Y(V) A_Y(W)
  ≫ (tensorIso p_V p_W).hom
  = p_(V ⊓ W).hom ≫ eX.hom.
```

It first allows arbitrary `eY` and `eX` with the indicated sources,
targets and identity-basis formulas. Apply injectivity of the hom
equivalence of `presheafPullbackPushforwardAdjunction f`, then injectivity
of `PresheafOfModules.freeYonedaEquiv`. Naturality reduces the diagram to
evaluation at the identity basis of `V ⊓ W`. The `eY` formula produces
the tensor of the two inclusion bases. The imported
`homEquiv_presheafPullbackTensorComparisonApp_app_tmul` sends it to the
tensor of their images under the adjunction unit. The tensor of `p_V`
and `p_W` acts on these two factors by
`presheafPullbackFreeYonedaIso_hom_unit_app`, producing the bases of the
inverse-image inclusions. On the other side,
`presheafPullbackFreeYonedaIso_hom_unit` sends the identity basis through
`p_(V ⊓ W)` to the identity basis of its inverse image, and the assumed
`eX` basis formula produces those same two bases.

The private `tensorGeneratorPullbackIsoAux_hom` cancels `L.map eY.hom`
and `(tensorIso p_V p_W).hom` from this diagram. It then simplifies the
composite with the inverse laws to obtain equality of its hom with the
canonical comparison.

Finally the public construction and hom lemma instantiate these private
helpers with the two displayed `freeYonedaInfTensorIso` isomorphisms.
Their basis formulas are
`freeYonedaInfTensorIso_hom_app_id`. For `eX`, the image under `F` of
each intersection inclusion agrees with the corresponding inverse-image
intersection inclusion because arrows between opens are subsingletons.
These equalities are proved by `Subsingleton.elim`. All the private
parameters and basis-law hypotheses are therefore discharged.

The content is an internal derivation from the pinned Mathlib adjunction,
free-Yoneda and tensor APIs and the imported Library constructions in
`PresheafPullbackFreeYoneda`, `FreeYonedaTensor`, and
`PresheafPullbackTensor`. No external theorem is transcribed. In
particular, the geometric inputs are the pullback formula for an individual
free Yoneda generator and preservation of intersections by inverse image.
This module constructs the specified comparison isomorphism on generator
pairs; extension to arbitrary module presheaves is separate.
