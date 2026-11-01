# Affine frame lifting and triviality along the zero section

For an arbitrary field `k : Type u`, an affine scheme `X : Scheme.{u}` and
`f : X ⟶ Spec k`, `DualNumberThickening.affineZeroSectionTrivialization`
constructs an actual module-sheaf isomorphism

```
L.obj ≅ structureModule (thickening f)
```

from an actual line bundle `L` on the actual dual-number thickening and a
specified trivialization of its pullback along `closedPoint f` to `X`.
No reducedness or smoothness hypothesis is imposed on `X`.

This is proved through a more general affine result. Let `g : Y ⟶ X` be a
morphism between affine schemes that is surjective on points and whose
actual global ring map `g.appTop : Γ(X,⊤) → Γ(Y,⊤)` is surjective. If a line
bundle on `X` becomes trivial after actual pullback to `Y`, then it is
already trivial on `X`. `lineBundle_trivial_of_affinePullback` gives
existence and `affinePullbackTrivialization` chooses an actual isomorphism.

The hypotheses imply that `g` is a surjective affine closed immersion;
the proof uses exactly the two surjectivity conditions and does not assume
a nilpotence bound on its defining ideal. In particular the conclusion
applies to the actual split square-zero thickening. The general result
requires no field or characteristic hypothesis.

## Surjectivity of actual sections

For a surjective homomorphism of commutative rings `φ : R ⟶ S` and an
`R`-module `M`, `oneTensor_surjective` proves that every element of actual
categorical scalar extension is `1 ⊗ m`. A pure tensor `s ⊗ m` has this form
by choosing `r` with `φ r = s` and moving `r` to the second factor. The sum
of two such tensors is `1 ⊗ (m + m')`. Tensor induction completes the proof.
No flatness or finite-generation assumption is needed.

For quasi-coherent `M` on `Spec R`, the existing actual affine sections
base-change isomorphism has the actual adjunction-unit sections map as its
value on `1 ⊗ m`. Surjectivity of both scalar extension and this isomorphism
therefore proves `affineSectionsPullbackMap_surjective`.

`affinePullbackSection_surjective` extends the conclusion to a morphism
between any two affine schemes whose global ring map is surjective.
The canonical maps to the spectra of their global rings are isomorphisms,
and their naturality square is consequently Cartesian. The already proved
`affineCartesianScalarSectionsIso` applies to this square. Its formula on
`1 ⊗ m`, together with `oneTensor_surjective`, gives every section of the
actual pulled-back quasi-coherent module as the pullback of a section.

`pullbackSection_eq_unit` checks that the global section pullback defined
by morphisms from the structure module agrees with the actual
pullback-adjunction unit on sections. The proof uses the canonical
`pullbackUnitIso` adjunction equation, naturality of the actual adjunction
unit, and evaluation of the section morphism at one. Thus the sections
being lifted are the existing geometric `pullbackSection`, not a substituted
map or carrier.

## Reflecting a frame and constructing a trivialization

Given a trivialization of `g*L`, apply its inverse to the unit section to
obtain a global frame. The proved sections surjectivity lifts this frame
to a global section `s` of `L`. Its pulled-back section morphism is an
isomorphism because it is the chosen trivialization's inverse.

The existing `lineBundlePullbackSectionOpen` theorem identifies the whole
generation open of the pulled-back section with the inverse image of the
whole generation open of `s`. The former is all of `Y`. Surjectivity of
`g` on points then makes the latter all of `X`. The already proved
section-morphism criterion now makes `sectionHom L s` an isomorphism.
Its inverse gives the promised actual trivialization of `L`.

For the actual zero section, `closedPoint_appTop_surjective` lifts every
ring section using the actual first-projection ring map; the scheme
identity `closedPoint f ≫ projection f = identity` proves the lift reduces
to the original section. The zero section is already known to be
surjective on points, and `thickening f` is affine over an affine `X` by
the proved affineness of its first projection. The general affine result
therefore constructs `affineZeroSectionTrivialization` directly.

## Provenance and scope

This is an internal proof built from actual affine sections base change,
quasi-coherence of the existing locally free rank-one sheaves, the proved
pullback formula for whole generation opens, and the actual thickening's
projection identities. The tensor induction and frame-lifting argument
are supplied in this module; no nilpotent Picard invariance or deformation
comparison is assumed.

This establishes the affine triviality step needed for normalized
first-order cocycle presentations. It does not yet choose normalized
local frames on an arbitrary non-affine scheme, classify rigidifications,
or prove the final tangent-to-H1 linear equivalence.
