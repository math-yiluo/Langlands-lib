# Identity and composition on actual derived geometric inverse images

This module constructs identity and composition isomorphisms for the existing
actual derived inverse-image functors, on unbounded and bounded-below derived
categories. It identifies them on every complex representative with localization
of the existing geometric comparisons on complexes.

## Parameters and scope

Let `X`, `Z`, and `V` belong to `Scheme.{u}`, let `f : Z ⟶ X` and
`g : V ⟶ Z` be arbitrary morphisms, and let `R : Type u` be a commutative
ring. The category `ModuleSheaf X R` is the actual category of
`ModuleCat.{u} R`-valued sheaves on `X.smallEtaleTopology`. No etaleness,
flatness, affineness, finiteness or Noetherian hypothesis is imposed.

The chosen derived categories of the sheaf categories on `X`, `Z`, and `V`
have independent localization morphism universes `wX`, `wZ`, and `wV`. The
identity constructions use only the category on `X`; composition uses all
three. There is no derived category of coefficient modules among the inputs
of this module. Write `L_f = EtaleInverseImage.inverseImage f R`,
`D_f = EtaleDerivedInverseImage.functor f R`, and `D⁺_f = plusFunctor f R`.
The existing `D_f` is the exact functor `L_f.mapDerivedCategory` obtained by
localizing the termwise inverse image at quasi-isomorphisms. Its restriction
`D⁺_f` preserves the same actual lower cohomological bound. These are the
previously constructed functors, with no new cohomology objects or chosen
comparisons as parameters.

## Unbounded comparisons

`functorId R X` constructs the natural isomorphism

```text
D_id ≅ 𝟭 (DerivedCategory (ModuleSheaf X R)).
```

It applies `Localization.liftNatIso` to the following fixed natural
isomorphism on cochain complexes:

```text
C(L_id) ⋙ Q ≅ C(𝟭) ⋙ Q ≅ 𝟭 ⋙ Q ≅ Q.
```

Here `C(L)` denotes `L.mapHomologicalComplex (.up ℤ)`, and `Q` denotes the
actual derived localization. The first two comparisons are
`NatIso.mapHomologicalComplex (inverseImageId R X) (.up ℤ)` and
`Functor.mapHomologicalComplexIdIso`, whiskered by `Q`. The last is the
functor left unitor. The lifting structures are the existing exact-functor
localization factors and the identity lifting. In particular the comparison
is determined from the actual ordinary geometric identity isomorphism.

For every unbounded cochain complex `K`, `functorId_hom_app_Q` proves

```text
functorId.hom.app (Q.obj K)
  = factors_id.hom.app K ≫ Q.map (complexId.hom.app K),
```

where `complexId` is precisely the composite of the two termwise comparisons
above. The proof unfolds the constructed lift, uses
`Localization.liftNatTrans_app`, and simplifies the actual lifting
isomorphisms and unitors.

`functorComp R f g` constructs

```text
D_f ⋙ D_g ≅ D_(g≫f).
```

It localizes the original
`Functor.mapHomologicalComplexCompIso (inverseImageComp R f g) (.up ℤ)`
whiskered by `Q`, preceded by the inverse functor associator. The lifting
structure for the source is the composite exact-functor lifting; the target
uses its existing factor. Thus the order is first inverse image along `f`,
then along `g`, compared with inverse image along `g ≫ f`.

`functorComp_hom_app_Q` computes its component at every representative:

```text
functorComp.hom.app (Q.obj K)
  = D_g.map (factors_f.hom.app K)
    ≫ factors_g.hom.app (C(L_f).obj K)
    ≫ Q.map (complexComp.hom.app K)
    ≫ factors_(g≫f).inv.app K.
```

Here `complexComp` is that exact original termwise composition isomorphism.
The proof again uses `liftNatTrans_app`, the actual lifting structures, and
associativity. These formulas specify the maps of the constructed natural
isomorphisms, rather than merely asserting that some comparison exists.

## Bounded-below restrictions

`plusFunctorId R X` and `plusFunctorComp R f g` construct

```text
D⁺_id ≅ 𝟭 (DerivedCategory.Plus (ModuleSheaf X R)),
D⁺_f ⋙ D⁺_g ≅ D⁺_(g≫f).
```

Each component is the preimage of the corresponding unbounded isomorphism
under the fully faithful inclusion `DerivedCategory.Plus.ι`. Naturality is
proved by applying that faithful inclusion and using the naturality already
proved for the unbounded comparison. No different derived functors are
introduced.

For `K : CochainComplex.Plus (ModuleSheaf X R)`, the two representative
formulas `plusFunctorId_hom_app_Q` and `plusFunctorComp_hom_app_Q` prove

```text
plusFunctorId.hom.app (Q⁺.obj K)
  = plusFactors_id.hom.app K
    ≫ Q⁺.map (inverseImageComplexId.hom.app K),

plusFunctorComp.hom.app (Q⁺.obj K)
  = D⁺_g.map (plusFactors_f.hom.app K)
    ≫ plusFactors_g.hom.app (C⁺(L_f).obj K)
    ≫ Q⁺.map (inverseImageComplexComp.hom.app K)
    ≫ plusFactors_(g≫f).inv.app K.
```

The `plusFactors` are the existing factors of the actual inverse-image
functors, `Q⁺` is `DerivedCategory.Plus.Q`, and the two coefficient-complex
isomorphisms are the constructed comparisons from
`EtaleComplexPullbackCoherence`. The proofs apply the faithful derived
inclusion, expose its images of the actual factors, and substitute the
unbounded representative formulas. Functorial congruence reduces the
remaining comparison to equality of maps of cochain complexes. Degreewise
extensionality and `inverseImageComplexId_hom_f` or
`inverseImageComplexComp_hom_f` identify those maps with the original
ordinary geometric comparison.

## Provenance and remaining obligations

This is internal categorical infrastructure derived from the existing exact
geometric inverse image and its ordinary and complex comparison maps. The
original pinned Mathlib ingredients are
`CategoryTheory/Localization/Predicate.lean` (`liftNatIso`,
`liftNatTrans_app`, identity lifting) and
`Algebra/Homology/DerivedCategory/ExactFunctor.lean` (exact-functor and
composite lifting structures). The fully faithful bounded-below inclusion
and its localization are those in
`Algebra/Homology/DerivedCategory/Plus.lean`. The text above describes the
implemented proofs, including the normalization through the previously
constructed factors.

This module constructs geometric comparison isomorphisms and their
representative formulas. It does not establish the full associativity and
unit coherence equations between iterated derived comparisons, their
compatibility with shifts, derived global-section or higher-cohomology
pullback laws, agreement with the older etale-restriction model,
coefficient-ring coherence, compact supports, smooth actions, or the Harris
specialization. Those remain separate obligations. No preservation of
injective sheaves by inverse image, or exactness of geometric direct image,
is assumed or claimed.
