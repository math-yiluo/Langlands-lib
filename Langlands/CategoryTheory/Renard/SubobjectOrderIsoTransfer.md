# Transfer of Renard finiteness along subobject order isomorphisms

Module `Langlands.CategoryTheory.Renard.SubobjectOrderIsoTransfer`, namespace
`Langlands.Renard`.

## Purpose

Renard's conditions "of finite type" and "Noetherian" for an object of a category
(Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026 version,
Appendix A.I.2–A.I.3, printed pp.248–249) are encoded in
`Langlands.CategoryTheory.RenardFiniteType` (`HasSubobjectUnions`,
`IsFiniteTypeObject`, `IsNoetherianObject`). Each one depends only on the partially
ordered set `Subobject X`. This module proves that they transfer along order
isomorphisms of subobject lattices, and builds such isomorphisms for two kinds of
functor: equivalences, and inclusions of full subcategories closed under subobjects.
It is general category theory, written for the VI.7.5 argument in
`Langlands/Representation/Exponents/SupercuspidalFiniteTypeNoetherianReduction.lean`,
which moves Noetherianity between a smooth representation, the same object in an
inertia block, and its image under the Hom equivalence of VI.4.1.

Private versions of the finite-type and the Noetherian transfer lemma exist in
`Representation/Category/RenardFinitenessProof.lean` and
`Representation/Category/RenardNoetherian.lean` respectively. This module states both
publicly for arbitrary categories, and its proofs follow those versions.

## Declarations

Transfer along an order isomorphism `e : Subobject X ≃o Subobject Y`:

- `hasSubobjectUnions_of_orderIso`: if every set of subobjects of `Y` has a least
  upper bound, so does every set of subobjects of `X`. Proof: take the least upper
  bound of `e '' S` and pull it back along `e`.
- `isFiniteTypeObject_of_orderIso`: Renard finite type transfers from `Y` to `X`. The
  image under `e` of a nonempty chain of proper subobjects of `X` is again a nonempty
  chain of proper subobjects. If the chain had least upper bound `⊤`, its image would
  too.
- `isNoetherianObject_of_orderIso`: Renard Noetherianity (every nonempty set of
  subobjects has a maximal element) transfers from `Y` to `X`. Map the set by `e`,
  take a maximal element of the image, and pull it back.

Fully faithful functors. Let `F : C ⥤ D` preserve monomorphisms. Worker 1582's
`functorSubobjectMap F X` (module `NoetherianReflection`) sends a subobject `P` to
`Subobject.mk (F.map P.arrow)`.

- `SubobjectSurjective F X` (definition): every monomorphism `m : Y ⟶ F.obj X` is, up to
  an isomorphism `e : F.obj Z ≅ Y` with `e.hom ≫ m = F.map n`, the image of a
  monomorphism `n : Z ⟶ X`.
- `functorSubobjectMap_surjective`: under `SubobjectSurjective F X` the map
  `functorSubobjectMap F X` is surjective. A subobject `Q` comes from
  `Subobject.mk n`, by two applications of `Subobject.mk_eq_mk_of_comm`.
- `functorSubobjectMap_le_iff`: if `F` is also full and faithful, the map reflects the
  order. A factorization of `F.map P.arrow` through `F.map Q.arrow`
  (`Subobject.ofMkLEMk`) has a preimage under `F`, and by faithfulness this preimage
  factors `P.arrow` through `Q.arrow`.
- `functorSubobjectEmbedding` (order embedding, `OrderEmbedding.ofMapLEIff`) and
  `functorSubobjectOrderIso F X hX : Subobject X ≃o Subobject (F.obj X)`
  (`OrderIso.ofSurjective`).
- `isFiniteTypeObject_iff_of_subobjectSurjective` and
  `isNoetherianObject_iff_of_subobjectSurjective`: `X` is of finite type (respectively
  Noetherian) exactly when `F.obj X` is.

The two kinds of functor:

- `subobjectSurjective_of_isEquivalence`: an equivalence preserving monomorphisms is
  surjective on subobjects. Take `Z = F.objPreimage Y` and `n` the preimage of
  `(F.objObjPreimageIso Y).hom ≫ m`, which is a monomorphism because `F` reflects
  monomorphisms.
- `subobjectSurjective_ι`: for `P : ObjectProperty C` closed under subobjects, with
  `P.ι` preserving monomorphisms, the inclusion `P.ι` is surjective on subobjects. A
  monomorphism `m : Y ⟶ X.obj` puts `Y` in `P`, and `ObjectProperty.homMk m` is the
  required monomorphism in the full subcategory.

## Provenance

The finite-type and Noetherian conditions are Renard's A.I.2–A.I.3 definitions as
already encoded in the library. The transfer lemmas and the order isomorphisms are
standard category theory. Renard does not state them; the VI.7.5 argument uses them
implicitly when it passes between a block and a module category. No representation
theory is involved.

The nonunital-module application reuses these general union and Noetherianity transfers through its existing public theorem names.
