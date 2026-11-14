# Ordered integral open cells over the maximal unramified integers

This module defines an actual ordered product of supplied integral models and
states the open-immersion clause of Kaletha–Prasad Proposition 8.3.14(3) in the
Library's maximal-unramified setting. The statement is a proposition definition;
this module does not prove it.

## Setting and compatibility

Let `F : Type u` be any nonarchimedean local field, let
`K = inertiaFixedField F`, and let `O = fixedFieldIntegers F`. The group `G`
is an affine group scheme over `K`. Supplied
`C : MaximalUnramified.BuildingData F G` records connected reductivity, a
maximal split torus `C.i : C.S.toGrp ⟶ G`, its apartment, the building action
and the actual root filtrations. No construction of building data is claimed.

The datum `E : UnramifiedZeroDatum F G` is arbitrary subject to the explicit
all-test compatibility

```text
(torusCentralizer C.i).IsRepresentedBy E.i.
```

Thus the actual inclusion `E.i : E.T.toGrp ⟶ G` represents the centralizer
of the apartment's split torus on every test scheme. Merely choosing an
unrelated maximal torus would not give this condition. The statement neither
chooses such an `E` nor proves independence of its `zeroPoints` from that choice.

For any apartment point `x` and any nonempty `Ω : Set C.Apartment` bounded
above under every real affine functional, the target quantifies over every
smooth affine flat finite-type integral model `N` with its specified generic
identification and exactly

```text
N.integralPoints =
  E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω).
```

It concludes existence of `A : TorusRootModelFamilyData C E x Ω N`.
This retains all fields of the published family interface: an actual smooth
torus model with geometrically connected fibres and integral points exactly
`E.torusIwahori`, and, for every actual relative root `a`, an actual
`RootFiltrationModelData` at `C.apartment.rootFixerDepth a x Ω`.
Each root datum supplies a generic group and inclusion representing
`RelativeRoot.subgroup C.i a` on all test schemes, a smooth affine integral
model with geometrically connected fibres, and its exact filtration-image
equation. The torus and every root model have actual compatible model maps
into `N`; their generic-fibre squares commute.

## Actual ordered source and morphism

The product definitions work for any two finite lists
`aneg : Fin nneg → relativeRoots C.i` and
`apos : Fin npos → relativeRoots C.i`. Signs and completeness are hypotheses
of the statement, rather than requirements for defining the maps.

`orderedIntegralIndex` concatenates the first list, the torus index `none`,
and the second list using `Fin.addCases` and `Fin.cases`. Its domain is
`Fin (nneg + (npos + 1))`. In increasing index order it is

```text
some (aneg 0), ..., some (aneg (nneg-1)),
none,
some (apos 0), ..., some (apos (npos-1)).
```

Here the displayed first or last list is absent when its length is zero.
`orderedIntegralFactor` selects the actual integral group model at each
index, and `orderedIntegralFactorMap` selects its supplied homomorphism into
`N.group`. `orderedIntegralProduct` is the underlying object over `Spec O`
of the categorical finite product of these group schemes, using
`Langlands.GroupScheme.Products`. Equivalently, up to the canonical
associativity isomorphism, its scheme is

```text
(product_j (A.rootModel (aneg j)).model.group)
  × A.torusModel.group
  × (product_j (A.rootModel (apos j)).model.group).
```

`orderedIntegralMultiplication` applies the published arbitrary-base
`RelativeRoot.orderedMultiplication` to the selected compatible maps.
It is an actual morphism in `Over (Spec O)`. Its underlying scheme morphism
is the `.left` field, and this is the morphism to which `IsOpenImmersion`
is applied. On every `O`-test scheme its value is the product of the mapped
factor points in the displayed order, using multiplication in `N.group`.
The multiplication morphism has no asserted homomorphism property for the
direct-product group law; the factors need not commute.

Finite categorical products also cover empty side products. If both root
lists are empty the source is a single torus factor, not an empty total
product.

## Exact target and provenance

`UnramifiedOrderedIntegralOpenCellStatement.{u}` concludes that there exists
one such `A` whose multiplication is an open immersion for every
`ν : cocharacterLattice C.S` with `IsGenericCocharacter C.i ν`, and every
pair of injective finite enumerations with character ranges exactly

```text
RelativeRoot.indivisiblePositiveRoots C.i (-ν)
RelativeRoot.indivisiblePositiveRoots C.i ν.
```

The enumerations take values in the actual root subtype, and the range
equations use its canonical inclusion into `characterLattice C.S`.
They therefore order all indivisible negative and positive roots, once each.
In a nonreduced system the doubled root remains inside the indivisible-root
factor `RelativeRoot.subgroup C.i a`; it is not an additional product index.
Both existence of `A` and the geometric open immersion are conclusions.

The source is the registered book
`kaletha-prasad-2023-bruhat-tits-new-approach`, Proposition 8.3.14(3),
printed pp. 299–300 / PDF pp. 330–331, together with Theorem 8.3.13.
The registered `kaletha-prasad-2024-corrections`, PDF pp. 37–38, imposes
perfect residue in Section 8.3 and corrects the connected-model argument:
the connected torus and root model maps first factor through the relative
identity component, before applying the open finite-index argument. A
nonarchimedean local field has perfect finite residue, so this specialization
is within that corrected field scope. Those corrections do not amend
Proposition 8.3.14(3).

The source states the cell for the canonical connected model
`G^0_Ω`. The quantification here over all smooth presentations with the
specified point image is a derived specialization. Corollaries
2.10.10–2.10.11 and Remark 2.10.19, printed pp. 124–127 /
PDF pp. 155–158, give the unique compatible integral-model isomorphisms and
maps extending the specified generic maps, since these affine smooth models
have the same integral-point images. Transporting the canonical torus/root
models and cell along those isomorphisms yields the stated all-presentations
form. Equality of point images alone is not taken as an identity of models.
Similarly, the explicit all-test generic representatives retain their chosen
maps and identifications throughout.

The statement isolates the open-immersion clause. It does not include the
same-sign products' being smooth closed subgroup schemes with unipotent
fibres. It also makes no assertion about the host special-fibre kernel,
translation into an apartment, existence of compatible zero data, torus
injectivity, or containment of a kernel in this cell. Those are separate
consumer obligations. The product constructors are internal constructions
from the named Library APIs; they add no existence assumption or theorem.
