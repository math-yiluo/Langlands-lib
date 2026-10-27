# Renard A.X: the center of the category of unital modules

This module states the example of David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, Appendix A.X "Centre
d'une catégorie", printed page 269 / PDF page 275. The center of the category of
unital modules over a unital ring is naturally identified with the center of the
ring. The statement uses Mathlib's general category center `CatCenter`, the
actual category `ModuleCat.{max u v} R` and Mathlib's existing scalar-action ring
homomorphism `Linear.toCatCenter`. No new center structure, module category or
map is introduced.

The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF page 275 was read in full, both as extracted text and as a rendered image.
PDF pages 11–12 (printed pages 5–6) were read for the conventions on modules, and
PDF page 18 for the forward reference from I.1.7 to A.X. The current Library has
no `notes/errata` file for this source. The registered 2010-edition errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, were
also checked. Their appendix corrections on PDF pages 18–19 were read, and a
search of their full extracted text finds no entry on the center of a category.
That errata list concerns a different edition, so the 2026 text governs here.

## The source passage

On PDF page 275 the original reads:

> **A.X Centre d'une catégorie**
>
> Soit 𝒞 une catégorie. Le centre 𝔷(𝒞) de 𝒞 est l'ensemble des endomorphismes
> (c'est-à-dire des transformations naturelles vers lui-même) du foncteur
> identité. Autrement dit, un élément *z* du centre de 𝒞 est la donnée, pour tout
> objet *X* de 𝒞, d'un morphisme *z_X* : *X* → *X*, de sorte qu'étant donnés deux
> objets *X* et *Y* de 𝒞, et un morphisme *f* : *X* → *Y*, on ait
> *f* ∘ *z_X* = *z_Y* ∘ *f*.
>
> *Exemple.* Si 𝒞 = ℳ(*A*), la catégorie des *A*-modules unitaires sur l'anneau
> unitaire *A*, alors 𝔷(𝒞) s'identifie naturellement au centre de l'anneau *A*.

In English: the center of a category is the set of natural endomorphisms of its
identity functor. For the category of unital modules over a unital ring *A*, it
is naturally identified with the center of the ring *A*.

## Conventions used

- **Modules.** In the conventions of Chapter I (PDF page 11, printed page 5),
  *A*−mod is the category of left *A*-modules. Footnote 1 there says that
  "unitaire" means that the unit of the ring acts as the identity of the module.
  On PDF page 12 (printed page 6) the book says that rings are not assumed
  unital unless stated. Modules over a unital ring are not assumed unital a
  priori. For a unital ring *A*, ℳ(*A*) is the full subcategory of *A*−mod whose
  objects are the unital *A*-modules. A.X explicitly takes a unital ring and
  unital modules, so ℳ(*A*) is the category of unital left *A*-modules. This is
  Mathlib's `ModuleCat R` for `R` with `[Ring R]`: `Module R M` requires
  `one_smul` and the left-action law `(r * s) • m = r • (s • m)`, and morphisms
  are all `R`-linear maps. The book's category of possibly nonunital modules is
  a different, earlier construction and is not used here.
- **Category center.** Mathlib's `CategoryTheory.CatCenter C` is the
  abbreviation `End (𝟭 C)`, the type of natural endomorphisms of the identity
  functor (`Mathlib/CategoryTheory/Center/Basic.lean`). This is the source's
  𝔷(𝒞). The component of `z` at `X` is `z.app X : X ⟶ X`. Mathlib's
  `CatCenter.naturality` reads `f ≫ z.app Y = z.app X ≫ f`. Since `≫` is
  composition in diagrammatic order, this is the source's *z_Y* ∘ *f* =
  *f* ∘ *z_X*. The general definition needs no preadditive structure. The
  ring structure used below is the endomorphism ring `End (𝟭 C)` of the
  identity functor in the preadditive functor category
  (`Preadditive.instSemiringEnd` over `functorCategoryPreadditive`), which
  exists because `ModuleCat R` is preadditive. Its addition is componentwise
  (`CatCenter.app_add`). Its multiplication is composition of components:
  `(x * y).app X = y.app X ≫ x.app X`, that is *(xy)_X* = *x_X* ∘ *y_X*
  (`CatCenter.mul_app'`). Mathlib's instance `IsMulCommutative (CatCenter C)`
  records that this ring is commutative.
- **Ring center.** The center of the ring `R` is Mathlib's
  `Subring.center R`, with membership
  `Subring.mem_center_iff : z ∈ Subring.center R ↔ ∀ g, g * z = z * g`. It is a
  commutative ring (`Subring.instCommRingSubtypeMemCenter`). Mathlib's instance
  `Algebra.instSubtypeMemSubringCenter`
  (`Mathlib/Algebra/Algebra/Basic.lean`) makes `R` an algebra over its center
  with `algebraMap` the inclusion `Subtype.val`.

## The actual map and its orientation

All four propositions use one and the same Mathlib ring homomorphism

```lean
Linear.toCatCenter (Subring.center R) (ModuleCat.{max u v} R) :
  Subring.center R →+* CatCenter (ModuleCat.{max u v} R)
```

from `Mathlib/CategoryTheory/Center/Linear.lean`. It goes from the center of the
ring to the center of the category. `Linear.toCatCenter S C` requires an
`S`-linear structure on `C`. Under `open scoped ModuleCat.Algebra`, Mathlib's
scoped instance `ModuleCat.Algebra.instLinear` makes `ModuleCat R` linear over
any commutative ring `S` with `[Algebra S R]`. Each module is an `S`-module
through `Module.compHom` along `algebraMap S R`. A private probe confirmed
that, for `S = Subring.center R`, instance resolution selects exactly
`ModuleCat.Algebra.instLinear` with `Algebra.instSubtypeMemSubringCenter`.

Mathlib's lemma `Linear.toCatCenter_apply_app` gives
`((Linear.toCatCenter S C) a).app X = a • 𝟙 X`. In `ModuleCat R`, the morphism
`c • 𝟙 M` acts as `m ↦ c • m`. For `c : Subring.center R` this is
`algebraMap c • m = (c : R) • m`. Hence the component at a unital left module
`M` of the image of a central element `c` is left multiplication by `c` on `M`.
It is `R`-linear because `c` is central. This is the source's natural
identification, read in the direction "ring center → category center". The
proposition `ModuleCatCenterScalarComponentStatement` records the formula in
Lean.

## Universes

`R : Type u` is an arbitrary ring and `v` is an independent universe. The module
category is `ModuleCat.{max u v} R`, the category of unital left `R`-modules
whose carriers live in `Type (max u v)`. Its morphism universe is `max u v`.
`CatCenter (ModuleCat.{max u v} R)` lives in `Type (max (u + 1) (v + 1))`. The
statements have universe parameters `u, v` in that order, and each carries
`@[pp_with_univ]`.

The size bound `max u v` is deliberate. The module category then contains the
regular module lifted to its carrier universe, `ModuleCat.of R (ULift.{v} R)`.
A later proof can evaluate a natural transformation there at
`ULift.up (1 : R)`. In a module category whose carrier universe is too small to
contain a copy of `R`, that argument is unavailable. No statement is made for
such universes. Taking `v = 0` gives the category `ModuleCat.{u} R` of modules
in the ring's own universe.

No commutativity, field, finiteness, nontriviality or abelian-category
hypothesis is imposed. The zero ring is allowed.

## Declarations

All declarations are in namespace `Langlands.Renard`. Each has explicit
arguments `(R : Type u) [Ring R]` and returns `Prop`. None of them is proved
or assumed in this module.

### `ModuleCatCenterScalarComponentStatement.{u, v} R`

```lean
∀ (c : Subring.center R) (M : ModuleCat.{max u v} R) (m : M),
  ((Linear.toCatCenter (Subring.center R) (ModuleCat.{max u v} R) c).app M).hom m =
    (c : R) • m
```

This is the component formula described above. It pins the meaning and
orientation of the map in the other statements. It is a normalization of the
source's identification by the implementation, not a numbered assertion of the
source. A private probe checked that it holds by `rfl`. That check is not
published here and is not review evidence.

### `ModuleCatCenterBijectiveStatement.{u, v} R`

```lean
Function.Bijective (Linear.toCatCenter (Subring.center R) (ModuleCat.{max u v} R))
```

The scalar-action ring homomorphism from the center of `R` to the center of the
category of unital left `R`-modules is bijective. This is the source's
"s'identifie naturellement", stated for the actual scalar-action map and not for
an arbitrary bijection of underlying sets.

### `ModuleCatCenterRingEquivStatement.{u, v} R`

```lean
∃ e : Subring.center R ≃+* CatCenter (ModuleCat.{max u v} R),
  e.toRingHom = Linear.toCatCenter (Subring.center R) (ModuleCat.{max u v} R)
```

There is a ring isomorphism whose underlying ring homomorphism is exactly the
scalar-action map. The equation with the existing map is what makes the
identification canonical. Mere existence of an abstract ring isomorphism is not
what is stated.

### `ModuleCatCenterIdentificationStatement.{u, v} R`

```lean
ModuleCatCenterBijectiveStatement.{u, v} R ∧ ModuleCatCenterRingEquivStatement.{u, v} R
```

This is the entry proposition for Renard's example. Its two clauses are the two
statements above, so each is separately usable. A private probe checked that the
two clauses imply each other, using `RingEquiv.ofBijective` in one direction and
`RingEquiv.bijective` with the equation in the other. They are both stated
because a later user may want either form directly. The component formula is a
separate proposition and is not part of this conjunction.

## Provenance

- The identification statements formalize the example in A.X, PDF page 275. The
  source asserts a natural identification without naming the map. The
  canonical map, acting on every module by left multiplication by the central
  element, is the implementation's normalization of "naturellement". The source
  gives no other map.
- The component formula is internal. It records Mathlib's existing definition
  of the map and is included so that review and later proofs can check the
  orientation.
- The carrier universe `max u v` is an implementation choice. Its reason is
  given above. The source does not discuss universes.
- Nothing is stated about naturality in the ring `R`, that is, compatibility
  with ring homomorphisms. "Naturellement" is read as "canonically, through
  the scalar action".

## Remaining proof obligations

These statements are targets for a separate proof task. All of the following
remain unproved here: the centrality of the regular-module evaluation, the
reconstruction of every component of a natural transformation from that
evaluation, bijectivity, and the inverse ring laws. A possible route is the
following. For `z : CatCenter (ModuleCat.{max u v} R)`, take
`((z.app (ModuleCat.of R (ULift.{v} R))).hom (ULift.up 1)).down : R`. Naturality
along the right multiplications of the lifted regular module shows that this
element is central. Naturality along the maps `ULift.{v} R → M`,
`r ↦ r • m`, shows that it determines every component. A private probe only
checked that this evaluation has the expected type, and that injectivity
follows from evaluation at the lifted regular module. These checks establish
neither surjectivity nor any of the obligations above.

## Coverage boundary

- The general definition of the center in A.X is Mathlib's `CatCenter`. It is
  reused by name, and no separate definition artifact is needed.
- I.1.7 (PDF page 18) describes the center of ℳ(*A*) for rings with
  idempotents and nondegenerate modules. It refers back to A.X but is a separate
  passage and is not covered here.
- The decompositions of categories in A.IX (PDF page 274) and later uses of the
  center (for example Bernstein-center statements) are not covered.
