# Renard II.2.1: corrected descent into an actual target sheaf

Worker 595, with Worker 6's source correction and universe design.

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.2.1, printed pp.35–37 /
PDF pp.41–43. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These three pages were read directly, and PDF p.42 was also rendered and
checked visually. The construction follows the local-image gluing on printed
p.36/PDF p.42 with the correction described below. The arbitrary raw source,
universe lifts, explicit comparison maps, and standalone intrinsic laws are
internal extensions and packaging of that construction.

All Lean names below have namespace prefix `Langlands.Sheaf.Renard`.
The module imports the published `GermUnit` and `SheafGermSeparation`
interfaces, including their actual original stalks, literal basis-sheaf gluing,
universe lifts, and canonical units.

## Source correction and hypotheses

The source attempts to infer equality of original presheaf sections from
equality of all their germs in (II.2.1.3), then obtains target-image
compatibility (II.2.1.4). The separation lemma immediately below requires a
sheaf. The arbitrary source presheaf need not satisfy that assumption.
Moreover, an arbitrary chosen basis need not contain intersections. The
published [source audit](../../../notes/renard/basis-sheafification-source.md)
explains the counterexample and the corrected target-sheaf argument, including
the bounded check of supplementary 2010-edition errata.

This implementation applies `rawTargetGermCompatibility` to the image
sections in the actual target sheaf, comparing on **every smaller basis open**
in each overlap. It never asserts (II.2.1.3) or restricts to an intersection
that might not be a basis member. The space is any `X : Type u` with its
supplied topology and any actual `OpenBasis X`. The original section universe
`v` is independent of `u`. No source normalization or separation is required
for the raw construction; the target is an actual `BasisSheaf`.

## Original-target component and local gluing

For `F : RawPresheaf.{u,v} B`, `G : BasisSheaf.{u,v} B`, and
`ψ : F ⟶ G.obj.obj`, the exposed component is

```lean
rawGermDesc ψ U : GermSections F U.obj →+ Sections G.obj.obj U
```

Its input carrier is in `max u v`, and its output is in the original value
universe `v`. This construction glues original target sections and does not
lower arbitrary larger-valued objects.

`GermDescentCover` stores an actual contained original representative for
each point of `U.obj`: the basis open, its inclusion into `U`, the representing
section, and its germ equality throughout that open. `germDescentCover`
chooses these from the input's `LocallyRepresented` proof.
`GermDescentCover.covers` is the literal `FamilyCovers` proof. Its
`compatible` theorem uses the published corrected target-compatibility
result, with the common input germ family identifying the source germs.

`rawGermDescValue` is the gluing supplied by `BasisSheaf.unique_gluing` for
these actual image sections. `rawGermDescValue_chosen` exposes its evaluation
on the chosen cover. `rawGermDescValue_germ` compares the global germ with its
restriction on the chosen neighborhood, applies that gluing equation, and
uses `rawStalkMap_germ` to prove

```text
germ_G,U,x (rawGermDescValue ψ U s) = stalkMap_ψ,x (s(x)).
```

`rawGermDesc` bundles that value as an additive homomorphism. Its zero and
addition proofs compare target germs and use only
`rawSheafGermEquality G.obj.obj G.property`. `rawGermDesc_apply` exposes its
value, and `rawGermDesc_germ` is its reusable intrinsic germ formula.

The point-indexed cover has no members when `U` is empty. The implementation
does not select a point of `U` and requires neither a nonempty domain nor a
nonempty cover. Literal sheaf gluing includes this case.
`rawGermDesc_empty` states that the output is the unique original target
section, namely zero, using the target's empty-component normalization.

## Intrinsic component laws

`rawGermDesc_representative` quantifies over **every** basis open `V` inside
`U` and **every** original section `t` representing the input family throughout
`V`. It states

```text
restriction_G,U,V (rawGermDesc ψ U s) = ψ_V(t).
```

The proof compares target germs on `V` using the intrinsic germ formula,
restriction compatibility and the given representative equality. It is
independent of the chosen cover and representatives used by the construction.
`rawGermDesc_amalgamation` applies it to any independently indexed contained
representative cover, with index universe `w` independent of `u` and `v`.
`rawGermDesc_eq_of_amalgamation` explicitly proves that any gluing of those
images equals the component, by comparing target germs at a member containing
each point. This includes empty covering families and establishes the claimed
choice independence for section gluing.

The remaining component laws are:

- `rawGermDesc_zero`, `rawGermDesc_add`, and `rawGermDesc_neg`, from its
  additive homomorphism structure;
- `rawGermDesc_restriction`, comparing the two target germ families after
  restriction;
- `rawGermDesc_sectionGerms`, obtaining the image of an original section by
  applying the arbitrary-representative formula to the whole domain;
- `rawGermDesc_precomp`, using the published `germSectionsMap` and
  `rawStalkMap_comp` for precomposition by an arbitrary raw source morphism;
- `rawGermDesc_postcomp`, using stalk-map composition and germ naturality for
  postcomposition by an actual target-sheaf morphism.

All equalities in the last two laws are detected in the actual target sheaf.
No equality-detection assertion about the source is used.

## Normalized packaging into the actual lifted target

For normalized `F : Presheaf.{u,v} B`, target
`G : BasisSheaf.{u,v} B`, and `ψ : F ⟶ G.obj`, the actual morphism is

```lean
liftedGermDesc ψ :
  (germSheafFunctor.{u,v} B).obj F ⟶ (sheafLiftJoint.{u,v} B).obj G
```

`liftedGermDesc_app` is a definitional component equation:

```text
(liftedGermDesc ψ)_U(s) = ULift.up (rawGermDesc ψ.hom U s).
```

Its naturality is the raw restriction law followed by `ULift.up`.
`liftedGermDesc_restriction` exposes this evaluation, and
`liftedGermDesc_representative` and `liftedGermDesc_sectionGerms` expose the
local and canonical-family equations in the actual lifted target.
`liftedGermDesc_factorization` proves the intrinsic categorical equation

```lean
(germSheafLiftUnit.{u,v} B).app F ≫
    (sheafForget B).map (liftedGermDesc ψ) =
  (presheafLiftJoint.{u,v} B).map ψ
```

`liftedGermDesc_precomp` states that precomposition agrees with the actual
`germSheafFunctor.map`. `liftedGermDesc_postcomp` states that postcomposition
agrees with the actual `sheafLiftJoint.map`. Their proofs evaluate components
and apply the raw composition laws under `ULift.up`.

## Direct joint-universe packaging and relift comparison

When original values already have universe `max u v`, the actual morphism is

```lean
germDesc.{u,v} ψ : (germSheafFunctor.{u,max u v} B).obj F ⟶ G
```

`germDesc_app` is definitionally the original-target component, with no extra
`ULift` in its output. The explicit restriction, arbitrary-representative,
and canonical-family equations are `germDesc_restriction`,
`germDesc_representative`, and `germDesc_sectionGerms`.
`germDesc_factorization` uses the published **direct** unit:

```lean
(germSheafUnit.{u,v} B).app F ≫
    (sheafForget B).map (germDesc.{u,v} ψ) = ψ
```

`germDesc_precomp` and `germDesc_postcomp` prove the same two composition laws
in this common category, again by evaluation and the raw laws.

`liftedGermDesc_eq_relift` compares the actual maps:

```lean
liftedGermDesc.{u,max u v} ψ ≫
    (sheafReliftJoint.{u,v} B).hom.app G = germDesc.{u,v} ψ
```

The published relift's actual hom applies `ULift.down`, so each component is
definitionally the raw descent. Conversely, `germDesc_eq_relift_inv` composes
direct descent with the actual inverse relift, whose components apply
`ULift.up`, and recovers `liftedGermDesc.{u,max u v} ψ`. These comparisons use
the published isomorphism, rather than an equality of universe categories.

## Scope

This definition unit constructs the maps and proves the intrinsic laws listed
above. Section-gluing uniqueness is used and exposed. Universal uniqueness
among arbitrary morphism factorizations, a Hom equivalence, an adjunction,
sheaf-unit invertibility, and basis/all-open equivalences are separate
successor obligations. No topology on the disjoint union of stalks or
comparison with Mathlib's all-open sheaf category is asserted here.
