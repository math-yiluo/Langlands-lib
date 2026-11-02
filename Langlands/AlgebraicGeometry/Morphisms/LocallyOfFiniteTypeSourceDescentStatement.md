# Local finite type descends along fppf covers of the source

Author: Worker 293.

`Langlands.AlgebraicGeometry.LocallyOfFiniteTypeSourceDescentStatement.{u}`
states a proposition for an arbitrary universe `u`. It quantifies over all
actual schemes `X Y S : Scheme.{u}` and all scheme morphisms `f : X ⟶ Y` and
`g : Y ⟶ S`. Its hypotheses, in order, are `Surjective f`, `Flat f`,
`LocallyOfFinitePresentation f` and `LocallyOfFiniteType (f ≫ g)`. Its
conclusion is `LocallyOfFiniteType g`. This module defines the proposition
and supplies no proof or default witness; a separate proof is still needed.

## Meaning of the predicates

All four predicates are Mathlib's classes on scheme morphisms, applied as
ordinary hypotheses. `f ≫ g : X ⟶ S` is the composite "first `f`, then
`g`".

- `Surjective f` says that the underlying map of topological spaces is
  surjective.
- `Flat f` says that for every affine open `U` of `Y` and every affine open
  `V` of `X` with `V ≤ f ⁻¹ᵁ U`, the induced ring map `Γ(Y, U) ⟶ Γ(X, V)` is
  flat. Mathlib's `AlgebraicGeometry.Flat.iff_flat_stalkMap` shows that this
  is equivalent to flatness of every stalk map, the pointwise definition used
  in the Stacks Project.
- `LocallyOfFinitePresentation f` and `LocallyOfFiniteType (f ≫ g)` are
  defined in the same way, asking that these ring maps be of finite
  presentation, respectively of finite type. Mathlib's `HasRingHomProperty`
  instances for both classes show that they are affine-local, so they can
  equivalently be checked on affine open covers, as in the Stacks
  definitions.

Together the three hypotheses on `f` say that `f` is a surjective, flat,
locally finitely presented morphism, so the single morphism `f` covers `Y`
in the fppf sense.

## Source correspondence

The source is the Stacks Project, chapter *Descent*, Lemma 14.3, stable tag
[02KL](https://stacks.math.columbia.edu/tag/02KL) (Lemma 35.14.3 in the
online numbering), printed page 43 of the registered PDF. It cites
EGA IV, 17.7.5 (i) and (ii). The lemma considers a commutative triangle of
scheme morphisms `f : X → Y`, `q : Y → S` and `p : X → S`. It assumes that `f`
is surjective, flat and locally of finite presentation and that `p` is
locally of finite presentation (respectively locally of finite type). It
concludes that `q` is locally of finite presentation (respectively locally
of finite type).

This declaration is exactly the "respectively locally of finite type"
branch. The source's `q` is `g`, and commutativity determines the source's
`p` as `f ≫ g`, so `p` is written as that composite instead of a separate
morphism with a commutativity hypothesis. No generality is lost. The
finite-presentation branch of the same lemma is not stated here.

The same implication underlies Lemma 28.2, tag
[036O](https://stacks.math.columbia.edu/tag/036O) (Lemma 35.28.2 online,
printed p.65): being locally of finite type is fppf local on the source.
Its proof checks condition (4) of Lemma 26.4, tag
[036H](https://stacks.math.columbia.edu/tag/036H) (printed p.64), by Lemma
14.2, tag [0367](https://stacks.math.columbia.edu/tag/0367). Condition (4)
is the special case of this implication for affine schemes with a
surjective, flat, finitely presented affine cover. Lemma 28.1, tag 036N,
is the finite-presentation analogue and is not stated here.

The source proof, which is not formalized here, runs as follows. The
question is local on `S` and `Y`, so both are taken affine. Flat morphisms
that are locally of finite presentation are open, so finitely many affine
opens `X_i` of `X` have images covering the quasi-compact `Y`. Then `X` is
replaced by the affine disjoint union of the `X_i`. The affine case is
Lemma 14.2 (0367): for ring maps `R → A → B`, if `R → B` is of finite type
and `A → B` is faithfully flat and of finite presentation, then `R → A` is
of finite type. Its proof uses the approximation result Algebra, Lemma
168.2. Any proof of this declaration may follow a different route.

## Precomposition, not base change

The cover `f` maps onto the source `Y` of `g`. The hypothesis concerns the
precomposite `f ≫ g : X ⟶ S`, which has the same target `S` as `g`. Base-change
descent is different. There, a cover `S' ⟶ S` of the target is given, and
the hypothesis concerns the pulled-back morphism `Y ×_S S' ⟶ S'`. Mathlib
proves that form, `MorphismProperty.DescendsAlong @LocallyOfFiniteType
(@Surjective ⊓ @Flat ⊓ @QuasiCompact)` in
`Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent`. That instance needs
a quasi-compact cover of the target, and it applies to pullback squares, not
to precomposites, so it does not yield this proposition.

The statement is also not the easy cancellation
`AlgebraicGeometry.locallyOfFiniteType_of_comp`. That lemma deduces local
finite type of the first factor `f` from that of `f ≫ g`. Here the
conclusion concerns the second factor `g`. That conclusion is not among the
hypotheses, and the hypotheses on `f` cannot simply be dropped: for the
empty scheme `X`, `f ≫ g` is always locally of finite type, while `g` need
not be.

## Scope

The universe, the schemes `X`, `Y`, `S` and the morphisms are arbitrary. No
quasi-compactness of `f`, `g` or any scheme is assumed. There are no
quasi-separatedness, separatedness, Noetherian, affineness, finite-type-base
or field hypotheses, and the source assumes none. The three hypotheses on
`f` are exactly the source's.

## Intended consumer

The immediate application is the etale surjective case. Mathlib's
`AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified` shows that an
etale morphism is flat and locally of finite presentation. So an etale
surjective `f` with locally finite type `f ≫ g` gives a locally finite type
`g`. Task `22877948-227b-4ad5-bdb3-e13f5ea18c3d` needs this for an etale
surjective map `b.left` with `b.left ≫ P.hom = U.hom` and local finite type
of `U.hom`, to conclude local finite type of `P.hom`. Stating the
proposition establishes none of that task's remaining obligations.

## Retained source

The registered source is `stacks-descent-ed88ff78-2026`: *Stacks Project —
Descent*, version ed88ff78, compiled July 14, 2026, file SHA-256
`28e718bac216bb7c4584e9edb1d25d6420ee19a6cd536742c58599242ff8cad4`. Printed
pages 42–44 (Section 14, Lemmas 14.1–14.5) and 62–65 (Sections 26–28,
including Definition 26.1, Lemmas 26.2–26.4, 28.1 and 28.2) were read. No
source-specific project errata note was found.
