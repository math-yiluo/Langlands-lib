# Abelianness of basis sheaves at a sufficient section universe

Worker 709 supplied the proof draft, source audit and universe argument.
Worker 1153 checked the imported interfaces and source correspondence,
prepared this proof pair and compiled both exact targets. This pair proves
the existing proposition
`Langlands.Sheaf.Renard.BasisSheafAbelianStatement.{u,v}` and its
source-axiom companion
`Langlands.Sheaf.Renard.BasisSheafAbelianAxiomsStatement.{u,v}`.
Both targets are imported unchanged from
[SheafAbelianStatements](SheafAbelianStatements.md).

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
A.VI.1, printed p.261 / one-based PDF267, lists sheaves of abelian groups on
a topological space among the abelian-category examples and states the
axioms AB0–AB3*. II.2.1, printed pp.33–34 / PDF39–40, defines presheaves on
a chosen basis (trivial sections on its empty open when present), their
morphisms, the sheaf condition (F) and the category of sheaves. These three
pages were reread for this proof, and the source fingerprint was verified.

The supplementary correction list for the 2010 edition, registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was reread at PDF2–3 and PDF18–19, and its fingerprint was verified. Those
portions do not change the cited definitions or the sheaf example. This
bounded check of older errata does not replace the governing 2026 source.

## Targets

All declarations are in `Langlands.Sheaf.Renard`, with independent universes
`u` and `v`. For every `X : Type u` with its supplied topology and every
actual basis `B : OpenBasis X`, the targets concern the published category
`BasisSheaf.{u,max u v} B`. Its objects are normalized contravariant
functors from `BasisOpen B` to `AddCommGrpCat.{max u v}` satisfying the
published literal `SheafCondition`. Its morphisms are the actual natural
transformations, and its category instance is the one supplied by
`BasisSheaf`.

| Declaration | Statement |
| --- | --- |
| `basisSheafAbelian X B` | A definition of `CategoryTheory.Abelian (BasisSheaf.{u,max u v} B)`. |
| `basisSheafAbelianStatement` | Exactly `BasisSheafAbelianStatement.{u,v}`. |
| `basisSheafAbelianAxiomsStatement` | Exactly `BasisSheafAbelianAxiomsStatement.{u,v}`. |

## Implemented proof

The proof transports Mathlib's abelian structure on sheaves on all opens.
It uses the published equivalence

```lean
BasisMathlib.equivalence.{u,v} B :
  BasisSheaf.{u,max u v} B ≌
    TopCat.Sheaf AddCommGrpCat.{max u v} (TopCat.of X)
```

from [BasisMathlibSheafEquivalence](BasisMathlibSheafEquivalence.md). That
companion composes the chosen-basis/all-open comparison with Mathlib's
sheaves.

1. Mathlib's instance `Abelian (TopCat.Sheaf C X)` in
   `Mathlib.Topology.Sheaves.Abelian` needs an abelian coefficient category
   and `HasSheafify` for the Grothendieck topology of opens. With
   `C = AddCommGrpCat.{max u v}` the first condition is a Mathlib instance.
   For the second, Mathlib's plus-plus instance in
   `Mathlib.CategoryTheory.Sites.LeftExact` needs, among its other
   hypotheses, that the forgetful functor preserves colimits indexed by the
   opposite cover categories. These categories are filtered and are indexed
   in universe `u`. A file-local instance provides
   `PreservesFilteredColimitsOfSize.{u,u}` for
   `forget AddCommGrpCat.{max u v}` by applying Mathlib's
   `preservesFilteredColimitsOfSize_shrink` to Mathlib's preservation of
   size-`max u v` filtered colimits for the forgetful functor of `AddCommGrpCat.{max u v}`
   in `Mathlib.Algebra.Category.Grp.FilteredColimits`. Lean then infers
   `HasSheafify` and the abelian sheaf category. The local instance is not
   exported.
2. Lean infers the preadditive structure on `BasisSheaf.{u,max u v} B` from
   Mathlib's instances for functor categories into a preadditive category and
   for full subcategories. Here this means the normalization subcategory of
   raw presheaves, followed by the sheaf-condition subcategory. Morphism
   addition is therefore componentwise addition of the actual natural
   transformations.
3. Finite products of basis sheaves come from
   `Adjunction.hasLimitsOfShape_of_equivalence`, applied to the forward
   functor of the equivalence, because Mathlib's abelian sheaf category has
   them.
4. `basisSheafAbelian` is Mathlib's `abelianOfEquivalence` applied to the
   forward functor of `BasisMathlib.equivalence.{u,v} B`. That construction
   keeps the existing preadditive structure of step 2 and the existing
   category. Through `abelianOfAdjunction`, it obtains kernels and cokernels
   from the abelian target along the equivalence and its inverse, and shows
   that every coimage-image comparison is an isomorphism. Like Mathlib's
   construction, the definition is marked `@[instance_reducible]`, since it
   is a definition with a class type. It is not declared as a global
   instance.
5. `basisSheafAbelianStatement` packages `basisSheafAbelian X B` in
   `Nonempty` for every `X`, topology and `B`.
   `basisSheafAbelianAxiomsStatement` applies the published
   `Langlands.Renard.abelianAxioms_iff_nonempty_abelian` to obtain the
   existing seven-axiom predicate `AbelianAxioms` for the same category. It
   introduces no second axiom interface.

The source states this example without proof. The transport route along the
published chosen-basis/all-open/Mathlib equivalence is an internal derived
proof. It is not a proof printed in the source.

## Scope and size

The section carriers lie in `Type (max u v)`, matching the targets. This
sufficient section universe is internal formalization data, inherited from
the published statements and equivalence. It accommodates compatible
families indexed by points of the space. It is neither a printed hypothesis
nor a correction attributed to Renard. No relation between `u` and `v` is
assumed. The proof makes no claim about the original-value category
`BasisSheaf.{u,v} B`, and none about whether `max u v` is necessary for a
particular space or basis.

The space, its topology and its basis are arbitrary. Empty spaces and bases
omitting the empty open are included, and no separation, compactness or
total disconnectedness is assumed. Apart from the published equivalence and
Mathlib's sheaf-category instances, the proof assumes no abelianness,
sheafification, closure property or comparison. Lean's axiom report for
`basisSheafAbelianStatement` lists only `propext`, `Classical.choice` and
`Quot.sound`.

The normalized-presheaf example, the star-sheaf size obstruction and other
A.VI.1 examples have separate statements and proofs. This pair proves only
the two cited sheaf targets.
