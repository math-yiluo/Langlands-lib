# Renard II.2.1: universal factorization, natural Hom equivalences and adjunction

Worker 1215, with Worker 6's source audit and universe design.

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.2.1, printed pp.35–37 /
PDF pp.41–43. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These three original PDF pages were read directly for this statement unit.
The published [source audit](../../../notes/renard/basis-sheafification-source.md)
records the correction of the separation step and its bounded supplementary
check of the 2010-edition errata. The 2026 original governs these statements.

The proposition on printed p.35 / PDF41 asserts the natural Hom
correspondence and the left adjunction for the locally represented
germ-family sheafification. The proof defines the canonical map and descent
on printed p.36 / PDF42, and proves that the two Hom operations are inverse
using uniqueness on printed p.37 / PDF43. The remark there restates the
universal property. The following declarations state precisely these
assertions for the actual published constructions; the additional universe
transport is internal formalization packaging.

All shortened Lean names below have prefix `Langlands.Sheaf.Renard`.
The module imports `GermDescent`, hence the actual `GermSectionSheaf`,
`GermUnit`, `BasisLift` and target-separation interfaces. It also imports
Mathlib's actual `CategoryTheory.Adjunction`. Every new declaration is a
`Prop`-valued definition. The module supplies statement targets and no proof
of universal uniqueness, Hom equivalence existence or adjunction existence.

## Universes and source hypotheses

Let `X : Type u` carry any supplied topology, and let `B : OpenBasis X` be
any actual chosen open basis. The original value universe `v` is independent
of `u`. A source is an arbitrary normalized `Presheaf B`; a target is an
actual `BasisSheaf B`. Normalization means that the original group on an
empty basis open is subsingleton. No source sheaf or separation hypothesis,
intersection closure of the basis, nonempty space, nonempty basis open,
compactness, local compactness, Hausdorffness or countability is assumed.

The actual germ carriers and the groups of locally represented germ
families have value universe `max u v`. Consequently there are two regimes:

- In the direct regime, `F : Presheaf.{u,max u v} B` and
  `G : BasisSheaf.{u,max u v} B`. Put
  `L = germSheafFunctor.{u,max u v} B`. Its target has the same value universe,
  since taking the maximum with `u` again changes no universe level.
  The maps are the actual `germSheafUnit.{u,v}` and `germDesc.{u,v}`.
- In the lifted regime, `F : Presheaf.{u,v} B` and
  `G : BasisSheaf.{u,v} B`. Put `L = germSheafFunctor.{u,v} B`,
  `I = presheafLiftJoint.{u,v} B`, and `J = sheafLiftJoint.{u,v} B`.
  The target is exactly `J.obj G`. The maps are the actual
  `germSheafLiftUnit.{u,v}` and `liftedGermDesc.{u,v}`.

These are the published functors and natural transformations, rather than
arbitrary functors equipped with assumed equivalences.

## Universal factorization and its actual witness

`GermUniversalFactorizationStatement B` quantifies over every direct `F`,
`G` and `ψ : F ⟶ G.obj`. It states the factorization

```text
germSheafUnit.app F ≫ sheafForget.map (germDesc ψ) = ψ
```

and, for every actual sheaf morphism `χ : L.obj F ⟶ G`, the equivalence

```text
germSheafUnit.app F ≫ sheafForget.map χ = ψ
  ↔ χ = germDesc ψ.
```

Thus the candidate is explicitly the published descent, and uniqueness
concerns all sheaf morphisms with that source and target.

`LiftedGermUniversalFactorizationStatement B` gives the analogous
factorization and uniqueness for arbitrary original values. Its displayed
equation is

```text
germSheafLiftUnit.app F ≫ sheafForget.map χ = I.map ψ
  ↔ χ = liftedGermDesc ψ,
```

where `χ : L.obj F ⟶ J.obj G` and `sheafForget` has value universe
`max u v`. The separate factorization conjunct substitutes
`liftedGermDesc ψ` for `χ`. The factorization conjuncts repeat the intrinsic
published `germDesc_factorization` and `liftedGermDesc_factorization` laws;
universal uniqueness is the new statement obligation.

## The natural Hom equivalences

`GermNaturalHomEquivalenceStatement B` asserts existence of one family

```text
e F G : (L.obj F ⟶ G) ≃ (F ⟶ G.obj)
```

for all direct sources and targets. Its forward map is exactly
`χ ↦ germSheafUnit.app F ≫ sheafForget.map χ`, and its inverse is exactly
`ψ ↦ germDesc ψ`. The family is a conclusion of the proposition, with no
equivalence hypothesis. Each `Equiv` includes both inverse laws.

The same family must obey both forward naturality equations. For source
morphisms `φ : E ⟶ F`, target morphisms `θ : G ⟶ H`, and suitable `χ`,
these are

```text
e E G (L.map φ ≫ χ) = φ ≫ e F G χ
e F H (χ ≫ θ) = e F G χ ≫ sheafForget.map θ.
```

`LiftedGermNaturalHomEquivalenceStatement B` asserts existence of

```text
e F G : (L.obj F ⟶ J.obj G) ≃ (F ⟶ G.obj).
```

Here its literal forward and inverse formulas are

```text
e F G χ =
  presheafLower.{u,v,u}
    (germSheafLiftUnit.app F ≫ sheafForget.map χ)
(e F G).symm ψ = liftedGermDesc ψ.
```

The composition inside `presheafLower` is a morphism from `I.obj F` to
`I.obj G.obj`: forgetting the actual `J.obj G` gives the latter object by
the published lift definitions. Only this morphism between actual lifted
objects is lowered. No object-lowering functor or operation on arbitrary
larger-valued presheaves is asserted.

Lifted forward source naturality has the same formula
`e E G (L.map φ ≫ χ) = φ ≫ e F G χ`. Lifted forward target naturality is

```text
e F H (χ ≫ J.map θ) = e F G χ ≫ sheafForget.map θ,
```

where the forgetful map on the right is in the original value universe `v`.

The named companions `GermDescentNaturalityStatement B` and
`LiftedGermDescentNaturalityStatement B` retain both inverse naturality
equations for the literal maps. In the direct regime they assert

```text
germDesc (φ ≫ ψ) = L.map φ ≫ germDesc ψ
germDesc (ψ ≫ sheafForget.map θ) = germDesc ψ ≫ θ.
```

The lifted equations replace `germDesc` by `liftedGermDesc` and replace the
last `θ` by `J.map θ`. These are precisely the meanings of the published
`germDesc_precomp`, `germDesc_postcomp`, `liftedGermDesc_precomp` and
`liftedGermDesc_postcomp`; the companions use `sheafForget.map θ` for the
same underlying presheaf morphism. Together with the specified inverse
formulas, they state inverse naturality for the asserted equivalence families.

## The direct adjunction

`GermAdjunctionStatement B` asserts existence of an actual

```text
a : germSheafFunctor.{u,max u v} B ⊣ sheafForget.{u,max u v} B.
```

It requires equality of the entire natural transformation
`a.unit = germSheafUnit.{u,v} B`, the same direct forward Hom formula,
and `(a.homEquiv F G).symm ψ = germDesc.{u,v} ψ`. For every target `G`,
it also specifies

```text
a.counit.app G = germDesc.{u,v} (𝟙 G.obj).
```

The quantified object is Mathlib's actual `Adjunction`, whose fields include
both triangle laws; they are consequently part of this existence conclusion.
The proposition does not assume an adjoint functor or a Hom equivalence.
The counit formula and the explicit naturality companions are the internal
categorical unpacking of the source's adjunction assertion.

## Aggregate, correction and boundaries

`GermUniversalStatement.{u,v}` is the closed aggregate of all seven named
propositions, universally quantified over `X`, its supplied topology and
the chosen `B`. It retains both independent universes and every empty case.
It is intended as the exact target of a later proof unit.

The printed proof attempts to infer equality of original source sections
from equality of their germs in (II.2.1.3). Its zero-germ lemma requires a
sheaf, whereas the source of the universal property is arbitrary. The
published descent instead sends local original representatives into the
actual target sheaf and applies target separation to their restrictions on
every smaller basis open within an overlap. This proves the required image
compatibility (II.2.1.4), permits sheaf gluing, and uses neither source
separation nor membership of the intersection in the basis. Empty domains
are handled by the same sheaf gluing and normalization interfaces.
The statements therefore retain the arbitrary sources of the governing
proposition without adopting that false intermediate assertion.

This unit defines the universal-property targets for the actual basis
germ sheafification. Universal-property proofs, invertibility of the unit
on sheaves and the basis/all-open category equivalence following the source
proposition remain separate units. Compact sections, scalar-module
extensions and comparison with Mathlib's all-open sheaf category are also
outside this statement family.
