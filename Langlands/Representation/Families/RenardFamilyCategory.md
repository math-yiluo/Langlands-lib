# Renard VI.8.1: the categories of `(G, B)`-modules and of admissible ones

Author: Worker 709. Module `Langlands.Representation.Families.RenardFamilyCategory`,
namespace `Langlands.Renard.AlgebraicFamily`. It contains **definitions**: the
category `FamilyModule B G` of `(G, B)`-modules, its full subcategory
`AdmissibleFamilyModule B G` of admissible ones, and their basic accessors. It states
and proves no theorem of Renard.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated **9 July 2026**, VI.8.1 "`(G, B)`-modules", the opening paragraph and the
Définition, printed p. 187 / PDF p. 193.

Literature ID `renard-2026-representations-groupes-reductifs-padiques`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 709 read PDF pages 193–194.

The source fixes "une `ℂ`-algèbre commutative noethérienne de type fini réduite"
`B` and defines:

> Définition. Un `(G, B)`-module est un `ℂ`-espace vectoriel `V` muni d'une
> représentation lisse `(π, V)` de `G` et d'une structure de `B`-module plat, où les
> deux actions commutent. Notons `M(G, B)` la catégorie des `(G, B)`-modules. Si `K`
> est un sous-groupe compact ouvert de `G`, l'espace `V^K` est encore un `B`-module.
> Un `(G, B)`-module `V` est admissible si pour tout sous-groupe compact ouvert `K`
> de `G`, `V^K` est de type fini sur `B`.

## Lean model

The binders are `B : Type uB` with `[CommRing B]` and `G : Type uG` with
`[Group G] [TopologicalSpace G]`; carriers live in `Type uV`. The three universes are
independent.

- A `B`-linear representation `ρ : Representation B G V` is a `B`-module `V` with a
  `G`-action by `B`-linear maps, so the two actions commute. This is how the published
  [RenardFamilyStatements](RenardFamilyStatements.md) models a family. When `B` is a
  `ℂ`-algebra, the `ℂ`-vector space structure of `V` is the one obtained through `B`.
- `flatProperty B G` is the property `Module.Flat B A` of an object `A` of the
  published category `SmoothRep B G` of smooth `B`-linear representations
  ([Category/Basic](../Category/Basic.md)).
- `FamilyModule B G` is the full subcategory of `SmoothRep B G` on `flatProperty`.
  An object is a smooth `B`-linear representation on a flat `B`-module, which is
  Renard's `(G, B)`-module. A morphism is a morphism of `SmoothRep`, that is a
  `B`-linear `G`-equivariant map. `FamilyModule` is Renard's `M(G, B)`.
- `admissibleProperty B G` asks, of a `(G, B)`-module `A`, that
  `Module.Finite B (fixedVectors A.representation K.toSubgroup)` for every
  `K : OpenSubgroup G` with `IsCompact (K : Set G)`. `fixedVectors` is the published
  `B`-submodule of `K`-fixed vectors. `AdmissibleFamilyModule B G` is the full
  subcategory of `FamilyModule B G` on this property.

The accessors are the coercion to the carrier with its `AddCommGroup` and `Module B`
instances, `representation`, `isSmooth`, `flat`, the bundling maps
`FamilyModule.of` and `AdmissibleFamilyModule.of`, the inclusion functors
`FamilyModule.toSmoothRep` and `AdmissibleFamilyModule.toFamilyModule`, the
morphism conversions `FamilyModule.hom` and `FamilyModule.ofHom` with their two
`rfl` laws, and `AdmissibleFamilyModule.finite_fixedVectors`.

## Correspondence notes

1. Morphisms. The source names the category `M(G, B)` without spelling out its
   morphisms. They are read as the linear maps commuting with both actions, as in
   "morphisme de `(G, B)`-module" in VI.8.4, before its Proposition (PDF p. 198).
   This reading is Worker 709's.
2. Hypotheses on `B`. The definitions need only a commutative ring `B`. Renard's
   standing hypotheses (a reduced Noetherian `ℂ`-algebra of finite type) are not
   imposed here; statements about these categories impose them where the source
   does.
3. Compact open subgroups. As in `RenardFamilyStatements`, a compact open subgroup
   is an open subgroup with compact carrier, and admissibility quantifies over
   these. The published `SmoothRep.IsAdmissible` (`Langlands.IsAdmissible`)
   quantifies over every open subgroup instead, and is not used here.
4. The objects of `FamilyModule B G` carry exactly the hypotheses `IsSmooth ρ` and
   `Module.Flat B V` of the published family statements, and those of
   `AdmissibleFamilyModule B G` add their finiteness hypothesis on compact-open
   fixed vectors. The published statements stay unbundled; this module does not
   restate them.

## Scope

No additive, abelian or monoidal structure is put on these categories, and no
functor between them other than the two inclusions is defined. Specialization,
induction and the Jacquet module of families are not bundled as functors here.
