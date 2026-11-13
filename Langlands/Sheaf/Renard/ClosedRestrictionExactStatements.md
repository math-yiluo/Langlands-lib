# Compact sections over an open subset and its closed complement (Renard II.2.5, Proposition)

Module `Langlands.Sheaf.Renard.ClosedRestrictionExactStatements`. Namespace
`Langlands.Sheaf.Renard.ClosedRestriction`. No universe parameters: as in the published II.2.5
Theorem modules, the space is `X : Type` and the sheaves are `VectorSheaf X`.

The module contains helper definitions and one **statement**, the `Prop`-valued definition
`ClosedRestrictionExactStatement`. The helpers are the objects of the source's
Proposition: the compact sections over `U` and over `Z`, the restriction map `p_Z`, and the
predicate "is the extension by zero". The only theorems are the closure and linearity laws
those definitions need. The module does not prove the Proposition.

Worker 1222 wrote this unit under the whole-book task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`.
The Library has the scalar case of the Proposition, (II.1.2.1)–(II.1.2.2). For sheaves it has
the compact sections `F_c(X)` (`CompactSupport.submodule`) and the II.2.5 Theorem. It has no
restriction of a sheaf to a closed subset and no statement of the Proposition.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read II.2.5, printed p.42 / PDF p.48:

> Si `F` est un faisceau sur l'espace t.d. `X` et que `Y` est une partie localement fermée de
> `X`, alors on définit un faisceau `F|_Y` sur `Y`, que l'on appelle restriction de `F` à `Y`. La
> fibre de `F|_Y` en un point `y ∈ Y` est égale à la fibre `F_y`, et les sections au-dessus d'un
> ouvert `U` de `Y` sont celles qui coïncident au voisinage de chaque point de `U` avec la
> restriction d'une section de `F`. […]
>
> Soient `U` un ouvert de `X`, `Z` un fermé de `X` et `F ∈ 𝒞^∞_X − Mod(X)`. De même qu'en
> (II.1.2.1), on définit deux morphismes : `i_U : F_c(U) → F_c(X)` et
> `p_Z : F_c(X) → (F|_Z)_c(Z)`. On allège les notations en posant `F_c(Z) = (F|_Z)_c(Z)`. On a alors
> un résultat qui généralise (II.1.2.1) et (II.1.2.2), et dont la démonstration est similaire :
>
> Proposition. Avec les notations ci-dessus, et `Z = X ∖ U`, on a une suite exacte
> `0 → F_c(U) → F_c(X) → F_c(Z) → 0` (flèches `i_U`, `p_Z`). Et dualement, une suite exacte :
> `0 → F_c(Z)* → F_c(X)* → F_c(U)* → 0` (flèches `p_Z^*`, `i_U^*`).

The next Remark begins: "La proposition ci-dessus affirme que toute section à support compact
`s ∈ F_c(U)` est la restriction d'une section de `F_c(X)`." In the statement below this is
clause 1: `s` is the restriction of `i_U(s)`. The Remark uses it to describe the stalk `F_x` as a
quotient of `F_c(X)`. That description is the published `CompactSectionStalks.StalkQuotientComparison`
(Task 5507) and is not restated here.

## Objects

- `VectorSheaf X` (published, [VectorSheafScalars](VectorSheafScalars.md)): Mathlib's
  `TopCat.Sheaf (ModuleCat ℂ) (TopCat.of X)`, sheaves of complex vector spaces on all opens.
  This is the category of the published II.2.5 Theorem
  ([CompactSectionTestModule](CompactSectionTestModule.md)). By the II.2.5 Proposition and
  Remark, these are Renard's sheaves of `𝒞^∞_X`-modules. By the last paragraph of II.2.1,
  sheaves on all opens are equivalent to sheaves on the compact-open base.
- `CompactSupport.submodule F.presheaf` (published, [CompactSupport](../CompactSupport.md)): the
  global sections whose support (the set of nonzero germs) is compact. This is `F_c(X)`.
- `openCompactSections F U` (helper, an `abbrev`): `F_c(U) = (F|_U)_c(U)`. It is
  `CompactSupport.submodule` applied to Mathlib's restriction
  `U.isOpenEmbedding.functor.op ⋙ F.presheaf` of `F` to the open subspace `U`. Its elements
  are sections of `F` over `U.isOpenEmbedding.functor.obj ⊤` (which equals `U`, by Mathlib's
  `Opens.isOpenEmbedding_obj_top`) with compact support in `U`.
- `IsLocalRestriction F Z t` (helper): Renard's sections of `F|_Z` over `Z`, as families
  `t : (z : Z) → F_z` of germs such that each `z ∈ Z` has an open neighbourhood `V` and a section
  `σ ∈ F(V)` with `σ_y = t(y)` for all `y ∈ Z ∩ V`. The stalks are Mathlib's stalks of `F`, as in
  the source ("la fibre de `F|_Y` en `y` est égale à `F_y`").
- `closedCompactSections F Z` (helper): `F_c(Z) = (F|_Z)_c(Z)`, the families with
  `IsLocalRestriction` whose support `{z ∈ Z | t(z) ≠ 0}` is compact. It is a complex subspace of
  the product of the stalks. `isClosed_support_of_isLocalRestriction` proves that the support is
  closed in `Z`, which gives closure under addition and scalars.
- `restrictToClosed F Z hZ` (helper): the linear map `p_Z : F_c(X) → F_c(Z)`,
  `φ ↦ (z ↦ φ_z)`. Its values lie in `F_c(Z)` because `φ` represents them on `V = X`, and because
  the support of `p_Z(φ)` is the preimage in `Z` of the compact support of `φ`, compact since `Z`
  is closed.
- `IsZeroExtension F U s φ` (helper): `φ` restricts to `s` on `U` and has zero germs at every
  point outside `U`. This is the relation `φ = i_U(s)`.

## The statement

**`ClosedRestrictionExactStatement`.** Let `X` be a t.d. space (`IsLocallyProfinite X`: Hausdorff
with a basis of compact open sets, Renard II.1.1), `F` a sheaf of complex vector spaces on `X`,
`U` an open subset, `Z = X ∖ U`, and `p_Z = restrictToClosed F Z`. Then:

1. for every `s ∈ F_c(U)` there is a unique global section `φ` with `IsZeroExtension F U s φ`,
   and it lies in `F_c(X)`. This defines `i_U : F_c(U) → F_c(X)`, which is injective because
   `φ` restricts to `s`. It also gives `p_Z ∘ i_U = 0`;
2. if `φ ∈ F_c(X)` and `p_Z(φ) = 0`, then `IsZeroExtension F U s φ` for some `s ∈ F_c(U)`:
   `ker p_Z ⊆ im i_U`;
3. `p_Z` is surjective;
4. the transpose `p_Z^* : F_c(Z)* → F_c(X)*` is injective;
5. a linear form `l` on `F_c(X)` with `l(φ) = 0` whenever `φ = i_U(s)` is in the range of `p_Z^*`:
   `ker i_U^* ⊆ im p_Z^*`. The reverse inclusion is `p_Z ∘ i_U = 0`;
6. every linear form `m` on `F_c(U)` equals `l ∘ i_U` for some linear form `l` on `F_c(X)`:
   `i_U^*` is surjective.

Clauses 1–3 are the exactness of `0 → F_c(U) → F_c(X) → F_c(Z) → 0`, and clauses 4–6 that of the
dual sequence. Here `*` is the algebraic dual, as in the source's Definition of distributions on
`F`.

## Formalization choices

- **`i_U` as a relation.** The source says that `i_U` is defined "as in (II.1.2.1)", that is,
  by extension by zero. Constructing it needs gluing in the sheaf `F` and the Hausdorff property.
  The statement asserts this as clause 1 and uses the relation `IsZeroExtension` in the other
  clauses.
- **`F|_Z` through its sections over `Z`.** Only `F_c(Z) = (F|_Z)_c(Z)` enters the Proposition.
  It is defined directly from Renard's description of the sections of `F|_Z`: families of
  germs that are locally restrictions of sections of `F`. The rest of the sheaf `F|_Z` (sections
  over smaller opens of `Z`) is not needed.
- **`F|_U`.** For the open `U`, `F|_U` is Mathlib's restriction along the open embedding.
  Its support is computed with its own stalks. These are canonically the stalks of `F` at
  points of `U`.
- **Space universe.** `X : Type`, because the published `CompactSupport` ties the space universe
  to that of `ℂ`, as in the published II.2.5 Theorem modules.

## Why the statement is true

1. Let `K` be the support of `s`, compact in `U`, hence compact and closed in `X`. The section
   `s` vanishes on `U ∖ K`. Glue `s` on `U` with `0` on the open `X ∖ K` to get `φ`. Its support
   is `K`. Uniqueness: two such sections have the same germs everywhere, so they are equal
   (`TopCat.Presheaf.section_ext`).
2. If `p_Z(φ) = 0`, the support of `φ` lies in `U`. So `s = φ|_U` has compact support, and
   `φ = i_U(s)`.
3. Let `t ∈ F_c(Z)` with compact support `S`. Cover `S` by finitely many opens on which `t` is
   given by sections of `F`. Since `X` is t.d., there are pairwise disjoint compact open sets
   `W_1, …, W_n` covering `S`, each inside one of these opens. Extend each representing section
   from `W_j` by zero (`W_j` is closed and open) and add. The sum `φ` has compact support and
   `φ_z = t(z)` on `Z`: on `Z ∩ W_j` by construction, and on `Z ∖ ⋃ W_j` both sides vanish.
4. `p_Z` is surjective, so its transpose is injective.
5. By 1 and 2, `im i_U = ker p_Z`. A linear form vanishing on `ker p_Z` factors through the
   surjection `p_Z` by a linear form on `F_c(Z)`.
6. `i_U` is an injective linear map of complex vector spaces. Every linear form on its source
   extends along it.

## Remaining obligations

The proof of `ClosedRestrictionExactStatement` is a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Sheaf.Renard.VectorSheafScalars` | `VectorSheaf` |
| `Langlands.Sheaf.CompactSupport` | `CompactSupport.submodule`; through its imports Mathlib's stalks, germs and `Γgerm` |
| `Langlands.Topology.LocallyProfinite` | `Langlands.Topology.IsLocallyProfinite` |
