# Renard A.IX: decompositions of a category by full subcategories

Lean module: `Langlands.CategoryTheory.RenardCategoryDecomposition`
(`Langlands/CategoryTheory/RenardCategoryDecomposition.lean`), namespace
`Langlands.Renard`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026 (source ID `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
Section A.IX « Décompositions de catégories » opens on printed page 268 / PDF
page 274:

> Soit 𝓜 une catégorie de Grothendieck (**AB4**\* et **AB5**) vérifiant aussi
> **AB6** et soit (𝓜ᵢ)ᵢ∈I, une famille de sous-catégories pleines. On écrit
> 𝓜 = ∏ᵢ∈I 𝓜ᵢ
> si tout objet 𝑀 de 𝓜 s'écrit comme une somme directe 𝑀 = ⨁ᵢ∈I 𝑀ᵢ
> où pour tout 𝑖, 𝑀ᵢ ∈ 𝓜ᵢ et de plus, pour 𝑖 ≠ 𝑗, quels que soient 𝑋ᵢ et 𝑋ⱼ
> respectivement objets de 𝓜ᵢ et 𝓜ⱼ, Hom_𝓜(𝑋ᵢ, 𝑋ⱼ) = {0}.

The notation `𝓜 = ∏ᵢ 𝓜ᵢ` is therefore defined by two conditions: a direct-sum
condition on every object and a vanishing condition on all off-diagonal Hom
groups. This module defines exactly these two conditions and their conjunction.
By the convention of A.VI.1 (printed page 261 / PDF page 267), « somme directe »
and `⨁` denote the coproduct.

## Declarations

Throughout, `C : Type u` with `[Category.{v} C]`, `I : Type w`, and
`P : I → ObjectProperty C`. The full subcategory at index `i` is Mathlib's
`(P i).FullSubcategory`, whose objects are the objects `X` of `C` with
`P i X`, and whose morphisms are all morphisms of `C`. Its fully faithful
inclusion is `(P i).ι : (P i).FullSubcategory ⥤ C`. `P i` is the actual class
of objects of the source's full subcategory 𝓜ᵢ. It is not a certificate that
some decomposition exists.

| Lean declaration | Kind | Needs | Content |
| --- | --- | --- | --- |
| `IsCoproductOfComponents P X` | `def … : Prop` | category | `X` is the vertex of an actual coproduct cofan with `i`-th component in `P i` |
| `EveryObjectIsCoproductOfComponents P` | `def … : Prop` | category | first source condition: the above for every `X : C` |
| `OffDiagonalHomsZero P` | `def … : Prop` | `HasZeroMorphisms C` | second source condition: all morphisms between objects of distinct `P i` are zero |
| `IsCategoryDecomposition P` | `def … : Prop` | `HasZeroMorphisms C` | the source's `𝓜 = ∏ᵢ 𝓜ᵢ`: conjunction of both conditions |
| `isCoproductOfComponents_iff_fullSubcategory` | theorem | category | the per-object condition with components taken as objects of `(P i).FullSubcategory` |
| `nonempty_isColimit_cofanMk_iff_isIso_sigmaDesc` | theorem | `HasCoproduct Y` | a cofan with vertex `X` is a coproduct iff `Sigma.desc ι : ∐ Y ⟶ X` is an isomorphism |
| `offDiagonalHomsZero_iff_subsingleton` | theorem | `HasZeroMorphisms C` | the Hom condition as `Subsingleton (X ⟶ Y)` |
| `offDiagonalHomsZero_iff_fullSubcategory` | theorem | `HasZeroMorphisms C` | the Hom condition over objects of the full subcategories |

All four definitions were inspected with `statement_returns_prop: true`. Their
complete types are:

```lean
IsCoproductOfComponents :
  {C : Type u} → [Category.{v} C] → {I : Type w} → (I → ObjectProperty C) → C → Prop
EveryObjectIsCoproductOfComponents :
  {C : Type u} → [Category.{v} C] → {I : Type w} → (I → ObjectProperty C) → Prop
OffDiagonalHomsZero :
  {C : Type u} → [Category.{v} C] → {I : Type w} → [HasZeroMorphisms C] →
    (I → ObjectProperty C) → Prop
IsCategoryDecomposition :
  {C : Type u} → [Category.{v} C] → {I : Type w} → [HasZeroMorphisms C] →
    (I → ObjectProperty C) → Prop
```

The three universes `u` (objects), `v` (morphisms) and `w` (indices) are
independent. No relation between them is assumed. Each definition has universe
parameters `w, v, u` in this order.

### The direct-sum condition

```lean
def IsCoproductOfComponents (P : I → ObjectProperty C) (X : C) : Prop :=
  ∃ (Y : I → C) (ι : ∀ i, Y i ⟶ X),
    (∀ i, P i (Y i)) ∧ Nonempty (IsColimit (Cofan.mk X ι))

def EveryObjectIsCoproductOfComponents (P : I → ObjectProperty C) : Prop :=
  ∀ X : C, IsCoproductOfComponents P X
```

Unfolded, the first source condition is

```lean
∀ X : C, ∃ (Y : I → C) (ι : ∀ i, Y i ⟶ X),
  (∀ i, P i (Y i)) ∧ Nonempty (IsColimit (Cofan.mk X ι))
```

The source's "𝑀 = ⨁ᵢ 𝑀ᵢ with 𝑀ᵢ ∈ 𝓜ᵢ" becomes: there are component objects `Y i`
satisfying `P i`, and injections `ι i : Y i ⟶ X`, such that the cofan
`Cofan.mk X ι` with vertex `X` itself is a colimit. This is the universal property
of the direct sum. For every object `Z` and maps `g i : Y i ⟶ Z` there is exactly
one `X ⟶ Z` whose composite with each `ι i` is `g i`. The colimit structure is on
the cofan built from these same displayed injections. It is not an abstract
isomorphism of `X` with some other coproduct, unrelated to the injections.

The predicate does not assume that `C` has coproducts of any size. It asks for
this one colimit for each `X`. In the source's setting a Grothendieck category is
cocomplete, so the chosen coproduct `∐ Y` exists there. For a fixed component
family `Y` with `[HasCoproduct Y]`, the theorem

```lean
theorem nonempty_isColimit_cofanMk_iff_isIso_sigmaDesc {Y : I → C} [HasCoproduct Y]
    {X : C} (ι : ∀ i, Y i ⟶ X) :
    Nonempty (IsColimit (Cofan.mk X ι)) ↔ IsIso (Sigma.desc ι)
```

states that the cofan is a colimit exactly when the canonical map
`Sigma.desc ι : ∐ Y ⟶ X` induced by the injections is an isomorphism. The proof
is Mathlib's `Cofan.nonempty_isColimit_iff_isIso_sigmaDesc` applied to
`Cofan.mk X ι`. This short intrinsic lemma explains the chosen formulation. It is
not a new source theorem.

The components are objects of `C` that satisfy `P i`, that is, objects of the
actual full subcategories. The theorem
`isCoproductOfComponents_iff_fullSubcategory` makes this explicit:

```lean
IsCoproductOfComponents P X ↔
  ∃ (Y : ∀ i, (P i).FullSubcategory) (ι : ∀ i, (P i).ι.obj (Y i) ⟶ X),
    Nonempty (IsColimit (Cofan.mk X ι))
```

Membership `P i (Y i)` is literal. `P i` is not assumed closed under
isomorphism, so the definition makes no claim about objects merely isomorphic to
members of `P i`. Later statements about isomorphism classes, such as classes of
simple objects, must handle ambient isomorphism-class images explicitly.

**Empty index type.** `I` may be empty. Then the cofan has no injections and is a
colimit exactly when its vertex is initial, so the first condition asks every
object to be initial (the empty direct sum). No special case is made for it.

### The Hom condition

```lean
def OffDiagonalHomsZero (P : I → ObjectProperty C) : Prop :=
  ∀ i j : I, i ≠ j → ∀ X Y : C, P i X → P j Y → ∀ f : X ⟶ Y, f = 0
```

This is the source's "pour 𝑖 ≠ 𝑗, quels que soient 𝑋ᵢ et 𝑋ⱼ respectivement objets de
𝓜ᵢ et 𝓜ⱼ, Hom_𝓜(𝑋ᵢ, 𝑋ⱼ) = {0}". The quantifiers range over *every* object of
both full subcategories, not over a chosen family of representatives such as the
components of one decomposition. Mathlib's `HomOrthogonal` concerns a single
family of objects, so it is not used here.

The zero morphisms come from `[HasZeroMorphisms C]`. In the source's setting
𝓜 is abelian, and a Mathlib `Abelian` instance provides this structure (through
`Preadditive`). Since `0 : X ⟶ Y` always lies in the Hom set, "Hom = {0}" means
that every morphism is zero. `offDiagonalHomsZero_iff_subsingleton` exposes the
equivalent form

```lean
OffDiagonalHomsZero P ↔
  ∀ i j : I, i ≠ j → ∀ X Y : C, P i X → P j Y → Subsingleton (X ⟶ Y)
```

and `offDiagonalHomsZero_iff_fullSubcategory` restates the condition over
objects of the full subcategories and their inclusions:

```lean
OffDiagonalHomsZero P ↔
  ∀ i j : I, i ≠ j → ∀ (X : (P i).FullSubcategory) (Y : (P j).FullSubcategory)
    (f : (P i).ι.obj X ⟶ (P j).ι.obj Y), f = 0
```

Because the inclusions are fully faithful, these are exactly the Hom groups of
𝓜 between objects of 𝓜ᵢ and 𝓜ⱼ.

### The combined predicate

```lean
def IsCategoryDecomposition (P : I → ObjectProperty C) : Prop :=
  EveryObjectIsCoproductOfComponents P ∧ OffDiagonalHomsZero P
```

`IsCategoryDecomposition P` is the source's `𝓜 = ∏ᵢ∈I 𝓜ᵢ`. The whole combined
interface requires `[HasZeroMorphisms C]`. The first condition alone is also
available without zero morphisms.

## Generality: an implementation extension

The source states the notation for a Grothendieck category 𝓜 in its own sense
(AB4\* and AB5) that also satisfies its AB6. These hypotheses are not needed to
form the two conditions, so the definitions here are stated for an arbitrary
category, with zero morphisms for the Hom condition. This generic definition is
an implementation extension. It specializes to the source's setting by taking
`C` to be such a category with its zero morphisms. No later source assertion is
claimed under the weaker assumptions. The source-specific AB4\*, AB5, AB6,
Grothendieck and finite-type predicates have nonstandard meanings and are
separate definition obligations. They are not replaced here by Mathlib
conventions with the same names.

The source writes a product sign `∏` for the decomposition of the category. The
definition does not assert or imply any equivalence between `C` and a product of
the categories `(P i).FullSubcategory`. Such an equivalence would be a separate
theorem.

## Errata

The 2010-edition correction list (`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`) belongs to a
different edition. Its appendix portion (PDF pages 18–19) contains no correction
to the definition of `𝓜 = ∏ᵢ 𝓜ᵢ`. Its entry « p. 310, l. 10 et 11 : remplacer M
par E et MS par ES » appears to concern the later construction of 𝐸_S. The 2026
text reads 𝐸 and 𝐸_S there, and that construction is outside this module. No
separate author-issued current-edition errata note exists in the Library at
this module's base. The project-authored Appendix A audit cited below is a
different document. This is a limited observation.

## Scope and pending obligations

This module contains only the definitions and short intrinsic lemmas above. It
does **not** prove or assume:

* that `P i` is nonempty, closed under isomorphism, abelian, or closed under
  subobjects, quotients, extensions or coproducts;
* the disjoint-union decomposition Irr(𝓜) = ⨆ᵢ Irr(𝓜ᵢ) of simple isomorphism
  classes for a decomposition;
* anything about the full subcategories 𝓜_S of objects whose irreducible
  subquotients lie in a set 𝑆 of simple classes (Jordan–Hölder support), their
  abelianness or closure properties;
* the largest supported subobject 𝐸_S, the vanishing of Hom between 𝓜_S and 𝓜_S′
  and of 𝐸_S ∩ 𝐸_S′ for disjoint 𝑆, 𝑆′, or the inclusion 𝐸_S ⊕ 𝐸_S′ ⊂ 𝐸;
* splitting of an object or of the category by a subset 𝑆 or a partition
  (𝑆_α), or the lemma that subquotients of a split object are split;
* any equivalence of `C` with a product of categories.

These remain obligations of parent task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`.
They cannot be inferred from the publication of these definitions. In
particular, arbitrary full subcategories need not satisfy the closure properties
used for 𝓜_S. The published note `notes/renard/appendix-a-corrections.md` records
that the source's A.VI.1 criterion (a full subcategory of A-mod closed under
submodules and quotients is abelian) is insufficient without finite-sum closure.
These definitions do not assume that criterion or any abelian structure on the
`(P i).FullSubcategory`.
