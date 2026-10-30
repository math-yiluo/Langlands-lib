# Renard A.IX: coproducts and colimits of supported objects

Author: Worker 985, who wrote, checked and documented this proof pair
without reusing a shared draft. The task is
`0783ae65-dcfd-41db-ba88-aa112d9c3836`, published by Worker 1006. The proved
statement pair `Langlands.CategoryTheory.Renard.SimpleSupportColimitStatements`
was written by Workers 6 and 1006 and is left unchanged.

The module `Langlands.CategoryTheory.Renard.SimpleSupportColimit`, namespace
`Langlands.Renard`, proves the published aggregate proposition

```lean
theorem simpleSupportColimitClosure (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSupportColimitClosureStatement.{w,t} C
```

with independent universes: source family universe `w`, diagram Hom
universe `t`, ambient Hom universe `v` and ambient object universe `u`.
Its complete unapplied type is
`∀ (C : Type u) [Category.{v} C] [Abelian C], SimpleSupportColimitClosureStatement.{w,t,v,u} C`.
It imports by Lean name, unchanged, the statement module, the public proof
`Langlands.CategoryTheory.Renard.SimpleSubquotientSum`, and Mathlib's
`Mathlib.CategoryTheory.Subobject.Limits` for image subobjects.

## Source

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`
(recomputed by Worker 985). In A.IX, printed page 268 / PDF page 274, `M` is a
Grothendieck category (AB4\* and AB5) that also satisfies AB6, and `S` is a
subset of `Irr(M)`. The source states: "Alors `M_S` est une sous-catégorie
abélienne, stable par passage aux sous-quotients, aux extensions et aux
colimites." In translation: `M_S` is an abelian subcategory, stable under
subquotients, extensions and colimits. The source gives no proof. This unit
proves only the colimit clause, in the form fixed by the published statement
pair. Worker 985 also read A.VI.2–3 on PDF269–270: the axioms AB4\*, AB5 and
AB6, and the Lemma whose item (iii) reads `JH(∑_{i∈I} M_i) = ⋃_{i∈I} JH(M_i)`.
That item is the published `simpleSubquotientSum` used below. The errata
situation is recorded in the statement Markdown and was not extended here.

The route below is internal. The source states the closure without an
argument; the two-step reduction to coproducts and to the published sum
identity is Worker 985's implementation, following the route suggested by
the task.

## Declarations

Common binders are `{C : Type u} [Category.{v} C] [Abelian C]` unless stated.

| Declaration | Statement |
| --- | --- |
| `epi_sigmaDesc_of_isColimit hc` | For any category `C`, `{J : Type w} [Category.{t} J] {F : J ⥤ C} {c : Cocone F}`, `hc : IsColimit c` and `[HasCoproduct fun j => F.obj j]`: `Epi (Sigma.desc fun j => c.ι.app j)` |
| `HasSimpleSupport.of_epi p hX` | `{S} {X Y}`, `p : X ⟶ Y`, `[Epi p]`: `HasSimpleSupport S X → HasSimpleSupport S Y` |
| `HasSimpleSupport.of_mono m hY` | `{S} {X Y}`, `m : X ⟶ Y`, `[Mono m]`: `HasSimpleSupport S Y → HasSimpleSupport S X` |
| `epi_subobjectSum_imageSubobject_arrow F` | With `[HasCoproducts.{w} C]`, `{I : Type w}`, `F : I → C`: `Epi (subobjectSum fun i => imageSubobject (Sigma.ι F i)).arrow` |
| `subobjectSum_imageSubobject_sigmaι F` | Same binders: `subobjectSum (fun i => imageSubobject (Sigma.ι F i)) = ⊤` |
| `simpleSubquotientClasses_sigma_subset hG hAB6 F` | `hG : IsSourceGrothendieck.{w} C`, `hAB6 : SourceAB6 C`, `{I : Type w}`, `F : I → C`, with `letI : HasCoproducts.{w} C := hG.1`: `simpleSubquotientClasses (∐ F) ⊆ ⋃ i, simpleSubquotientClasses (F i)` |
| `simpleSupportCoproduct C` | `SimpleSupportCoproductStatement.{w} C`, explicit `C` |
| `simpleSupportColimit C` | `SimpleSupportColimitStatement.{w,t} C`, explicit `C` |
| `simpleSupportColimitClosure C` | `SimpleSupportColimitClosureStatement.{w,t} C`, explicit `C` |

`HasSimpleSupport.of_mono` is a reusable companion of `of_epi` and is not
used by the main proof. `subobjectSum_imageSubobject_sigmaι` records the
source-style fact that the images of the injections sum to the whole
coproduct; the main proof uses the epimorphism form
`epi_subobjectSum_imageSubobject_arrow` directly.

## The implemented proof

**Colimit vertex as a quotient.** `epi_sigmaDesc_of_isColimit` holds in any
category. Given `g h : c.pt ⟶ Z` with `Sigma.desc c.ι.app ≫ g = Sigma.desc c.ι.app ≫ h`,
precomposing with the injection `Sigma.ι _ j` and simplifying with the
coproduct factorization equation gives `c.ι.app j ≫ g = c.ι.app j ≫ h` for
every `j`. Hom-extensionality of the colimit, `hc.hom_ext`, gives `g = h`.
Only the coproduct indexed by the objects of `J` is used; no coproduct
indexed by arrows and no size condition on the Hom types of `J` occur.

**Support transport.** `HasSimpleSupport S X` is the public inclusion
`simpleSubquotientClasses X ⊆ S`. `of_epi` and `of_mono` compose this
inclusion with the public `simpleSubquotientClasses_subset_of_epi` and
`simpleSubquotientClasses_subset_of_mono`.

**The injection images exhaust the coproduct.** Fix `[HasCoproducts.{w} C]`,
`I : Type w` and `F : I → C`, and put
`G i := imageSubobject (Sigma.ι F i) : Subobject (∐ F)`. Define
`s : ∐ F ⟶ ∐ fun i => (G i : C)` by `Sigma.desc`, with `i`-th component
`factorThruImageSubobject (Sigma.ι F i) ≫ Sigma.ι _ i`. Using the public
`subobjectSumπ_arrow` and checking components with `ext i` and `simp`
(the coproduct factorization and `imageSubobject_arrow_comp`),
`(s ≫ subobjectSumπ G) ≫ (subobjectSum G).arrow = 𝟙 (∐ F)`.
Hence the arrow of `subobjectSum G` is epi (`epi_of_epi_fac`). Being also a
mono, it is an isomorphism in the abelian category, and
`Subobject.eq_top_of_isIso_arrow` gives `subobjectSum G = ⊤`.

**Simple subquotients of a coproduct.** In
`simpleSubquotientClasses_sigma_subset`, a class `q` of `∐ F` is a class of
the underlying object of `subobjectSum G`, by epi transport along its arrow.
The published `simpleSubquotientSum C hG hAB6 (∐ F) I G` identifies these
classes with `⋃ i, simpleSubquotientClasses (G i : C)`. So `q` is a class of
some `G i`, and since `factorThruImageSubobject (Sigma.ι F i) : F i ⟶ G i`
is epi, `q` is a class of `F i`. The coproduct instance is `hG.1`, as in the
statement, and the published sum identity is applied at the same family
universe `w` with the same `hG` and `hAB6`.

**Coproduct component.** For `hF : ∀ i, HasSimpleSupport S (F i)`, every
class of `∐ F` lies in some `simpleSubquotientClasses (F i) ⊆ S`. This
covers every `I : Type w`, including empty `I`, where the union is empty.

**Colimit component.** Given `J : Type w`, `[Category.{t} J]`, `F : J ⥤ C`,
`c : Cocone F`, `hc : IsColimit c` and support of every `F.obj j`, install
`HasCoproducts.{w} C` from `hG.1`. The coproduct component applied to the
`J`-indexed family `fun j => F.obj j` gives support of its coproduct, and
`HasSimpleSupport.of_epi` along the epi `Sigma.desc fun j => c.ι.app j`
gives support of `c.pt`. Empty `J` is included.

The aggregate theorem is the pair `⟨simpleSupportCoproduct C, simpleSupportColimit C⟩`.

## Scope

Every quantifier and hypothesis of the published statement is retained. The
proof adds no smallness, arrow-smallness, well-poweredness, generator,
separator, finite-type, finite-length, module or concrete-category premise,
no global colimit existence, and no identification of `w`, `t`, `v` or `u`.
The coproduct instance is the one supplied by `hG.1`, and the support
conclusion is the unchanged public `HasSimpleSupport`; no support-closure
certificate is assumed. The premise `S ⊆ simpleClasses C` is retained but
not used: the argument works for any set `S` of object classes. AB5 and AB6
enter only through the published `simpleSubquotientSum`.

Subquotient, extension and finite closure, abelianness of `M_S`, support and
maximality of `E_S`, Hom orthogonality, splitting and product decompositions
are not addressed here and remain with their separate tasks.

## Development check

In approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, the module
compiled without errors or warnings (diagnostic
`3ad1b13b-8274-4e9d-b03b-263bbe027d0d`). Inspection
`47c3d626-5ab9-4d50-a457-90f8b178850c` of `simpleSupportColimitClosure`
reported universe order `w, t, v, u` and only the axioms `propext`,
`Classical.choice` and `Quot.sound`. The final workspace check
`94f8e024-5eaf-46ba-9ba1-7a7a92376bdf` repeated this with the same result. A private probe, excluded from this
pair, completed with zero errors or warnings (diagnostic
`0d0a88d2-6ec3-4a69-92ce-03c1cd32d686`). It printed the complete unapplied
types of all nine declarations and the bodies of the three statement
definitions, checked by `example` that `@simpleSupportColimitClosure.{w,t,v,u}`
has the complete aggregate type above and is definitionally the pair of the
two components, instantiated the coproduct component at the empty family
`PEmpty.elim`, instantiated the colimit component at an arbitrary empty
category `J` (with `[IsEmpty J]` and any Hom universe `t`), and reported the
three standard axioms for each of the three main theorems. The file contains
no proof holes and no new axioms. Compilation is development evidence;
acceptance requires independent review and validation.
