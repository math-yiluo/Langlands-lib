# Renard A.III.2: Yoneda and representable presheaves

This pair states the core Yoneda theorem and its representation dictionary from
David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, Appendix A.III.2, printed pp.253–254 / one-based PDF259–260.
It declares propositions and supplies no proof of them.

The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The beginning of A.III.2 on PDF259 defines the presheaves `h_X` and the map
`φ ↦ h_φ`. PDF260 defines representation by a natural isomorphism, states the
equivalence with the full subcategory of representable presheaves, and proves
the evaluation and Hom bijections. These passages were read directly; the
formulas on PDF260 were also checked visually.

The supplementary older-edition source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked at one-based PDF18–19. Those pages correct formulas in the later
universal-property discussion: the representing arrow is evaluated at the
identity, and a subsequent factorization passes through the representing
transformation. The governing 2026 PDF260–261 already has these forms.
This bounded check supplies no correction to the core theorem stated here.

## Actual constructions and universe conventions

All declarations are in `Langlands.Renard.Yoneda`. They use the actual Mathlib
`CategoryTheory.uliftYoneda`, `Functor.RepresentableBy`,
`Functor.IsRepresentable`, `ObjectProperty.FullSubcategory` and its inclusion
`ObjectProperty.ι`. The imports construct those objects and their intrinsic
laws; this unit introduces no replacement category or new mathematical data.

The three levels `w`, `v` and `u` are independent. Each component quantifies
`C : Type u` and `[Category.{v} C]` internally. In the evaluation and dictionary
clauses, `F : Cᵒᵖ ⥤ Type w` has an arbitrary value universe, including one
smaller than the morphism universe. There is no smallness, shrinking,
nonemptiness, finiteness or additional category hypothesis.

The common comparison universe is `Type (max w v)`:

| Expression | Values and action |
| --- | --- |
| `uliftYoneda.{w}.obj X` | `ULift.{w} (Y ⟶ X)` at `op Y`; precomposition on morphisms |
| `uliftYoneda.{w}.map f` | At `op Z`, sends `ULift.up g` to `ULift.up (g ≫ f)` |
| `F ⋙ uliftFunctor.{v}` | `ULift.{v} (F.obj (op Y))` at `op Y`; lifted action of `F` |
| `F.RepresentableBy X` | Actual equivalences `(Y ⟶ X) ≃ F.obj (op Y)`, compatible with precomposition |
| `F.IsRepresentable` | Existence of an object `X` and `Nonempty (F.RepresentableBy X)` |

The explicit lifts are an internal universe formulation of the source's
set-valued functors. They preserve the underlying elements and maps. In
particular, the statements do not identify the value universe with the Hom
universe. `Nonempty` expresses existence of isomorphism or representation data
as a proposition.

## The four clauses

`EvaluationStatement` says that, for every `C`, `F` and `X`, an actual type
equivalence

```text
e : (uliftYoneda.{w}.obj X ⟶ F ⋙ uliftFunctor.{v}) ≃ F.obj (op X)
```

exists with both maps specified. Its forward map sends `θ` to
`(θ.app (op X) (ULift.up (𝟙 X))).down`. Its inverse sends `x` to the natural
transformation whose component at `op Y` sends `ULift.up f` to
`ULift.up (F.map f.op x)`, for every actual `f : Y ⟶ X`.
Thus this is the source's evaluation-at-identity bijection and construction
`x ↦ θ_x`, with the inverse laws contained in `Equiv`. Naturality is contained
in the actual natural-transformation type; the formulas concern every `x`,
object `Y` and morphism `f`.

`HomEquivalenceStatement` says that, for every `C`, `X` and `Y`, an actual
equivalence

```text
e : (X ⟶ Y) ≃ (uliftYoneda.{w}.obj X ⟶ uliftYoneda.{w}.obj Y)
```

exists. Its forward map is exactly `uliftYoneda.{w}.map`. Its inverse sends a
natural transformation `θ` to
`(θ.app (op X) (ULift.up (𝟙 X))).down`.
This states full faithfulness for the actual Yoneda functor and identifies
the particular bijection printed in the theorem, rather than merely giving
some bijection between the two types.

`RepresentationDictionaryStatement` says, for every `C`, `F` and `X`,

```text
Nonempty (F.RepresentableBy X) ↔
  Nonempty (uliftYoneda.{w}.obj X ≅ F ⋙ uliftFunctor.{v}).
```

Mathlib's representation data uses natural Hom equivalences with independent
universes. The right side is Renard's definition by a natural isomorphism,
after the explicit lifts. The clause records the exact dictionary needed to
use that data without changing the source definition. It assumes neither
representation nor a natural isomorphism.

`RepresentableEquivalenceStatement` sets

```text
P : ObjectProperty (Cᵒᵖ ⥤ Type (max w v)) := fun F => F.IsRepresentable
```

and asserts that an actual equivalence `e : C ≌ P.FullSubcategory` exists,
together with `Nonempty (e.functor ⋙ P.ι ≅ uliftYoneda.{w} (C := C))`.
The subcategory has all ambient natural transformations between its objects.
The last natural isomorphism retains the theorem's assertion that Yoneda
realizes the equivalence. Thus the conclusion is about the actual embedding,
not merely an abstract equivalence between two categories. Every presheaf
in this full subcategory has values in the common comparison universe; the
dictionary clause separately handles arbitrary value universes.

`YonedaStatements.{w,v,u}` is the closed conjunction of these four propositions
in the order just given: evaluation, Hom equivalence, representation dictionary,
full-subcategory equivalence. Every category, functor and object is quantified
inside the respective component. This order first states the bijection proved
in the source, then its Hom specialization, then relates the imported
representation data to the source definition before stating the equivalence.

## Provenance and proof boundary

The evaluation and Hom formulas, the definition of representation and the
full-subcategory equivalence come from the cited 2026 passages. The independent
universe lifts, the dictionary between two actual Mathlib formulations, the
explicit inclusion natural isomorphism, and the closed conjunction are derived
internal packaging. They add no hypothesis or replacement construction. The
dictionary is an obligation of this statement family, not an assumed result.

A future proof can use Mathlib's `uliftYonedaEquiv`, followed by `Equiv.ulift`,
for the evaluation clause; `ULiftYoneda.fullyFaithful` for the Hom clause;
`representableByUliftFunctorEquiv` and
`RepresentableBy.equivUliftYonedaIso` for the dictionary; and the actual
full-subcategory lift, full faithfulness and each representable object's
`uliftYonedaReprXIso` for the equivalence. These APIs have been source-inspected.
This paragraph describes a proposed route and is not proof evidence.

The exact-proof successor remains a separate task, gated on independent
statement acceptance and actual Library publication. The later A.III.2 remark
about left universal problems, the compatible-uniqueness corollary, A.III.3,
adjunctions, and all remaining whole-book obligations remain separate units.
