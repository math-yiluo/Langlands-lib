# Closure statement for nondegenerate original modules

Workers 6 and 691. Worker 6 authored the shared draft; Worker 691 checked
the original passages, categorical predicates and complete interfaces. This
unit states the closure proposition without proving it.

## Exact proposition

`Langlands.Algebra.NondegenerateModuleClosureStatement.{uA,uM}` is a closed
`Prop`. For every `A : Type uA` with `NonUnitalRing A`, assuming
`IsIdempotented A`, it asserts the conjunction

```lean
(nondegenerateProperty.{uA, uM} A).ContainsZero ∧
(nondegenerateProperty.{uA, uM} A).IsClosedUnderSubobjects ∧
(nondegenerateProperty.{uA, uM} A).IsClosedUnderQuotients ∧
(nondegenerateProperty.{uA, uM} A).IsClosedUnderFiniteProducts
```

The property is the published `IsNondegenerate A M`: every vector of the
specified original module is fixed by an actual idempotent of `A`.
It is a property of the published
`NonUnitalModuleCat.{uA,uM} A`, whose objects have carriers in `Type uM`
and whose morphisms are the original additive intertwiners.

The four Mathlib properties have the following meanings.

| Property | Required conclusion |
| --- | --- |
| `ContainsZero` | There exists an ambient zero object satisfying the actual nondegeneracy property. |
| `IsClosedUnderSubobjects` | For every original monomorphism `f : X ⟶ Y`, nondegeneracy of `Y` implies nondegeneracy of `X`. |
| `IsClosedUnderQuotients` | For every original epimorphism `f : X ⟶ Y`, nondegeneracy of `X` implies nondegeneracy of `Y`. |
| `IsClosedUnderFiniteProducts` | Every ambient limiting cone on a finite discrete diagram of nondegenerate objects has a nondegenerate vertex. |

These are conclusions of the closed proposition. No closure certificate,
abelian structure on the nondegenerate subcategory, chosen fixed idempotent,
unit-action law, field, commutativity, nontriviality, finite generation or
finite dimension is an input. The imported ambient abelian structure is
already proved for the unchanged original category; it is not an additional
assumption.

The acting-ring and carrier universes are independent. The complete unfolded
proposition is checked by definitional equality at arbitrary `uA,uM` and
at `(uA,uM)=(0,1)` and `(1,0)`. Mathlib defines
`IsClosedUnderFiniteProducts` using finite indices in `Type` and transports
the closure to finite index types in other universes. It includes the empty
diagram. Its conclusion concerns every limiting cone, rather than only one
selected coordinatewise presentation. The statement uses only published
definitions and does not import the separate concrete product construction.

## Source and provenance

The governing original is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant original passages were read:

- Printed pp.5–6/PDF11–12 allow rings without units and module actions without
  a unit law, including over rings which have a unit.
- I.1.2, printed p.7/PDF13, defines nondegenerate modules over an idempotented
  ring, defines their full subcategory, and asserts closure under submodules
  and quotients before claiming abelianness.
- A.VI.1, printed p.261/PDF267, lists zero objects and finite products among
  the abelian-category axioms, alongside the other axioms.

The subobject and quotient clauses express the corresponding I.1.2 assertions
in the published original category. The zero and finite-product clauses are
explicit internal obligations needed to justify the intended application of
an abelian-subcategory criterion. They are not attributed to a separately
numbered theorem in the book. The public source audit
`notes/renard/appendix-a-corrections.md` explains why the unrestricted
full-subcategory sentence in A.VI.1 omits needed hypotheses. This proposition
states those hypotheses for this particular full subcategory; it does not
assume or reproduce that defective criterion.

The supplementary registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF1–3 and PDF18–19, was checked. It concerns the earlier edition and does not
replace the governing 2026 original or supply a proof of this conjunction.

The implementation reuses the actual property, action and category from
`Langlands.Algebra.NonUnitalModule`, its proved ambient structure from
`Langlands.Algebra.NonUnitalModuleAmbientAbelianProof`, and Mathlib's
`CategoryTheory.ObjectProperty` predicates from `EpiMono`,
`ContainsZero` and `FiniteProducts`. This exact four-clause packaging is
internally derived infrastructure.

## Proof boundary

The Lean file defines and checks the proposition. It contains no proof of
its four conclusions. A proof successor must construct the certificates
for the existing property over the existing category, retaining independent
universes. The finite-product clause needs a common idempotent fixing the
finitely many coordinates; an infinite-product closure assertion is not
part of this statement.

The named abelian structure on `NondegenerateModuleCat`, compatibility with
its inherited pointwise Hom groups, exactness of its inclusion and of the
nondegenerate-part functor, adjunctions, concrete image/coimage comparisons
and the remaining book assertions stay separate obligations. This statement
does not claim any of them.
