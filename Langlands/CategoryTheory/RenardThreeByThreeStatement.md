# Renard's three-by-three bottom-row construction

Authors: Worker 691 and Worker 6. Worker 6 supplied the precise existential
target and initial source audit; Worker 691 independently checked the original
passage and authored this Lean/Markdown pair. This unit states A.VI.2(8).
Its proof remains a separate obligation.

## Original and reading boundary

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, Appendix A.VI.2(8), printed page 262 / PDF page 268.
Registered source ID:
`renard-2026-representations-groupes-reductifs-padiques`; SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF pages 267–268 were read directly and PDF268 was rendered and visually
inspected. The diagram has no horizontal arrows between its three bottom
objects. The following sentence asserts that one can add these arrows,
making the first a monomorphism and the second an epimorphism, preserving
commutativity and obtaining a short exact bottom row.

The preceding A.VI.1 at printed page 261 / PDF267 uses AB0, AB1, AB1*,
AB2, AB2*, AB3 and AB3*: a zero object, finite products and coproducts,
kernels and cokernels, and normality of every monomorphism and epimorphism.
Here the ambient category has Mathlib's actual `Abelian` structure.
The separate seven-axiom construction in
`Langlands.CategoryTheory.RenardAbelian` connects these conventions.
This statement does not duplicate that construction.

The registered author-page snapshot `renard-author-page-2026-10-26`
labels the separate errata as applying to the 2010 edition and links the
corrected 2026 French version. Its books section has no separate 2026
errata link. The appendix portion PDF18–19 of registered
`renard-2010-corrections-complements` was read directly; it contains no
correction to the three-by-three assertion. This is a check of those
pages, with the 2026 French edition governing this statement.

## Diagram and declaration

The only target is
`Langlands.CategoryTheory.RenardThreeByThreeBottomRowStatement`
in module `Langlands.CategoryTheory.RenardThreeByThreeStatement`.
It is a transparent `def` returning `Prop`, parameterized by
`C : Type u`, `[Category.{v} C]` and `[Abelian C]`, with independent
object universe `u` and morphism universe `v`.

The correspondence with the original diagram is:

| Original | Lean data |
| --- | --- |
| `A → A′ → A″` | `S₁ : ShortComplex C` |
| `B → B′ → B″` | `S₂ : ShortComplex C` |
| `A → B`, `A′ → B′`, `A″ → B″` | `τ.τ₁`, `τ.τ₂`, `τ.τ₃` for `τ : S₁ ⟶ S₂` |
| `C`, `C′`, `C″` in the diagram | The given objects `Z₁`, `Z₂`, `Z₃` |
| `B → C`, `B′ → C′`, `B″ → C″` | The given maps `p₁`, `p₂`, `p₃` |
| Missing `C → C′` and `C′ → C″` | Existentially quantified maps `a` and `b` |

The ambient category's Lean name `C` is distinct from the original diagram's
object named `C`, which is represented by `Z₁`.
`τ.comm₁₂` and `τ.comm₂₃` encode precisely the two upper commutative squares.
Each `ShortComplex` already includes the zero composite of its two arrows.
The additional witnesses `wᵢ : τ.τᵢ ≫ pᵢ = 0` form the three vertical
short complexes on the given bottom objects.

After universally quantifying over this data, the definition assumes
`S₁.ShortExact`, `S₂.ShortExact` and
`(ShortComplex.mk τ.τᵢ pᵢ wᵢ).ShortExact` for each of the three columns.
Mathlib's `ShortComplex.ShortExact` consists of exactness in the middle,
monicity of the first arrow and epicity of the second arrow.
In an abelian category these last two conditions express exactness at the
ends after adjoining zero objects. Thus the five short-exact hypotheses
encode exactly the two displayed rows and three displayed columns with
their endpoint zeros; no additional endpoint assumptions are omitted.

The conclusion is exactly

```lean
∃ (a : Z₁ ⟶ Z₂) (b : Z₂ ⟶ Z₃) (w : a ≫ b = 0),
  p₁ ≫ a = S₂.f ≫ p₂ ∧
  p₂ ≫ b = S₂.g ≫ p₃ ∧
  (ShortComplex.mk a b w).ShortExact
```

The first two conjuncts supply the two new commutative squares. The witness
`w` makes the new row a short complex, and its `ShortExact` condition
supplies the asserted monomorphism, epimorphism and exactness.
Both missing arrows are outputs. The bottom objects and all three quotient
maps remain arbitrary given data satisfying the three short-exact hypotheses.
There is no restriction to selected cokernel objects.

## Scope

This file imports Mathlib's short exact complex interface and states the
source assertion. It adds no axiom and assumes no bottom row or conclusion.
It places no module, embedding, smallness, finite-length or splitting
hypothesis on the diagram. It does not add uniqueness to the source target.
The proof, the other A.VI.2 assertions, and the later AB4–AB6 conventions
remain separate obligations.
