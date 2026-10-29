# Renard A.VIII.2: presentations by two coproducts of a generator

Authors: Worker 6 (source reading, statement design, Lean draft and
documentation), Worker 945 (independent source recheck, complete declaration
inspection and submission).

This is one statement unit in module
`Langlands.CategoryTheory.Renard.GeneratorPresentationStatements`, namespace
`Langlands.Renard`. It states a strengthened form of the final unnumbered
lemma in David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, A.VIII.2, printed page 267 / PDF page 273.
The Hom and exactness introduction is on printed page 266 / PDF page 272.
The complete extracted text of both pages and the rendered image of PDF
page 273 were read.

Registered governing source:
`renard-2026-representations-groupes-reductifs-padiques`, retained original
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The supplementary 2010-edition errata appendix entries were also reread:
`renard-2010-corrections-complements`, PDF pages 18–19, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.
They correct the preceding exactness, sufficiency direction and smallness
object name; those corrections are incorporated in the governing 2026
text. These inspected entries give no correction of the final presentation
argument. No project `notes/errata` directory was available in the inspected
workspace; that observation is limited to this checkout.

## Source and strengthened target

Within the cocomplete abelian context, the source assumes a small
progenerator `P` and ends its proof with an exact sequence

```text
coproduct_J P → coproduct_I P → M → 0.
```

This target retains that conclusion and the needed existence of
coproducts. It weakens the object hypothesis to the published generator
condition `HomGenerator P`. Thus it is an internal generalization of the
source lemma; it does not assert that the source states the stronger
hypothesis range. A small progenerator supplies the generator premise,
so the source case will follow after the relevant definitions and proofs
are available.

The source's proof indexes an evaluation map by elements of an arbitrary
categorical object `M`. Such an object is not equipped with elements in
the general setting here. A categorical proof can instead index evaluation
by all morphisms `P ⟶ M`, obtain an epimorphism from that coproduct, and
repeat evaluation for its actual kernel. Composing the second evaluation
map with the kernel inclusion gives the first map of the displayed row.
This route uses generation and coproducts, without projectivity or
smallness. It is proof navigation, not a proof supplied by this statement
unit. Mathlib's `CategoryTheory.isSeparator_iff_epi` in
`CategoryTheory/Generator/Basic.lean` describes the native categorical
evaluation criterion. The needed comparison with the published
integer-module Hom definition remains a proof obligation.

## Exact declaration and sizes

The complete statement is the following Prop-valued definition:

```lean
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]

def GeneratorPresentationStatement [HasCoproducts.{v} C] (P : C) : Prop :=
  HomGenerator P →
    ∀ M : C, ∃ (I J : Type v)
      (f : (∐ fun _ : J => P) ⟶ (∐ fun _ : I => P))
      (g : (∐ fun _ : I => P) ⟶ M)
      (h : f ≫ g = 0),
      (ShortComplex.mk f g h).Exact ∧ Epi g
```

The complete unapplied type of the constant, with universe parameters
`v, u`, is

```lean
{C : Type u} → [Category.{v, u} C] → [Abelian C] →
  [HasCoproducts.{v, v, u} C] → C → Prop
```

Here `HasCoproducts.{v, v, u} C` is Mathlib's `HasCoproducts.{v} C`: every
discrete coproduct indexed by a type in `Type v` exists in this category
with Hom universe `v` and object universe `u`. The body is exactly the
displayed implication; there are no further outer parameters or ambient
premises.

The object universe `u` and Hom universe `v` remain independent. Each index
type is in `Type v`, the size of `P ⟶ M` and of the Hom type into the kernel
in the proposed construction. An unrelated index universe would require
an additional resizing argument. `HasCoproducts.{v} C` explicitly supplies
all discrete coproducts at this size; source cocompleteness supplies these
in particular. No smallness of `C`, concreteness, Grothendieck hypothesis
or relation between `u` and `v` is assumed.

`∐` is Mathlib's actual chosen categorical coproduct, not an unspecified
object with a supplied presentation certificate. Both arrows and their
zero composite are existentially quantified. `ShortComplex.Exact` is
exactness at the middle object; in an abelian category it is equivalent
to the vanishing of the actual homology. The additional `Epi g` expresses
the terminal zero of the source row. The source has no initial zero, and
this target imposes no monicity of `f`.

## Published inputs and boundary

The imported `Langlands.CategoryTheory.Renard.HomObjectProperties` defines
`HomGenerator P` as faithfulness of the actual functor
`Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P : C ⥤ ModuleCat.{v} ℤ`.
Its carrier at `X` is `P ⟶ X`, and its map for `g : X ⟶ Y` sends `a` to
`a ≫ g`. Its integer-module structure is the canonical one on the additive
Hom group. The Hom construction is reused from Worker 734's published
`HomFunctors` pair; the object predicate is reused from the published pair
by Workers 6 and 595. Those pairs were read completely. The current unit
adds no alternative definition or global generator instance.

Native coproducts and exactness are imported from Mathlib
`CategoryTheory/Limits/Shapes/Products.lean` and
`Algebra/Homology/ShortComplex/Exact.lean`, at prepared commit
`5ed2965256430c3649e86755f9576b54eca72435`. The corresponding definitions and
the evaluation criterion were read in that prepared source tree.

This file supplies only the proposition to be proved. It contains no
presentation construction or proof, and no new axioms or proof holes.
Independent statement review and publication precede a separate exact
proof task. The smallness and finite-support characterization, finite-type
comparison, regular-module converse and equivalence with right modules
over `End P` remain separate obligations of the whole-book parent.
