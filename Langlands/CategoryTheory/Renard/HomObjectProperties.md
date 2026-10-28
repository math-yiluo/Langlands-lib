# Renard A.VIII.2: projective, injective and generator objects

Authors: Worker 6 (original shared draft, implementation and documentation),
Worker 595 (direct source checks, declaration inspection and submission).

This definition unit covers the five object properties in David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, A.VIII.2, printed page 267 / PDF page 273. The preceding Hom
functors and exactness convention occur in A.VIII.1–2, printed page 266 /
PDF page 272. The original extracts for both pages were read in full.
Registered source: `renard-2026-representations-groupes-reductifs-padiques`.
The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The available 2010-edition errata,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were reread on PDF pages 18–19. Their appendix entries correct an old argument
from “faithful” to “exact”, the direction of the nonzero-Hom criterion argument,
and the object name in the definition of smallness. They do not alter these
five object-property definitions. The governing 2026 text already incorporates
those corrections. No Renard entry was found in the inspected Library's project
errata notes; this is a bounded observation.

## Actual functors and source exactness

The module is `Langlands.CategoryTheory.Renard.HomObjectProperties`.
All its declarations are in namespace `Langlands.Renard`, with the common
complete binders

```lean
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
```

The object universe `u` and Hom universe `v` are independent. There are no
smallness, cocompleteness, Grothendieck, concreteness, finiteness, or module
category assumptions on `C`.

The imported module `Langlands.CategoryTheory.Renard.HomFunctors` supplies
the actual functors in namespace `Langlands.CategoryTheory.Renard`:

```lean
preadditiveCoyonedaInt (P : C) : C ⥤ ModuleCat.{v} ℤ
preadditiveYonedaInt (P : C) : Cᵒᵖ ⥤ ModuleCat.{v} ℤ
```

Their carriers are respectively `P ⟶ X` and `X ⟶ P`. For `g : X ⟶ Y`,
the covariant map sends `f : P ⟶ X` to `f ≫ g`; the contravariant map on
`g.op` sends `h : Y ⟶ P` to `g ≫ h`. Their restricted integer actions are
the canonical actions on those additive Hom groups. Both functors are
additive. These constructions and intrinsic laws are imported from their
published pair, authored by Worker 734, rather than reconstructed here.
The target carriers have universe `v`, with no comparison between `u` and `v`.
`Mathlib.Algebra.Category.ModuleCat.Abelian` supplies the abelian target.

The imported module `Langlands.CategoryTheory.RenardExactFunctor`, authored
by Worker 595 with Worker 6's specification, supplies the source conditions.
For an additive functor `F : A ⥤ B` between abelian categories, left sequence
exactness means

```lean
∀ S : ShortComplex A,
  S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f)
```

Right sequence exactness uses `S.Exact ∧ Epi S.g` and requires
`(S.map F).Exact ∧ Epi (F.map S.g)`. `SequenceExact F` is their conjunction.
These are the actual mapped short complex and arrows. The input to either
one-sided condition is not restricted to a short exact sequence.

For `F : Cᵒᵖ ⥤ B`, the source transfers the same covariant definitions to
the opposite category. The published alias `ContravariantSequenceExact F`
is `SequenceExact F`. The injective condition below follows that convention
on the actual contravariant functor, without interchanging the names of
the one-sided conditions.

## Five source definitions

With the common binders above, the exact declaration types and bodies are:

```lean
def HomProjective (P : C) : Prop :=
  SequenceExact (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P)

def HomInjective (P : C) : Prop :=
  ContravariantSequenceExact
    (Langlands.CategoryTheory.Renard.preadditiveYonedaInt P)

def HomGenerator (P : C) : Prop :=
  (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P).Faithful

def HomCogenerator (P : C) : Prop :=
  (Langlands.CategoryTheory.Renard.preadditiveYonedaInt P).Faithful

def HomProgenerator (P : C) : Prop :=
  HomProjective P ∧ HomGenerator P
```

Renard defines projective and injective objects by exactness of these two
Hom functors, generator and cogenerator objects by their faithfulness, and
a progenerator as a projective generator. These five definitions follow
that wording directly.

`Functor.Faithful` is Mathlib's proposition that the functor's map is
injective on every Hom type. For example, for generation it compares the
actual linear maps induced by two parallel morphisms `X ⟶ Y`.
It is not defined as a test on nonzero objects. Cogeneration applies the
same faithfulness condition to the actual functor on `Cᵒᵖ`.

The predicates are ordinary proposition definitions. They do not install
global instances for any Mathlib projectivity or generator notions.

## Definitional laws and boundary

The five accompanying theorems, in the same full common context, are

```lean
homProjective_iff (P : C) :
  HomProjective P ↔
    SequenceExact (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P)

homInjective_iff (P : C) :
  HomInjective P ↔
    ContravariantSequenceExact
      (Langlands.CategoryTheory.Renard.preadditiveYonedaInt P)

homGenerator_iff (P : C) :
  HomGenerator P ↔
    (Langlands.CategoryTheory.Renard.preadditiveCoyonedaInt P).Faithful

homCogenerator_iff (P : C) :
  HomCogenerator P ↔
    (Langlands.CategoryTheory.Renard.preadditiveYonedaInt P).Faithful

homProgenerator_iff (P : C) :
  HomProgenerator P ↔ HomProjective P ∧ HomGenerator P
```

Each proof is exactly `Iff.rfl`, exposing a definition for subsequent use.
They assert no preservation or comparison theorem.

Hom left exactness, comparison with Mathlib `Projective`, `Injective`,
`IsSeparator` and `IsCoseparator`, and the nonzero-Hom criterion for a
projective object to be a progenerator remain theorem obligations.
Smallness and preservation of coproducts, the finite-support characterization,
the finite-type comparison in Grothendieck categories, presentations by
coproducts of the progenerator, and the module-category equivalence remain
separate construction or theorem obligations. These boundaries preserve the
rest of A.VIII.2 under the whole-book parent task.
