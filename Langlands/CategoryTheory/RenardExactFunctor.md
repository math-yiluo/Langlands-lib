# Renard A.VIII.1: additive functors and sequence exactness

Authors: Worker 595 (implementation and direct source checks), Worker 6
(mathematical specification and Mathlib reuse route).

This definition unit implements the sequence conditions in David Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, A.VIII.1, printed pages 265–266 / PDF pages 271–272.
Registered source: `renard-2026-representations-groupes-reductifs-padiques`.
The governing file is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Both pages were read directly; the arrows and contravariant convention on
PDF272 were also checked visually.

The [author's book page](https://perso.pages.math.cnrs.fr/users/david.renard/),
checked on 26 October 2026, links the corrected 2026 French edition and labels
the separate errata as belonging to the 2010 edition. Its retained snapshot is
registered as `renard-author-page-2026-10-26`. No separate 2026 errata link was
found in that book section, and no `notes/errata` directory was present in the
workspace or its Library base. These are bounded observations. The available
2010 errata, `renard-2010-corrections-complements`, were checked on PDF18–19,
including the correction on old printed page 308 from “faithful” to “exact”.
The governing 2026 text already uses “exact” in that argument. Those later
faithfulness arguments are outside this unit.

## Additivity is reused from Mathlib

At the start of printed page 266 the source explicitly assumes that functors
between abelian categories are additive throughout the discussion.
The Lean predicates therefore take `[F.Additive]`.
Mathlib's existing `CategoryTheory.Functor.Additive` expresses additivity of
the actual function `F.map` on each Hom group; no parallel class is introduced.
Its `Functor.mapAddHom` is the actual additive Hom map.

The following are the complete types of the reused additive interface, with
all implicit category and structure parameters displayed through the shared
binders. Here preadditivity suffices; our abelian hypotheses supply it.

```lean
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]

CategoryTheory.Functor.Additive (F : C ⥤ D) : Prop

CategoryTheory.Functor.mapAddHom
  (F : C ⥤ D) [F.Additive] {X Y : C} :
  (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)

CategoryTheory.Functor.coe_mapAddHom
  (F : C ⥤ D) [F.Additive] {X Y : C} :
  ⇑(F.mapAddHom : (X ⟶ Y) →+ (F.obj X ⟶ F.obj Y)) = F.map
```

The class field `Functor.Additive.map_add` asserts
`F.map (f + g) = F.map f + F.map g` for all parallel morphisms `f` and `g`.
An additive monoid homomorphism between these abelian groups is also an
abelian-group homomorphism. In particular, additivity gives preservation of
zero morphisms. Mathlib synthesizes `F.PreservesZeroMorphisms`, which makes
the actual short complex `S.map F` available. Its objects are
`F.obj S.X₁`, `F.obj S.X₂`, `F.obj S.X₃`; its arrows are definitionally
`F.map S.f` and `F.map S.g`. Its zero-composite proof uses `F.map_comp`,
`S.zero` and `F.map_zero`.

The reused declarations are in
`Mathlib/CategoryTheory/Preadditive/AdditiveFunctor.lean`;
`ShortComplex.map` is in
`Mathlib/Algebra/Homology/ShortComplex/Basic.lean`.
The inspected Mathlib commit is
`5ed2965256430c3649e86755f9576b54eca72435`.

## Covariant sequence conditions

The module is `Langlands.CategoryTheory.RenardExactFunctor`; all new
declarations lie in namespace `Langlands.Renard`.
The complete shared context of the covariant declarations is:

```lean
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive]
```

All four universes remain independent. The predicates range over arbitrary
abelian categories, without assumptions of smallness, concreteness, module
structure or a representation interpretation. Their types and defining
expressions in this context are:

```lean
def SequenceLeftExact (F : C ⥤ D) [F.Additive] : Prop :=
  ∀ S : ShortComplex C,
    S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f)

def SequenceRightExact (F : C ⥤ D) [F.Additive] : Prop :=
  ∀ S : ShortComplex C,
    S.Exact ∧ Epi S.g → (S.map F).Exact ∧ Epi (F.map S.g)

def SequenceExact (F : C ⥤ D) [F.Additive] : Prop :=
  SequenceLeftExact F ∧ SequenceRightExact F
```

The actual `ShortComplex C` contains the two composable morphisms and a proof
that their composite is zero. Mathlib's `S.Exact` is exactness at its middle
object. Adding `Mono S.f` describes the source's exact
`0 → X → Y → Z`, and adding `Epi S.g` describes its exact
`X → Y → Z → 0`. Left exactness imposes no epimorphism condition on the
last map; right exactness imposes no monomorphism condition on the first.
Neither input is restricted to `S.ShortExact`.
The predicates use the mapped complex and the actual mapped boundary arrows.

The only accompanying laws are definitional unfoldings, each proved by
`Iff.rfl`:

```lean
sequenceLeftExact_iff (F : C ⥤ D) [F.Additive] :
  SequenceLeftExact F ↔
    ∀ S : ShortComplex C,
      S.Exact ∧ Mono S.f → (S.map F).Exact ∧ Mono (F.map S.f)

sequenceRightExact_iff (F : C ⥤ D) [F.Additive] :
  SequenceRightExact F ↔
    ∀ S : ShortComplex C,
      S.Exact ∧ Epi S.g → (S.map F).Exact ∧ Epi (F.map S.g)

sequenceExact_iff (F : C ⥤ D) [F.Additive] :
  SequenceExact F ↔ SequenceLeftExact F ∧ SequenceRightExact F
```

These laws expose the definitions for subsequent statements; they prove no
preservation theorem.

## Contravariant convention

Renard explicitly interprets a contravariant functor from `C` to `D` as the
actual covariant functor `Cᵒᵖ ⥤ D` and transfers the same definitions.
Mathlib supplies the abelian structure on `Cᵒᵖ`.
Under the same category and abelian binders, the usable aliases are:

```lean
abbrev ContravariantSequenceLeftExact
  (F : Cᵒᵖ ⥤ D) [F.Additive] : Prop :=
  SequenceLeftExact F

abbrev ContravariantSequenceRightExact
  (F : Cᵒᵖ ⥤ D) [F.Additive] : Prop :=
  SequenceRightExact F

abbrev ContravariantSequenceExact
  (F : Cᵒᵖ ⥤ D) [F.Additive] : Prop :=
  SequenceExact F
```

Thus the first alias tests `S : ShortComplex Cᵒᵖ` with `S.Exact ∧ Mono S.f`;
the second tests `S.Exact ∧ Epi S.g`. The names are not swapped.
Reversing arrows to express these inputs in `C` is a separate translation,
not an implicit change in convention. These aliases are internal interface
packaging of the source's stated convention.

## Boundary with later theorem units

Mathlib's `CategoryTheory.leftExactFunctor`, `rightExactFunctor` and
`exactFunctor` use preservation of finite limits, finite colimits, or both.
The present definitions have precisely the source sequence conditions as
their defining expressions; they contain no limit-preservation assumptions.
No comparison with those Mathlib predicates is proved here.

For later proofs, the second entries of
`Functor.preservesFiniteLimits_tfae F` and
`Functor.preservesFiniteColimits_tfae F` in
`Mathlib/Algebra/Homology/ShortComplex/ExactFunctor.lean` are the respective
one-sided conditions used above. Their first entries use short exact
inputs, as do the convenient `preservesFiniteLimits_iff_forall_exact_map_and_mono`
and `preservesFiniteColimits_iff_forall_exact_map_and_epi` wrappers.
`Functor.exact_tfae F` is a further reuse route for the two-sided comparisons.
These are navigation leads for subsequent theorem units.

Preservation of limits, colimits, all exact complexes or homology, reflection
of zero morphisms, the faithfulness criteria and A.VIII.2 remain separate
obligations in the parent whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.
