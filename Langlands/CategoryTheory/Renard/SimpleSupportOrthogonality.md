# Renard A.IX: disjoint supports and canonical subobject maps

Author: Worker 827.

This module proves exactly the published proposition
`Langlands.Renard.SimpleSupportOrthogonalityStatement` from
`Langlands.CategoryTheory.Renard.SimpleSupportOrthogonalityStatements`,
for an arbitrary `C : Type u` with `[Category.{v} C]` and `[Abelian C]`
and independent universes `w`, `v`, `u`. The statement pair and every pair
it imports are used unchanged. No smallness, well-poweredness,
finite-length, finite-type, module or concrete-category hypothesis is
added, and no component's conclusion is assumed as a premise of another.

The exported constant has the complete unapplied type

```lean
Langlands.Renard.simpleSupportOrthogonality.{w, v, u} :
  (C : Type u) → [Category.{v} C] → [Abelian C] →
    Langlands.Renard.SimpleSupportOrthogonalityStatement.{w} C
```

and is the conjunction, in the statement's order, of

```lean
Langlands.Renard.simpleSupportHomOrthogonality.{w, v, u} C :
  SimpleSupportHomOrthogonalityStatement.{w} C
Langlands.Renard.simpleSupportSubobjectIntersection.{w, v, u} C :
  SimpleSupportSubobjectIntersectionStatement.{w} C
Langlands.Renard.simpleSupportSubobjectBiproductMono.{w, v, u} C :
  SimpleSupportSubobjectBiproductMonoStatement.{w} C
```

Each component keeps the antecedents `IsSourceGrothendieck.{w} C`,
`SourceAB6 C`, arbitrary `S T : Set (ObjectClass C)`, both conditions
`S ⊆ simpleClasses C` and `T ⊆ simpleClasses C`, and `Disjoint S T`.
The two subset conditions are not needed by the argument; they are
introduced and left unused. The conclusions are about the actual ambient
morphisms and zero morphism, the actual `Subobject X` infimum and bottom,
and `Mono` of the actual canonical map `biprod.desc P.arrow Q.arrow`.

## Source and provenance

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The complete A.IX page, printed 268 / PDF274, was read. For disjoint
`S, S' ⊂ Irr(M)` it states: if `E ∈ M_S` and `E' ∈ M_S'` then
`Hom_M(E, E') = {0}`; moreover `E_S ∩ E_S' = {0}` for every `E`, hence
`E_S ⊕ E_S' ⊂ E`. The source gives no proof. The A.VI.3 material on
printed 263–264 / PDF269–270 (the source Grothendieck context, AB6 as
local finite type, and the `JH` Lemma) was also read in full.

The Hom component is the source assertion. The intersection and
monicity components are internal generalizations: the source states them
for the full supported sums `E_S` and `E_S'`, while the Lean targets
cover any two actual subobjects `P, Q` of a common object whose
underlying objects are supported on `S` and `T`. This module does not
prove that `E_S` exists, is supported on `S` or is maximal, and so does
not prove the source's `E_S` specialization; that remains a separate
obligation. Monicity of `biprod.desc P.arrow Q.arrow` is the precise
meaning used for the source's inclusion `E_S ⊕ E_S' ⊂ E`.

The separate registered 2010-edition errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF18–19, were read. Their item for old page 310, lines 10–11 (replace
`M` by `E` and `M_S` by `E_S`) is already incorporated in the 2026
passage; they give no correction to the Hom assertion. This is a bounded
comparison; no claim is made that no other errata exist.

## Published dependencies

The proof imports by Lean name:

- `simpleSubquotientClasses_subset_of_mono` and
  `simpleSubquotientClasses_subset_of_epi` from
  `Langlands.CategoryTheory.Renard.SimpleSubquotientSubobjectQuotient`:
  the simple-subquotient classes of the source of a monomorphism lie in
  those of its target, and those of the target of an epimorphism lie in
  those of its source. Both hold in every abelian category.
- `simpleSubquotientEmpty` from
  `Langlands.CategoryTheory.Renard.SimpleSubquotientEmpty`, Renard A.VI.3
  Lemma (ii): in the source context, `simpleSubquotientClasses X = ∅`
  iff `IsZero X`. This is the only place where `IsSourceGrothendieck.{w} C`
  and `SourceAB6 C` are used.
- `HasSimpleSupport S X`, meaning `simpleSubquotientClasses X ⊆ S`, from
  `Langlands.CategoryTheory.Renard.SimpleSupport`.
- Mathlib's images (`image`, `factorThruImage`, `image.ι`, `image.fac`),
  `Subobject.inf_factors`, `Subobject.factors_comp_arrow`,
  `Subobject.bot_factors_iff_zero`, `Subobject.mk_eq_bot_iff_zero`,
  `biprod.desc_eq`, `biprod.hom_ext` and
  `Preadditive.mono_of_cancel_zero`.

## Implemented proof

`isZero_of_hasSimpleSupport_of_disjoint`. If `Z` is supported on both `S`
and `T`, its simple-subquotient classes lie in `S ∩ T`, which is empty by
`Disjoint S T`. Hence they are empty, and `simpleSubquotientEmpty` with
the two retained source antecedents gives `IsZero Z`.

`eq_zero_of_hasSimpleSupport_of_disjoint` (Hom component). Factor
`f : X ⟶ Y` through its actual image as
`factorThruImage f ≫ image.ι f`. The first map is an epimorphism and the
second a monomorphism, so the classes of `image f` lie in those of `X`,
hence in `S`, and in those of `Y`, hence in `T`. Thus `image f` is zero,
`factorThruImage f = 0`, and `f = 0`.

`inf_eq_bot_of_hasSimpleSupport_of_disjoint` (intersection component).
The actual inclusions `Subobject.ofLE (P ⊓ Q) P inf_le_left` and
`Subobject.ofLE (P ⊓ Q) Q inf_le_right` are monomorphisms, so the
underlying object of `P ⊓ Q` is supported on `S` and on `T`, hence zero.
Then its arrow is zero, and `Subobject.mk_eq_bot_iff_zero` applied to
`Subobject.mk (P ⊓ Q).arrow = P ⊓ Q` gives `P ⊓ Q = ⊥`.

`mono_biprod_desc_arrow_of_inf_eq_bot` (abelian-category criterion, no
source hypotheses). Let `P Q : Subobject X` with `P ⊓ Q = ⊥`, and let
`g : Z ⟶ (P : C) ⊞ (Q : C)` satisfy `g ≫ biprod.desc P.arrow Q.arrow = 0`.
By `biprod.desc_eq` this says
`(g ≫ biprod.fst) ≫ P.arrow + (g ≫ biprod.snd) ≫ Q.arrow = 0`, so the
morphism `a = (g ≫ biprod.fst) ≫ P.arrow` equals
`(-(g ≫ biprod.snd)) ≫ Q.arrow`. Thus `a` factors through both `P` and
`Q`, hence through `P ⊓ Q = ⊥`, so `a = 0`. Cancelling the monomorphisms
`P.arrow` and `Q.arrow` gives `g ≫ biprod.fst = 0` and
`g ≫ biprod.snd = 0`, so `g = 0` by `biprod.hom_ext`. By
`Preadditive.mono_of_cancel_zero` the canonical map is monic.

The three exported component theorems introduce the full antecedents of
their statements and apply these lemmas; the biproduct component applies
the criterion to the zero intersection just proved for the same `P` and
`Q`. `simpleSupportOrthogonality` is their conjunction. The route is the
one suggested in the statement's Markdown and the task context (image
factorization with mono/epi transport and zero detection; actual
monomorphisms for the intersection; a canonical-map criterion for the
biproduct).

## Checks and remaining obligations

The module was compiled in the approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with no errors or warnings, and
the declaration `Langlands.Renard.simpleSupportOrthogonality` was
inspected: it is a theorem with level parameters `w, v, u` whose axioms
are only `propext`, `Classical.choice` and `Quot.sound`. It uses no
`sorry`, `admit` or new axiom. Development compilation is not
acceptance; independent review, Lake build and exact-target validation
are separate.

Existence of the full indexed sums `E_S`, the source-size adapters, their
support and maximality, the `E_S` specialization of the last two
components, finite and colimit closure, splitting by a subset or
partition and the product decomposition are not addressed here and keep
their separate tasks and owners.
