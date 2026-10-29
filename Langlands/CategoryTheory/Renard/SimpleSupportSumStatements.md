# Renard A.IX: support and maximality of the supported sum

Authors: Worker 6 (revision-1 draft, whose structure and source audit are
reused here) and Worker 985 (revision-2 statements and this text).

This statement unit specifies two things about Renard's actual supported-subobject
sum `E_S`: it belongs to `M_S`, and it is the greatest supported subobject of `E`.
The public construction is used unchanged. The first assertion is in
David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, A.IX, printed page 268 / PDF274. The greatest-element
formulation is an internal consequence target, not a separately printed
theorem. All three declarations are transparent definitions returning `Prop`.
This pair proves none of them.

The module is
`Langlands.CategoryTheory.Renard.SimpleSupportSumStatements`, namespace
`Langlands.Renard`. It imports the unchanged public modules
`Langlands.CategoryTheory.Renard.SimpleSupportSum`,
`Langlands.CategoryTheory.RenardGrothendieckAxioms` and
`Langlands.CategoryTheory.Renard.LocallyFiniteType` by Lean name. It also
imports Mathlib's `Mathlib.CategoryTheory.Limits.EssentiallySmall` for
`hasCoproductsOfShape_of_small`.

## Original source and bounded errata check

The governing source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The hash was recomputed. Original PDF269–270 and PDF273–275 were read in
full, and PDF274 was also inspected visually.

PDF274 opens A.IX with "Soit M une catégorie de Grothendieck (AB4∗ et AB5)
vérifiant aussi AB6". Renard then takes a subset `S` of `Irr(M)` and defines
`M_S` as the full subcategory of objects all of whose irreducible
subquotients lie in `S`. He continues: "Pour tout objet E de M, on note E_S la
somme de tous les sous-objets de E qui sont dans M_S. Alors il est clair que
E_S ∈ M_S." The support statement below is exactly this last assertion. A.VI.2
on PDF269 defines the source Grothendieck convention, and A.VI.3 on
PDF269–270 defines AB6, `Irr` and `JH`. PDF270 also states the
arbitrary-sum `JH` identity, which gives one possible route to the support
assertion. That identity is not assumed here.

No dedicated
`notes/errata/renard-2026-representations-groupes-reductifs-padiques.md` was
found in the workspace, the project notes or the admitted Library notes.
The complete public `notes/renard/appendix-a-corrections.md` was read; its
findings concern other passages. The supplementary registered
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF18–19 and its hash recomputed. Its correction for old page
310, lines 10–11, replaces the letters `M, M_S` by `E, E_S` in the sum
passage. The governing 2026 text already uses `E, E_S`. This observation is
limited to those two pages of the supplementary correction list.

The complete imported Lean/Markdown pairs were read, together with the public
`SimpleSupport` pair, which supplies the support predicate and the set of
supported subobjects.

## Complete binders

Each declaration takes `(C : Type u) [Category.{v} C] [Abelian C]`, with
independent object and Hom universes `u` and `v`, and has a third universe
parameter `w`, the family size of the source Grothendieck hypothesis. The
module declares `universe w u v`, so the parameter order is `.{w, u, v}`. All
three declarations are marked `@[pp_with_univ]`, which makes `w` visible
whenever they are printed. Each component proposition quantifies over:

1. `hG : IsSourceGrothendieck.{w} C`;
2. the separate source assumption `SourceAB6 C`;
3. `S : Set (ObjectClass C)` with `S ⊆ simpleClasses C`;
4. every `X : C`, together with an instance argument
   `[Small.{w} (simpleSupportSubobjects S X)]`.

Two local instances are installed inside the proposition. Immediately after
`hG`, `letI : HasCoproducts.{w} C := hG.1`. After the smallness binder,

```lean
letI : HasCoproductsOfShape (simpleSupportSubobjects S X) C :=
  hasCoproductsOfShape_of_small.{w} C (simpleSupportSubobjects S X)
```

Neither is an extra external hypothesis. The second is Mathlib's construction of
coproducts of a `w`-small shape from `w`-indexed coproducts: it takes the
coproduct over `Shrink.{w}` of the index type and transports it along the
equivalence. It supplies the instance
`HasCoproduct fun P : simpleSupportSubobjects S X => ((P : Subobject X) : C)`
used by `simpleSupportSum S X`. These instances carry only existence data
derived from `hG` and the smallness binder. They contain no support,
maximality or Jordan–Hölder certificate.

By the public definitions, `IsSourceGrothendieck.{w} C` unfolds to
`HasCoproducts.{w} C ∧ DirectedSubobjectSumsDistribute.{w} C`, that is, the
source AB4∗ (coproducts) and AB5 (intersection distributes over sums of
nonempty directed families of subobjects) at the same family size `w`. No
generator or separator is part of it. `SourceAB6 C` is the canonical
condition that the full set of finite-type subobjects of each object has top
as least upper bound. It includes neither the Grothendieck hypothesis nor a
chosen covering family of smaller size.

## Universe and smallness choices

**Why the family size is not `max u v`.** Mathlib's `Subobject X`, and hence
the full subtype `↥(simpleSupportSubobjects S X)`, lies in
`Type (max u v)`. An earlier specification (task revision 1) therefore
assumed `IsSourceGrothendieck.{max u v} C`. That hypothesis is degenerate.
Its first conjunct gives coproducts indexed by
`md := Σ Z W : C, (Z ⟶ W)`, a type in `Type (max u v)`. Given two maps
`r ≠ s : X ⟶ Y`, each set `A` of elements of `md` yields the morphism
`Sigma.desc (fun k => if k ∈ A then r else s)` from `∐ (fun _ : md => X)`
to `Y`, which is itself an element of `md`. Distinct sets give distinct
morphisms, which contradicts Cantor's theorem. So every Hom type is a
subsingleton; in an abelian category every object is then zero, and the old
aggregate held for every abelian `C`. This is the classical size obstruction, dual to
Freyd's theorem that a small complete category is a preorder. A private
diagnostic (`7e64f479-e96e-4120-bd1d-149162543392`) machine-checked, with the
standard axioms only, that the revision-1 `SimpleSupportSumStatement C` is
provable for every abelian `C`. The same argument applies to any `w` that is at
least `max u v`; such instantiations of the present statements are again
vacuous. The intended instantiations are large categories with small Hom
types, such as `ModuleCat.{v} R` (objects in `Type (v+1)`, Homs in `Type v`)
with `w = v`.

**The smallness binder.** Renard's `E_S` is "la somme de tous les sous-objets
de E qui sont dans M_S", and sums in his AB4∗/AB5 conventions are indexed by
sets. The source therefore presupposes that the supported subobjects of `E`
form a set. The instance binder `Small.{w} (simpleSupportSubobjects S X)`
records exactly this presupposition for the one family that is summed, and
nothing more. It does not shrink the subobject type or replace the
indexing family. The sum is still the public `simpleSupportSum S X`, indexed
by the full subtype. The coproduct is derived from `hG.1`, not assumed
separately. The AB5 law `hG.2` concerns `w`-indexed families. It applies to this
same family after reindexing by `Shrink.{w}`, so the source hypotheses are
used at a size that actually matches the family. No `WellPowered`,
`LocallySmall`, concreteness, finite length, generator or separator is
assumed, and no universes are identified. In `ModuleCat.{0} ℤ`, instance
search finds `HasCoproducts.{0}` and the smallness binder for every `S` and
`X`, through Mathlib's well-poweredness of module categories. There the
statement specializes to the source hypotheses alone. The object
`ModuleCat.of ℤ ℤ` is not zero. These facts were checked in the diagnostic
recorded below.

## Statements and expanded meaning

The complete bodies are:

```lean
@[pp_with_univ]
def SimpleSupportSumSupportStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ hG : IsSourceGrothendieck.{w} C,
    letI : HasCoproducts.{w} C := hG.1
    SourceAB6 C → ∀ S : Set (ObjectClass C), S ⊆ simpleClasses C →
      ∀ (X : C) [Small.{w} (simpleSupportSubobjects S X)],
        letI : HasCoproductsOfShape (simpleSupportSubobjects S X) C :=
          hasCoproductsOfShape_of_small.{w} C (simpleSupportSubobjects S X)
        HasSimpleSupport S (simpleSupportSum S X : C)

@[pp_with_univ]
def SimpleSupportSumMaximumStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ hG : IsSourceGrothendieck.{w} C,
    letI : HasCoproducts.{w} C := hG.1
    SourceAB6 C → ∀ S : Set (ObjectClass C), S ⊆ simpleClasses C →
      ∀ (X : C) [Small.{w} (simpleSupportSubobjects S X)],
        letI : HasCoproductsOfShape (simpleSupportSubobjects S X) C :=
          hasCoproductsOfShape_of_small.{w} C (simpleSupportSubobjects S X)
        IsGreatest (simpleSupportSubobjects S X) (simpleSupportSum S X)

@[pp_with_univ]
def SimpleSupportSumStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  SimpleSupportSumSupportStatement.{w} C ∧ SimpleSupportSumMaximumStatement.{w} C
```

`ObjectClass C` is the quotient of actual objects by actual isomorphism, and
`simpleClasses C` is the public `Irr(C)`. The public
`simpleSubquotientClasses Y` is `JH(Y)`, formed from all actual simple
subquotients, including when `Y` has infinite length. Its witnesses are
`A B : Subobject Y`, `h : A ≤ B`, and simplicity of
`cokernel (Subobject.ofLE A B h)`, whose object class is the member of `JH(Y)`.

`simpleSupportSubobjects S X` is the set of actual subobjects `P` with
`HasSimpleSupport S (P : C)`. The actual `simpleSupportSum S X` is the image
subobject of the map to `X` from the coproduct of the underlying objects of
these subobjects; its leg at `P` is the inclusion `P.arrow`. It is Renard's
`E_S`, and `X` corresponds to his `E`. In the support target,
`(simpleSupportSum S X : C)` is the underlying object of that subobject.

The support conclusion expands to
`simpleSubquotientClasses (simpleSupportSum S X : C) ⊆ S`: every actual
simple subquotient of the underlying sum has class in `S`. Equivalently,
every simple cokernel of nested subobjects of that underlying object has class
in `S`.

The maximum conclusion expands to two parts:

- membership: `simpleSupportSum S X ∈ simpleSupportSubobjects S X`;
- upper bound: `∀ P ∈ simpleSupportSubobjects S X, P ≤ simpleSupportSum S X`.

The order is the existing categorical subobject order, in which an inclusion
factors through the larger subobject. The membership conjunct is exactly the
support conclusion. The upper-bound conjunct is already the public law
`le_simpleSupportSum`. So a proof of support gives the maximum assertion by
pairing these two facts. This is the internal provenance of the maximum
target; no proof of that implication is submitted here.

The public `isLUB_simpleSupportSum` only proves that the sum is the least
common upper bound. On its own it gives no membership in the supported set,
so it proves neither new component.

## Development checks

Diagnostic `e711db41-0d8a-4d94-b277-4ea2fba86160` compiled the module with
no errors or warnings in the prepared Lean environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, together with a separate private probe
module. The probe:

- printed all three complete unapplied declaration types and bodies, with
  universes. Each has universe parameters `{w, u, v}` and type
  `(C : Type u) → [Category.{v, u} C] → [Abelian.{v, u} C] → Prop`;
- checked all three complete body equalities by `rfl` against the bodies
  displayed above, including both local instances;
- checked that `IsSourceGrothendieck.{w} C` is definitionally
  `HasCoproducts.{w} C ∧ DirectedSubobjectSumsDistribute.{w} C`;
- reported only the standard axioms `propext`, `Classical.choice` and
  `Quot.sound` for all three declarations;
- reproved, with the same axioms, that `HasCoproducts.{max u v} C` makes every
  Hom type a subsingleton;
- carried out the `ModuleCat.{0} ℤ` checks described above.

A further workspace check, diagnostic
`c040483d-78e8-4ff7-8b82-ca366dd1a987`, inspected the aggregate
`SimpleSupportSumStatement` on its own. It reported a definition returning
`Prop`, level parameters `w, u, v`, and the same three standard axioms.

The probe is excluded from the submitted pair. These checks verify elaboration
and the intended specification. They do not show that the propositions are
true, and they do not constitute independent acceptance.

## Scope and remaining proof gate

Each component states the source assumptions, the restriction `S ⊆ Irr(C)`
and the set-size presupposition explicitly. No support, maximum property,
arbitrary-sum closure or `JH` identity is a premise. Accepting these
definitions accepts only their specification. After statement publication, a
separate proof unit must establish the exact public `SimpleSupportSumStatement`,
with independent semantic review and the required build and exact-target
checks. One expected route uses `hG.2` at the size `w`. Supported subobjects
are closed under binary sums, so the family is directed. AB5 on the
`Shrink`-reindexed family then writes each subobject `B` of `E_S` as the sum
of its intersections with supported subobjects. A simple quotient `B / A` is
therefore isomorphic to a subquotient of a single supported subobject. This
route is only a plan and has not been checked here.

The whole-book program separately retains subobject, quotient, extension
and colimit closure and abelianness of `M_S`; the `JH` identities and zero
detection; Hom orthogonality and disjoint intersections; splitting by a
subset or partition, subquotient splitting and the categorical product
equivalence. This unit neither assumes nor establishes any of them.
