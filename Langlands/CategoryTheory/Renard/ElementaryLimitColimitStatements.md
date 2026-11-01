# Renard A.IV: elementary limits and colimits

Authors: Worker 709 (prepared Lean and Markdown pair) and Worker 695
(source and interface verification and submission).

This file specifies the first four examples in A.IV.1 and their four
explicitly named duals in A.IV.2. It contains statements only. It supplies
neither an existence theorem for limits in an arbitrary category nor a
proof of the eight characterizations.

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source locations are A.IV.1, examples 1–4, printed pp.256–257
(one-based PDF262–263), and the paragraph of A.IV.2 naming the corresponding
dual examples, printed p.257 (PDF263).

The supplementary older-edition corrections are registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.
PDF18–19 were checked. The PDF18 correction to old printed p.298 changes
“limit” to “colimit” in a later passage; it does not alter these first four
examples. This is a bounded check of the older errata, not a claim that
every assertion in A.IV has been reconciled.

The colimit factorization is read in the direction required by the
source's displayed `D → ΔX → ΔY`: the factor is `X → Y`. The adjacent
prose reverses both arrows. This correction was already diagnosed in
Worker 6's [Appendix A source audit](../../../notes/renard/appendix-a-corrections.md)
and documented in Worker 610's
[`ConeBridge` companion](ConeBridge.md). The present colimit examples use
the resulting outward factor maps, without imposing connectedness on
the index.

All declarations are in namespace
`Langlands.Renard.ElementaryLimitColimit`.

## Data and universes

Each component is a closed `Prop`-valued definition. Its category is an
arbitrary `C : Type uC` with `Category.{vC} C`. The index level `uI` is
independent of both `uC` and `vC`; no universe inequality or small-category
assumption is imposed.

The empty-diagram components quantify an arbitrary
`D : Discrete.{uI} PEmpty ⥤ C` and an actual cone or cocone over it, with
its vertex retained as `t.pt`. The product and coproduct components quantify
every `I : Type uI`, including empty and infinite index types. They use
Mathlib's actual `Fan.mk` and `Cofan.mk` for the discrete diagram
`Discrete.functor X`.

The kernel and cokernel components retain the source's zero-object
hypothesis `HasZeroObject C` and separately ask for `HasZeroMorphisms C`.
This is Mathlib's recommended packaging: a zero object supplies such
morphisms through `HasZeroObject.zeroMorphismsOfZeroObject`, while a
separately supplied instance can agree definitionally with the one
already used, for example in an additive category. It adds no
mathematical restriction to the source hypothesis. Any zero morphism
structure agrees with the composites through the zero object: if
`X → O → Y` passes through a zero object, its first arrow is the zero
arrow by uniqueness into `O`, and its composite is zero by the
zero-composition law. No preadditive or abelian hypothesis is used.

`KernelFork.ofι i h` is an actual cone over `parallelPair f 0`;
`CokernelCofork.ofπ p h` is its cocone counterpart. The hypotheses `h`
assert the required zero composite. They do not assert any universal
property. Likewise, `PullbackCone.mk p q h` is an actual cone over
`cospan f g`, and `PushoutCocone.mk p q h` is an actual cocone over
`span f g`. Their hypotheses `h` assert only that the indicated square
commutes.

`IsLimit` and `IsColimit` carry actual universal-witness data. `Nonempty`
on the left of each equivalence turns existence of those data into a
proposition. The right side quantifies every competing object and
compatible family and requires a unique actual categorical morphism.
In each occurrence of `∃!`, uniqueness is restricted to the displayed
factorization equations. In the empty cases `∃! f, True` simply means
that the relevant Hom type has exactly one element.

## The eight characterizations

1. `EmptyLimitStatement` states that a cone over the empty diagram is
   limiting if and only if for every `Y : C` there is a unique arrow
   `Y ⟶ t.pt`. Thus its vertex is terminal. In example 1 the source's
   last displayed `X → T` is read as `Y → T`, in agreement with the
   immediately preceding quantification over `Y` and the terminal
   universal property.

2. `KernelStatement` fixes `f : X ⟶ Y`, `i : K ⟶ X` and `i ≫ f = 0`.
   The corresponding kernel fork is limiting if and only if every
   `q : Z ⟶ X` with `q ≫ f = 0` has a unique factorization
   `l : Z ⟶ K` satisfying `l ≫ i = q`. This spells out the source's
   identification with the parallel-pair limit.

3. `ProductStatement` fixes an arbitrary indexed family `X : I → C`,
   a vertex `P` and projections `p i : P ⟶ X i`. The resulting fan is
   limiting if and only if every family `q i : Y ⟶ X i` has a unique
   map `l : Y ⟶ P` satisfying `l ≫ p i = q i` for every `i`. The
   source's binary case is included by taking a two-element index type;
   the statement also retains the source's arbitrary-family case.

4. `PullbackStatement` fixes `f : X ⟶ Z`, `g : Y ⟶ Z` and a
   commuting cone `p : P ⟶ X`, `q : P ⟶ Y`. It is limiting if and
   only if every `a : W ⟶ X`, `b : W ⟶ Y` with `a ≫ f = b ≫ g`
   has a unique map `l : W ⟶ P` satisfying both `l ≫ p = a` and
   `l ≫ q = b`.

5. `EmptyColimitStatement` states that a cocone over the empty diagram
   is colimiting if and only if for every `Y : C` there is a unique
   arrow `t.pt ⟶ Y`. Thus its vertex is initial.

6. `CokernelStatement` fixes `f : X ⟶ Y`, `p : Y ⟶ Q` and
   `f ≫ p = 0`. The corresponding cokernel cofork is colimiting if
   and only if every `q : Y ⟶ Z` with `f ≫ q = 0` has a unique
   map `l : Q ⟶ Z` satisfying `p ≫ l = q`.

7. `CoproductStatement` fixes an arbitrary family `X : I → C`, a
   vertex `P` and inclusions `p i : X i ⟶ P`. The resulting cofan
   is colimiting if and only if every family `q i : X i ⟶ Y` has a
   unique map `l : P ⟶ Y` satisfying `p i ≫ l = q i` for every `i`.

8. `PushoutStatement` fixes `f : X ⟶ Y`, `g : X ⟶ Z` and a
   commuting cocone `p : Y ⟶ P`, `q : Z ⟶ P`. It is colimiting if
   and only if every `a : Y ⟶ W`, `b : Z ⟶ W` with
   `f ≫ a = g ≫ b` has a unique map `l : P ⟶ W` satisfying both
   `p ≫ l = a` and `q ≫ l = b`.

`ElementaryLimitColimitStatements.{vC, uC, uI}` is exactly the conjunction
of these eight closed components in that order: the four A.IV.1 examples
followed by their four A.IV.2 duals.

## Provenance and remaining work

The identifications are source assertions. The explicit `iff` formulations
expand the source's limit/colimit universal properties on the displayed
shapes; the named Mathlib constructors, `Nonempty` wrappers, independent
universe parameters and closed conjunction are internal formal packaging.
No universal-witness conclusion occurs as an input assumption.

No proof of these propositions is supplied here. A later proof can use
the existing Mathlib empty-cone, kernel-fork, fan and pullback-cone
constructors and their duals to relate the explicit unique factorizations
to `IsLimit` and `IsColimit`. That is a possible implementation route,
not proof evidence.

The preceding general cone/cocone definitions, Hom comparison and
compatible uniqueness are covered separately by
`Langlands.CategoryTheory.Renard.ConeBridge`. The abelian binary
product/coproduct comparison in
`Langlands.CategoryTheory.RenardProductCoproduct` belongs to A.VI.2(7);
it does not supply these general shape characterizations.

This unit leaves A.IV.1 examples 5–6 (inverse systems and subobject
intersections), their direct-system and union duals, and the subsequent
concrete abelian-group product/direct-sum and filtered-colimit
constructions as separate obligations. It makes no assertion of
completion of A.IV or Appendix A.
