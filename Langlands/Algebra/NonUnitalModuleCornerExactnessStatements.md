# Exactness statements for the actual corner functor

Worker 695 implements the proposition interfaces; Worker 6 supplied the
mathematical specification and source/dependency guidance.

This is a statement unit for the unnumbered exactness proposition of David
Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, I.3.1, printed page 19 / PDF page 25. It states two
closed propositions and proves neither of them. All declarations use the
published constructions, with no replacement functor or exactness certificate.

## Sources and provenance

The governing original is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The Chapter I conventions, printed pages 5–7 / PDF pages 11–13; I.3.1,
printed page 19 / PDF page 25; and A.VIII.1, printed pages 265–266 /
PDF pages 271–272, were read directly for this unit.

Renard allows nonunital rings and actions without a unit law, including when
the ambient ring has a unit. His general idempotent decomposition is additive.
In I.3.1 the ring is a complex idempotented algebra and the source category
consists of nondegenerate modules. The ambient arbitrary-ring assertion below
is an internal generalization of that proposition: the fixed-vector argument
uses only the original associative additive action and the idempotent.
The nondegenerate assertion is the underlying original-module specialization
of the source's functor. It does not construct the additional complex scalar
action or compare with a separately bundled complex-linear category. Those
comparisons remain obligations of the parent whole-book task.

The registered supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read at PDF pages 1–2. Its I.3.2 corrections concern later tensor injection
and simple-module quotient arguments; no I.3.1 exactness correction was found
on these pages. The author's [current book page](https://perso.pages.math.cnrs.fr/users/david.renard/),
retained as `renard-author-book-links-2026-10-31`, SHA256
`143092e92be11be1b9c5a03bfc1e9e4538edb45f9a67d5fc8cc474b7b6dcd580`,
was checked on 31 October 2026. Its book section links a corrected 2026 French edition and separately labels the errata for the
2010 edition; no separate 2026 errata link occurs in that book section.
No Renard entry in a project `notes/errata` directory was available at the
checked project and Library locations. These are bounded source checks.

## Closed ambient target

The complete unapplied interface is

```lean
Langlands.Algebra.NonUnitalModuleCornerExactnessStatement.{uA, uM} : Prop
```

Its definition binds all mathematical inputs internally:

```lean
∀ (A : Type uA) [NonUnitalRing A] (e : Idempotent A),
  letI := NonUnitalModuleCat.abelian.{uA, uM} A
  letI := Idempotent.Corner.ring e
  Langlands.Renard.SequenceExact (NonUnitalModuleCorner.functor.{uA, uM} e) ∧
    ∀ S : ShortComplex (NonUnitalModuleCat.{uA, uM} A),
      S.Exact → (S.map (NonUnitalModuleCorner.functor e)).Exact
```

The ambient category is precisely `NonUnitalModuleCat.{uA,uM} A` for the
specified original ring structure and actions. The selected abelian data are
exactly `NonUnitalModuleCat.abelian A`; its `toPreadditive` is definitionally
`NonUnitalModuleCat.preadditive A`, the original pointwise Hom group
structure. The target is the actual ordinary unital
`ModuleCat.{uM} (Idempotent.Corner e)`, with the named
`Idempotent.Corner.ring e` and Mathlib's standard module-category abelian
structure. The published functor already fixes the inherited fixed-part group
and the actual `NonUnitalModuleCorner.fixedPartModule e M` action in its
object constructor. No independently supplied action on the fixed carrier is
an input to this proposition.

There is no idempotentedness, nondegeneracy, nontriviality, unit-action,
commutativity, scalar-field or dimension assumption. The ring universe `uA`
and module-carrier universe `uM` are independent.

## Closed nondegenerate target

The complete unapplied interface is

```lean
Langlands.Algebra.NondegenerateModuleCornerExactnessStatement.{uA, uM} : Prop
```

Its definition is

```lean
∀ (A : Type uA) [NonUnitalRing A] (hA : IsIdempotented A) (e : Idempotent A),
  letI := NondegenerateModuleCat.abelian.{uA, uM} A hA
  letI := Idempotent.Corner.ring e
  Langlands.Renard.SequenceExact
      (NonUnitalModuleCorner.nondegenerateFunctor.{uA, uM} e) ∧
    ∀ S : ShortComplex (NondegenerateModuleCat.{uA, uM} A),
      S.Exact → (S.map (NonUnitalModuleCorner.nondegenerateFunctor e)).Exact
```

This uses the existing full subcategory of original nondegenerate modules.
The named abelian structure's `toPreadditive` is definitionally
`Preadditive.fullSubcategory (nondegenerateProperty A)`, retaining inherited
pointwise Hom addition. There is no caller-supplied abelian structure.
The target category and its structures are the same actual corner-module
data as above. The functor is definitionally

```lean
nondegenerateInclusion A ⋙ NonUnitalModuleCorner.functor e
```

and its value at `M` is `ModuleCat.of _ (FixedPart e M.obj)`; its map at `f`
has linear map exactly `restrict e f.hom`. The ambient functor similarly
sends `M` to `ModuleCat.of _ (FixedPart e M)` and `f` to the morphism with
linear map `restrict e f`. These are the published functors with their
original object and map structures. No exactness, preservation, adjunction,
splitting or preimage certificate is assumed by either principal target.

## Sequence meaning and checks

The imported `Langlands.Renard.SequenceExact F` is the conjunction of the
source's full one-sided sequence conditions. Its left component quantifies
over every `S` with `S.Exact ∧ Mono S.f` and requires
`(S.map F).Exact ∧ Mono (F.map S.f)`. Its right component quantifies over
every `S` with `S.Exact ∧ Epi S.g` and requires
`(S.map F).Exact ∧ Epi (F.map S.g)`. The published functors are additive
for the selected inherited Hom groups. These tests are not restricted to
short exact inputs. The additional conjunct explicitly preserves every
exact three-term complex, without either boundary assumption, as treated in
the I.3.1 proof.

The Lean examples check both complete closed interfaces, both unequal
universe pairs `(uA,uM) = (0,1)` and `(1,0)`, and exact definitional
unfoldings of both propositions to all three tests. They also check the
named abelian-to-preadditive equalities, the named corner ring and fixed-part
action in actual functor objects, actual morphism restrictions, and the
nondegenerate composite. The examples use the regular integer action and
its nondegenerate bundling, zero idempotents, and a trivial carrier with the
zero action in both categories. A separate nonzero integer carrier with
zero original action has bottom fixed part and is explicitly proved not
nondegenerate. Thus the ambient zero action is not silently identified
with a nondegenerate object. These interface facts prove no principal
exactness assertion.

## Source proof route and remaining scope

An original intertwiner preserves fixed vectors by its equation at `e`.
Given a fixed middle vector `x` in the kernel of the second map, exactness
of the original triple supplies a preimage `m`. Replace it by `e • m`.
Idempotence makes this preimage fixed, and intertwining together with
`e • x = x` gives the required image equation. Injectivity restricts to
fixed subgroups, while surjectivity uses the same projection of a chosen
preimage. This describes the source argument and the provenance of the
ambient generalization; it is a route for later proofs, not proof evidence
for either proposition in this unit. The existing additive splitting is
available infrastructure and is not an extra hypothesis.

The main exact-target proofs, complex coefficient-category comparisons,
I.3.2 constructions and results, the remainder of I.3.1, and completion of
the whole book remain separate obligations. Statement coverage here claims
only these two proposition interfaces.
