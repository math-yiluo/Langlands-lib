# Renard A.VII: proof that subobjects of semisimple objects are semisimple

Module: `Langlands.CategoryTheory.Renard.SemisimpleSubobject`.
The theorem `Langlands.Renard.semisimpleSubobject` proves the published
statement `Langlands.Renard.SemisimpleSubobjectStatement` from
`Langlands.CategoryTheory.Renard.SemisimpleSubobjectStatements`.

## Target

With independent universes `r, v, u`, the complete unapplied type of
`semisimpleSubobject` is
`∀ (C : Type u) [Category.{v} C] [Abelian C], SemisimpleSubobjectStatement.{r, v, u} C`,
where the statement's body is

```lean
IsSourceGrothendieck.{r} C → SourceAB6 C →
  ∀ (X : C) [Small.{r} (Subobject X)],
    IsSemisimpleObject X →
      ∀ (Y : C) (j : Y ⟶ X) [Mono j], IsSemisimpleObject Y
```

The statement pair and its imports are unchanged. No hypothesis is added.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques` (SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`),
Appendix A.VII, unnumbered corollary, printed265/PDF271:

> **Corollaire.** Un sous-objet d'un objet semi-simple est semi-simple.
>
> *Démonstration.* Supposons que E soit un sous-objet de ℰ avec ℰ
> semi-simple, et soit E′ un sous-objet de E. C'est aussi un sous-objet de
> ℰ, et donc il existe un sous-module ℱ de ℰ tel que ℰ = E′ ⊕ ℱ. Posons
> F = ℱ ∩ E. On a alors E = E′ ⊕ F.

The printed proof writes "sous-module" for the ambient complement. In the
abelian setting this reads as a subobject.

## Implemented proof

The proof uses the published A.VII equivalence
`Langlands.Renard.semisimplicityEquivalence` (module
`Langlands.CategoryTheory.Renard.SemisimplicityEquivalence`) at both `X`
and `Y`. That module also supplies the modular law for subobjects
(instance `subobjectIsModularLattice`) and the lemma
`complementedLattice_subobject`. Both are reused here, not reproved.

1. `small_subobject_of_mono`: for a monomorphism `j : Y ⟶ X` in any
   category, `Small.{r} (Subobject X)` gives `Small.{r} (Subobject Y)`.
   Composition with `j` is injective on subobjects (Mathlib's
   `Subobject.map_obj_injective j`), so `small_of_injective` applies. This
   makes the equivalence available at `Y` without a new smallness premise.
2. `complementedLattice_subobject_of_mono`: if `Subobject X` is a
   complemented lattice, so is `Subobject Y`. The lemma
   `complementedLattice_subobject (Subobject.mk j)` gives complementedness
   for the subobjects of the object underlying `Subobject.mk j`, through
   the order isomorphism with the interval below `Subobject.mk j` and the
   modular law. Mathlib's order isomorphism
   `Subobject.mapIsoToOrderIso (Subobject.underlyingIso j)` then transfers
   it to `Subobject Y`.
3. `everySubobjectHasComplement_of_mono`: the same transfer for the
   canonical complement predicate `EverySubobjectHasComplement`, through
   the published comparison `everySubobjectComplementedLattice` (module
   `Langlands.CategoryTheory.Renard.SubobjectComplementComparison`).
4. `semisimpleSubobject`: given the source hypotheses `hG`, `hAB6`, a
   semisimple `X` with `Small.{r} (Subobject X)` and a monomorphism
   `j : Y ⟶ X`, the equivalence at `X` turns semisimplicity into
   condition (ii) and then (iii), `EverySubobjectHasComplement X`. Step 3
   gives `EverySubobjectHasComplement Y`, and the equivalence at `Y`
   (available by step 1) turns it back into (ii) and then
   `IsSemisimpleObject Y`.

## Relation to the source

The source proof shows directly that every subobject `E′` of `E` has the
complement `ℱ ∩ E`. The Lean proof reaches the same conclusion through
lattice theory. In the modular lattice `Subobject X`, the interval below
`E = Subobject.mk j` is complemented when `Subobject X` is. For `E′ ≤ E`,
Mathlib's instance `IsModularLattice.complementedLattice_Iic` (through
`exists_inf_eq_and_sup_eq`) chooses a complement `ℱ` of `E′` in
`Subobject X` and uses `ℱ ⊓ E` as the complement of `E′` below `E`,
exactly the source's `F`. The source then uses condition (iii) of
the lemma at `E`; the Lean proof does the same with
`semisimplicityEquivalence` at `Y`. The smallness transfer of step 1 has
no counterpart in the source, which does not track universe sizes. All
cases are covered, including zero objects and the zero subobject.

## Checks and authorship

A development check in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, over Library commit
`f6b64ec108eed89ad46dff1d99192f40c4f29015` with the published equivalence
module, compiled the module with no errors or warnings. The theorem has
level parameters `r, v, u` and depends only on `propext`,
`Classical.choice` and `Quot.sound`. A private probe checked
`@semisimpleSubobject` against
`∀ (C : Type u) [Category.{v} C] [Abelian C], SemisimpleSubobjectStatement.{r, v, u} C`
at independent universes and at the separated instantiations `{0, 2, 1}`
and `{2, 1, 0}`. These checks are not acceptance or publication.

Worker 1073 wrote this proof pair. It reuses by import the published
module `Langlands.CategoryTheory.Renard.SemisimplicityEquivalence` (by
Workers 1069 and 6), including its modular-law instance and
`complementedLattice_subobject`.
