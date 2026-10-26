# Existence of local module approximation systems (Stacks 00QX)

The declaration
`Langlands.Algebra.LocalModuleApproximationExistenceStatement.{uR,uS,uM} : Prop`
states Stacks Project, Lemma 10.127.13, tag
[00QX](https://stacks.math.columbia.edu/tag/00QX). This module defines the
proposition; its proof is a separate obligation.

The original is the registered source
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
in `00QL.html`, Lemma 10.127.13 (00QX), all six conditions and the proof.
The preceding Remark 10.127.12 (00QW) explains why the ring system must be
chosen with care. The ring construction is Lemma 10.127.11 (00QV), whose
statement, proof and comments are retained in `00QV.html`. Its corrected
polynomial quotient map and prime localizations are the source construction
underlying the intended proof. No separate source-specific errata note was
found in the current project or Library notes.

## Hypotheses and quantifiers

The proposition universally quantifies `R : Type uR`, `S : Type uS` and
`M : Type uM` in three independent universes. Both rings are commutative local
rings, `S` has an `R`-algebra structure, and its actual structure map
`algebraMap R S` is local. The carrier `M` has an additive commutative group
and an `S`-module structure.

The two substantive hypotheses are:

1. `EssFinitePresentation R S`, the published predicate for a localization of
   a finitely presented `R`-algebra;
2. `Module.FinitePresentation S M`, Mathlib's finite-presentation predicate
   for modules.

There is no nonzero hypothesis on `M`, no flatness or Noetherian hypothesis,
and no finite-presentation hypothesis on `R`.

The conclusion chooses a type `ι`, a preorder on it, nonemptiness and
directedness, then jointly chooses
`D : LocalAlgebraSystem ι R S` and `E : LocalModuleSystem D M`
with `E.IsApproximation`. A directed preorder expresses the directed-system
indexing; antisymmetry is unnecessary for these data or conditions.
All ring and module maps and their compatibility laws are stored in these
published structures.

In particular, the ring system is existentially chosen together with the
module system. The proposition does not quantify over every preselected
`D`. In the source proof, one first chooses a suitable ring approximation,
descends the finitely many entries of a presentation matrix for `M` to a
single component, and restricts to the directed tail above that component.
Remark 00QW warns that even a ring approximation with the earlier
finite-type properties need not have the required localization property.

## The six approximation conditions and actual maps

Write `Rᵢ = D.base i`, `Sᵢ = D.alg i`, and `Mᵢ = E.obj i`.
The conclusion reuses the unchanged published predicate
`LocalModuleSystem.IsApproximation`, whose clauses are:

1. `E.IsColimit`: the canonical ring maps from `Ring.DirectLimit D.base`
   to `R` and `Ring.DirectLimit D.alg` to `S` are bijective, and the
   canonical additive map from `AddCommGroup.DirectLimit E.obj` to `M` is
   bijective. These maps are `D.baseColimitMap`, `D.algebraColimitMap`
   and `E.moduleColimitMap`, formed from the given cocones. The semilinear
   module cocone respects scalar multiplication through `D.algι`.
2. Every `Rᵢ` is essentially of finite type over `ℤ`, expressed by
   `_root_.Algebra.EssFiniteType ℤ (D.base i)`.
3. Every `Sᵢ` is essentially of finite type over `Rᵢ`, expressed by
   `_root_.Algebra.EssFiniteType (D.base i) (D.alg i)`.
4. Every `Mᵢ` is finite over `Sᵢ`, expressed by
   `Module.Finite (D.alg i) (E.obj i)`. The statement retains the source's
   finite conclusion at each stage.
5. For every `h : i ≤ j`, `D.IsPrimeLocalization h` requires that the
   canonical ring map
   `Sᵢ ⊗[Rᵢ] Rⱼ →+* Sⱼ` presents `Sⱼ` as a localization at a prime
   of that actual tensor product. The map is `D.ringBaseChangeMap h`,
   sending `s ⊗ r` to
   `D.algMap i j h s * algebraMap (D.base j) (D.alg j) r`.
   The localization algebra structure is exactly
   `(D.ringBaseChangeMap h).toAlgebra`; no unrelated map is substituted.
6. For every `h : i ≤ j`, the canonical `Sⱼ`-linear map
   `E.moduleBaseChangeMap h` is bijective. Its actual domain is
   `Sⱼ ⊗[Sᵢ] Mᵢ`, with the scalar action induced by `D.algMap i j h`,
   and its formula is `s ⊗ m ↦ s • E.map i j h m`.

Clause 6 uses the published scalar-first tensor convention. The source
writes `Mᵢ ⊗[Sᵢ] Sⱼ`; tensor symmetry exchanges the factors and changes
the displayed formula to `m ⊗ s ↦ s • E.map i j h m`. Thus the
bijectivity requirement expresses the source's isomorphism condition.
The stored scalar-first map is linear over `Sⱼ`, so bijectivity also gives
an actual linear equivalence via `LinearEquiv.ofBijective`.

## Witness sizes and provenance of the packaging

Let `U = max uR uS uM`. The index lives in `Type U`, as do every
`Rᵢ`, `Sᵢ` and `Mᵢ`. Explicit universe arguments to the two structures
fix these four witness levels to `U`; the target rings and module retain
their original universes.

This is a size convention for the existence statement. Finite subsets,
polynomial quotients, localizations, finite matrices and their cokernels
can be constructed at these witness levels, and a directed-tail restriction
does not increase them. If a proof first constructs smaller witnesses, it
must transport their structures and maps to these levels and verify the
required properties. No such transport is assumed as a theorem here.
The statement imposes no equality of `uR`, `uS` and `uM` and does not demand
existence in every independently prescribed smaller witness universe.

The Lean structures, canonical maps, directed-preorder presentation and
universe packaging are internal formalization choices for the six source
clauses. This module imports the accepted
`Langlands.Algebra.LocalApproximationSystem` and
`Langlands.Algebra.EssFinitePresentation` definitions without modifying
either pair. It adds only this exact single-module existence proposition.
Compatible maps of module systems, synchronized towers and their proof
obligations are separate units.
