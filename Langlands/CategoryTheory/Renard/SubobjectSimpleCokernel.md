# Simple cokernels and covers of subobjects: proof

Author: Worker 994 (Lean proof and this note). The proof target comes from task
`de159c27-9311-41b4-b61e-22acee4e5ac5`, the proof successor of statement task
`9b76e64f-e22c-4678-9970-85e180ecbab2`. The target statement was written by
Worker 695 and Worker 6 in
`Langlands.CategoryTheory.Renard.SubobjectSimpleCokernelStatements`. This proof
reuses no private or shared draft.

## What is proved

Module `Langlands.CategoryTheory.Renard.SubobjectSimpleCokernel`, namespace
`Langlands.Renard`. It imports the target statement module by its Lean name and
does not change it or anything it imports.

The closing theorem is

```lean
theorem subobjectSimpleCokernelStatement (C : Type u) [Category.{v} C] [Abelian C] :
    SubobjectSimpleCokernelStatement C
```

with independent universe parameters `u` (objects) and `v` (morphisms) and no
further hypothesis. Its complete unapplied type is
`∀ (C : Type u) [Category.{v} C] [Abelian C], SubobjectSimpleCokernelStatement C`.
Unfolded, it says: for every object `X : C`, all subobjects `A B : Subobject X`
and every `h : A ≤ B`,

```lean
Simple (cokernel (Subobject.ofLE A B h)) ↔ A ⋖ B
```

Here `Subobject.ofLE A B h` is Mathlib's actual monomorphism from the underlying
object of `A` to that of `B`, `cokernel` is the actual categorical cokernel
(the quotient `B/A`), `Simple` is Mathlib's simplicity, and `A ⋖ B` is
Mathlib's `CovBy` in the order of subobjects of `X`. The meaning of the
statement and its source context are explained in the target's Markdown,
`Langlands/CategoryTheory/Renard/SubobjectSimpleCokernelStatements.md`.

No Grothendieck, AB6, well-poweredness, smallness, concreteness, module,
finite-dimensionality, finiteness, `JordanHolderLattice` or modularity
assumption is added. The quotient is the actual cokernel object.

## Provenance

This is a derived internal bridge. Renard, *Représentations des groupes
réductifs p-adiques* (French edition dated 9 July 2026), Appendix A.VI.2(9) and
A.VI.3, printed page 263 / PDF page 269, gives the Noether isomorphisms, defines
simple objects and composition series by simple successive quotients, and
says that Jordan–Hölder follows from those isomorphisms. The book does not
state this equivalence separately. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The proof
below is a direct categorical argument and does not follow a printed proof.

## Auxiliary declarations

All three take `{C : Type u} [Category.{v} C] [Abelian C]`, an object `X`,
subobjects `A B : Subobject X` and `h : A ≤ B`.

- `isZero_cokernel_ofLE_iff h :
  IsZero (cokernel (Subobject.ofLE A B h)) ↔ A = B` — the zero-quotient case.
- `covBy_of_simple_cokernel h (hs : Simple (cokernel (Subobject.ofLE A B h))) :
  A ⋖ B` — the forward direction.
- `simple_cokernel_of_covBy h (hc : A ⋖ B) :
  Simple (cokernel (Subobject.ofLE A B h))` — the reverse direction.

The closing theorem pairs the last two for each `X`, `A`, `B` and `h`.

Write `f = Subobject.ofLE A B h` and `π = cokernel.π f : B ⟶ B/A`, where `B`
also denotes the underlying object of the subobject `B`.

## The zero-quotient case

`isZero_cokernel_ofLE_iff`.

- If `B/A` is a zero object, then `π = 0`, so `f` is an epimorphism
  (`Preadditive.epi_of_cokernel_zero`). A monomorphism and epimorphism in an
  abelian category is an isomorphism (`isIso_of_mono_of_epi`). Its inverse
  commutes with the arrows into `X`, so `B ≤ A` (`Subobject.le_of_comm`), and
  `A = B` by antisymmetry.
- If `A = B`, then `f` is the identity (`Subobject.ofLE_refl`), hence an
  epimorphism, so `π = 0` (`cokernel.π_of_epi`). An epimorphism equal to zero
  has zero target (`IsZero.of_epi_eq_zero`).

This keeps the degenerate inclusion `A = B` in the main statement: the
quotient is zero, so it is not simple, and `A ⋖ B` fails because `A < B`
fails. Each direction below uses this lemma for that case.

## Forward direction: a simple quotient gives a cover

`covBy_of_simple_cokernel` uses Mathlib's characterization
`covBy_iff_lt_and_eq_or_eq`: `A ⋖ B` holds when `A < B` and every `D` with
`A ≤ D ≤ B` equals `A` or `B`.

- `A < B`: a simple object is not zero (`Simple.not_isZero`), so `A ≠ B` by the
  zero-quotient lemma; with `h` this gives `A < B`.
- Let `A ≤ D ≤ B` and `g = Subobject.ofLE D B _`. Consider `g ≫ π : D ⟶ B/A`.
  - If `g ≫ π = 0`, then since the monomorphism `f` is the kernel of its
    cokernel in an abelian category, `g` factors through `f`
    (`Abelian.monoLift`, `Abelian.monoLift_comp`). The factorization commutes
    with the arrows into `X`, so `D ≤ A`, and `D = A`.
  - Otherwise `g ≫ π` is a nonzero morphism to a simple object, so its
    cokernel map is zero (`cokernel_zero_of_nonzero_to_simple`) and it is an
    epimorphism. Then `g` is an epimorphism (`Preadditive.epi_of_cancel_zero`):
    if `g ≫ t = 0`, then `f ≫ t = 0` because `f` factors as
    `Subobject.ofLE A D _ ≫ g` (`Subobject.ofLE_comp_ofLE`), so
    `t = π ≫ cokernel.desc f t _`; composing with the epimorphism `g ≫ π`
    shows `cokernel.desc f t _ = 0`, hence `t = 0`. Being also a monomorphism,
    `g` is an isomorphism, its inverse gives `B ≤ D`, and `D = B`.

## Reverse direction: a cover gives a simple quotient

`simple_cokernel_of_covBy` proves Mathlib's defining property of `Simple`:
for every monomorphism `m : Y ⟶ B/A`, `IsIso m ↔ m ≠ 0`. First, `B/A` is not a
zero object, because `A < B` and the zero-quotient lemma would force `A = B`.

- If `m` is an isomorphism and `m = 0`, then `B/A` is zero
  (`IsZero.of_epi_eq_zero`), a contradiction.
- Suppose `m ≠ 0`. Form the actual pullback of `m` and `π`, with projections
  `pullback.fst m π` to `Y` and `pullback.snd m π` to `B`. The second
  projection is a monomorphism (pullback of the monomorphism `m`), and the
  first is an epimorphism (in an abelian category the pullback of the
  epimorphism `π` is an epimorphism, `Abelian.epi_pullback_of_epi_g`). Put
  `D = Subobject.mk (pullback.snd m π ≫ B.arrow)`, a subobject of `X`.
  Then `A ≤ D`, witnessed by `pullback.lift 0 f _` since `f ≫ π = 0`, and
  `D ≤ B`, witnessed by `pullback.snd m π`. By the cover (`CovBy.eq_or_eq`),
  `D = A` or `D = B`.
  - If `D = A`, then `D ≤ A` gives `s` with `s ≫ f = pullback.snd m π`
    (`Subobject.ofMkLE`, checked after composing with the monomorphism
    `B.arrow`). Hence `pullback.fst m π ≫ m = pullback.snd m π ≫ π =
    s ≫ f ≫ π = 0`, and cancelling the epimorphism `pullback.fst m π` gives
    `m = 0`, contradicting `m ≠ 0`.
  - If `D = B`, then `B ≤ D` gives `t` with `t ≫ pullback.snd m π = 𝟙`
    (`Subobject.ofLEMk`, again checked after composing with `B.arrow`). Hence
    `(t ≫ pullback.fst m π) ≫ m = π`, so `m` is an epimorphism
    (`epi_of_epi_fac`). Being a monomorphism, `m` is an isomorphism.

## Scope and status

The module proves only this criterion. It does not prove Jordan–Hölder,
derive numerical length, translate composition chains into Mathlib
composition series, or add a `JordanHolderLattice` construction. The published
`Langlands.CategoryTheory.Renard.CompositionChains` and
`Langlands.CategoryTheory.Renard.JordanHolderStatements` are unchanged.

A development `lean_check` of this module reported zero errors and zero
warnings. Inspection of the closing theorem reported level parameters `u, v`
and only the axioms `propext`, `Classical.choice` and `Quot.sound`. These are
development checks; acceptance requires independent semantic review, the Lake
build, exact-target and axiom checks, and publication.
