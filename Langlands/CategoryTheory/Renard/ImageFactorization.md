# Renard A.VI.2(1, 4–5): proof of balancedness, images and factorization

Author: Worker 795 (Lean proof and this note). The proof target and the list of
required clauses come from the specification of task
`4bc289b5-47e8-4626-aa61-e3f3337f7ffa`, published by Worker 6. The target
statement and its universal properties were written by Worker 207 in
`Langlands.CategoryTheory.RenardImageFactorizationStatements`. This proof does
not reuse any private draft.

## What is proved

Module `Langlands.CategoryTheory.Renard.ImageFactorization`, namespace
`Langlands.Renard`. It imports the target statement module by its Lean name and
does not change it.

The main theorem is

```lean
theorem imageFactorizationStatement (C : Type u) [Category.{v} C] [Abelian C] :
    ImageFactorizationStatement C
```

for independent universes `u` (objects) and `v` (morphisms). It has no further
hypothesis. The statement is the conjunction
`IsoIffMonoAndEpiStatement C ∧ AbelianImageCoimageStatement C ∧
EpiMonoFactorizationStatement C`, whose meaning and source correspondence
(Renard 2026, Appendix A.VI.2(1), the image and coimage definitions, (4) and (5),
printed page 262 / PDF page 268, with the orders of A.I.2, printed page 248 /
PDF page 254) are explained in the target's Markdown,
`Langlands/CategoryTheory/RenardImageFactorizationStatements.md`.

The three clauses are also exported as separate theorems:

- `isoIffMonoAndEpiStatement C : IsoIffMonoAndEpiStatement C`;
- `abelianImageCoimageStatement C : AbelianImageCoimageStatement C`;
- `epiMonoFactorizationStatement C : EpiMonoFactorizationStatement C`.

Each takes `C : Type u` with `[Category.{v} C]` and `[Abelian C]` explicitly. The
kernel reports only the standard axioms `propext`, `Classical.choice` and
`Quot.sound` for the main theorem.

## Reusable lemmas

Three lemmas give the two universal properties of the target.

- `imageUniversalProperty_of_strongEpi`: in any category, if `e ≫ m = f` and
  `e` is a strong epimorphism (`[StrongEpi e]`), then
  `ImageUniversalProperty f e m`. No hypothesis on `m` is needed.
- `coimageUniversalProperty_of_mono`: in any category with
  `[StrongEpiCategory C]`, if `e ≫ m = f` and `m` is a monomorphism, then
  `CoimageUniversalProperty f e m`. No hypothesis on `e` is needed.
- `imageUniversalProperty_of_epi`: in an abelian category, if `e ≫ m = f` and
  `e` is an epimorphism, then `ImageUniversalProperty f e m`.

The proofs use the lifting property of a strong epimorphism against a
monomorphism (Mathlib's `CommSq.lift`).

*Image.* Let `e' ≫ m' = f` with `m'` mono. Then `e' ≫ m' = e ≫ m`, a commutative
square with the strong epi `e` on the left and the mono `m'` on the right. Its
lift `t : I ⟶ J` satisfies `e ≫ t = e'` and `t ≫ m' = m`. If another `t'` has
`t' ≫ m' = m`, then `t' ≫ m' = t ≫ m'`, so `t' = t` because `m'` is mono.

*Coimage.* Let `e' ≫ m' = f` with `e'` epi. In a `StrongEpiCategory`, `e'` is a
strong epimorphism (`strongEpi_of_epi`). The square `e ≫ m = e' ≫ m'` has `e'` on
the left and the mono `m` on the right. Its lift `t : J ⟶ I` satisfies
`e' ≫ t = e` and `t ≫ m = m'`. This is the direction required by
`CoimageUniversalProperty`: from the arbitrary epi factorization to the given
one. If another `t'` has `e' ≫ t' = e`, then `e' ≫ t' = e' ≫ t`, so `t' = t`
because `e'` is epi.

In an abelian category Mathlib supplies `StrongEpiCategory C`: the class
`Abelian` extends `IsNormalEpiCategory C` (every epimorphism is normal), which
gives `IsRegularEpiCategory C` (`regularEpiCategoryOfNormalEpiCategory`), which
gives `StrongEpiCategory C` (`strongEpiCategory_of_regularEpiCategory`). These
instances are found automatically.

## `isoIffMonoAndEpiStatement` (source (1))

This is Mathlib's `isIso_iff_mono_and_epi`, which needs `[Balanced C]`. Mathlib
derives `Balanced C` from `StrongEpiCategory C` (`balanced_of_strongEpiCategory`),
so the instance is found for every abelian `C`.

## `abelianImageCoimageStatement` (source (4) and the definitions)

The fifteen conjuncts of `AbelianImageCoimageStatement C` at `f : X ⟶ Y` are
proved as follows.

1. `Abelian.image.ι f = kernel.ι (cokernel.π f)`: `rfl`, since `Abelian.image.ι`
   is an `abbrev` for `kernel.ι (cokernel.π f)`.
2. `Abelian.coimage.π f = cokernel.π (kernel.ι f)`: `rfl` for the same reason.
3. `ImageUniversalProperty f (Abelian.factorThruImage f) (Abelian.image.ι f)`:
   `imageUniversalProperty_of_epi` applied to Mathlib's `Abelian.image.fac f`
   (`Abelian.factorThruImage f ≫ Abelian.image.ι f = f`). The factor map is epi
   by Mathlib's abelian instance.
4. `(Abelian.imageIsoImage f).hom ≫ Limits.image.ι f = Abelian.image.ι f`:
   Mathlib's `Abelian.imageIsoImage_hom_comp_image_ι`.
5. `Abelian.factorThruImage f ≫ (Abelian.imageIsoImage f).hom =
   Limits.factorThruImage f`: cancel the monomorphism `Limits.image.ι f`; by
   associativity, clause 4 and `Limits.image.fac`, both sides become
   `Abelian.factorThruImage f ≫ Abelian.image.ι f = f`, which is
   `Abelian.image.fac f`.
6. `CoimageUniversalProperty f (Abelian.coimage.π f) (Abelian.factorThruCoimage f)`:
   `coimageUniversalProperty_of_mono` applied to Mathlib's `Abelian.coimage.fac f`.
   The map `Abelian.factorThruCoimage f` is mono by Mathlib's abelian instance.
7. `Epi (Abelian.factorThruImage f)`, `Mono (Abelian.image.ι f)`: Mathlib
   instances. The factorization identity is `Abelian.image.fac f`.
8. `Epi (Abelian.coimage.π f)`, `Mono (Abelian.factorThruCoimage f)`: Mathlib
   instances. The factorization identity is `Abelian.coimage.fac f`.
9. `IsIso (Abelian.coimageImageComparison f)`: Mathlib's abelian instance.
10. `Abelian.coimage.π f ≫ Abelian.coimageImageComparison f =
    Abelian.factorThruImage f`: unfold `Abelian.coimageImageComparison f`, which
    is `cokernel.desc (kernel.ι f) (kernel.lift (cokernel.π f) f _) _`, and
    simplify with `cokernel.π_desc`.
11. `Abelian.coimageImageComparison f ≫ Abelian.image.ι f =
    Abelian.factorThruCoimage f`: both sides are maps out of the cokernel
    `Abelian.coimage f`, so by cokernel extensionality (`ext`) it suffices to
    compare them after `Abelian.coimage.π f`; unfolding the comparison, `simp`
    reduces both to `f`.

## `epiMonoFactorizationStatement` (source (5))

For `f : X ⟶ Y`:

1. *Existence.* The witness is the actual kernel-of-cokernel factorization
   `Abelian.factorThruImage f ≫ Abelian.image.ι f = f`, through
   `Abelian.image f`, with the Mathlib epi and mono instances.
2. *Unique compatible isomorphism.* Let `e ≫ m = f` through `I` and
   `e' ≫ m' = f` through `J` be epi–mono factorizations. The image universal
   property of `e ≫ m` (from `imageUniversalProperty_of_epi`, as `e` is epi),
   applied to the mono factorization `e' ≫ m'`, gives `t : I ⟶ J` with
   `t ≫ m' = m` and `e ≫ t = e'`. Symmetrically, the image universal property of
   `e' ≫ m'` gives `s : J ⟶ I` with `s ≫ m = m'`. Then
   `(t ≫ s) ≫ m = t ≫ m' = m`, so `t ≫ s = 𝟙 I` because `m` is mono; likewise
   `s ≫ t = 𝟙 J` because `m'` is mono. The isomorphism `⟨t, s, _, _⟩ : I ≅ J`
   satisfies `e ≫ t = e'` and `t ≫ m' = m`. For uniqueness, let `φ : I ≅ J`
   satisfy the same two equations. By `Iso.ext` it suffices that
   `φ.hom = t`; cancelling the mono `m'`, both `φ.hom ≫ m'` and `t ≫ m'` equal
   `m`.
3. *Identification.* For every epi–mono factorization `e ≫ m = f`,
   `ImageUniversalProperty f e m` holds by `imageUniversalProperty_of_epi` (as `e`
   is epi) and `CoimageUniversalProperty f e m` holds by
   `coimageUniversalProperty_of_mono` (as `m` is mono).

## Relation to the source route

Renard lists these assertions as consequences of the abelian axioms without a
displayed proof. The Lean proof does not follow a textual argument. It uses the
fact, proved in Mathlib, that every epimorphism of an abelian category is
strong, together with Mathlib's checked abelian image and coimage constructions
and their comparison isomorphism. The image and coimage directions are those of
the target's `ImageUniversalProperty` and `CoimageUniversalProperty`; the coimage
comparison goes from the arbitrary epi factorization to the given one.

## Scope

Only the target aggregate and its three clauses are proved here. Other A.VI
assertions (A.VI.2(2–3), (6), (7), (8), the Noether isomorphisms) and the
comparison of Renard's seven axioms with Mathlib's `Abelian` class remain
separate obligations. No axiom, `sorry` or extra hypothesis is introduced.
