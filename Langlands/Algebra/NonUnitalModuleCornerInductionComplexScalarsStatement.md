# Renard I.3.2: the two complex structures on `A ⊗_{eAe} Z` coincide

Module `Langlands.Algebra.NonUnitalModuleCornerInductionComplexScalarsStatement`.
Namespace `Langlands.Algebra.NonUnitalModuleCornerInduction`.
Entry proposition `ComplexScalarsStatement`.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read I.3.2 on printed pp.19–20 / PDF pp.25–26. The assertion
stated here is the remark right after the Lemma (I.3.2.1), printed p.20 /
PDF p.26:

> Remarquons que nous ne sommes pas tout-à-fait dans les conditions de la
> section I.2.3 où le foncteur `P` est défini de manière similaire, car `A`
> n'est pas un `eAe`-module unitaire, `e` n'agissant pas comme l'identité de
> `A`. Néanmoins si `Z` est un `eAe`-module unitaire, c'est en particulier un
> C-espace vectoriel. L'algèbre `A` aussi, et les deux structures induites de
> C espaces-vectoriel sur le produit tensoriel `A ⊗_{eAe} Z` coïncident.

The surrounding text (printed p.19 / PDF p.25) fixes `A` as a complex algebra
with idempotents and `e ∈ Idem(A)`. The Lemma's induction functor is
`i : M(eAe) → M(A)`, `Z ↦ A ⊗_{eAe} Z`. The source does not say how `Z` is a
complex vector space. The only structure available is the unital algebra
`eAe`, whose unit is `e`, so `c ∈ ℂ` acts on `Z` as the corner element `c e`.
The Lean statement uses exactly this.

## The objects

All objects come from the Library; this file constructs nothing.

- `A` is an arbitrary `NonUnitalRing A` with `Module ℂ A`,
  `IsScalarTower ℂ A A` and `SMulCommClass ℂ A A`, which is the published
  encoding of a complex algebra, for instance in `NonUnitalModuleCornerScalars`.
- `e : Idempotent A`, `eAe` is the published unital ring
  `Idempotent.Corner e`, and `Idempotent.Corner.toAmbient e` is its inclusion
  into `A`.
- `Z` is an additive group with `Module (Idempotent.Corner e) Z`, an ordinary
  module over the unital ring `eAe`, hence a unital `eAe`-module.
- `A ⊗_{eAe} Z` is the published balanced quotient
  `NonUnitalModuleCornerInduction.Tensor e Z` with additive group
  `tensorAddCommGroup e Z`, for the right action of `eAe` on `A` by
  multiplication (`rightCornerModule`) and the given left action on `Z`.
  `tmul e a z` is `a ⊗ z`. This is the carrier of the published induction
  functor of (I.3.2.1).

## `ComplexScalarsStatement`

For all such `A`, `e` and `Z`, two things hold.

1. There is a `Module ℂ Z` such that for every `c : ℂ` some
   `s : Idempotent.Corner e` satisfies `toAmbient e s = c • e` and
   `c • z = s • z` for all `z : Z`. In words: `Z` is a complex vector space on
   which `c` acts as the corner element `c e`. This is "c'est en particulier un
   C-espace vectoriel".
2. With the additive group `tensorAddCommGroup e Z` on `A ⊗_{eAe} Z`, there is
   a `Module ℂ (Tensor e Z)` such that for all `c : ℂ`, every
   `s : Idempotent.Corner e` with `toAmbient e s = c • e`, all `a : A` and all
   `z : Z`,
   - `c • (a ⊗ z) = (c • a) ⊗ z`, the structure induced from `A`, and
   - `c • (a ⊗ z) = a ⊗ (s • z)`, the structure induced from `Z`.

Clause 2 says that both induced structures exist on the quotient and that they
are equal. Pure tensors generate `A ⊗_{eAe} Z` additively, so each formula
determines the complex structure. The element `s` is unique because
`toAmbient e` is injective, and `s • z` is the action of `c` from clause 1.

## Internal formal choices

- The source speaks of a complex algebra with idempotents. The statement
  drops the idempotented hypothesis (`IsIdempotented A`): the remark uses
  neither local units nor nondegeneracy, and it stays true for every complex
  algebra and idempotent. The statement is therefore at least as general as the
  source.
- The complex structure on `Z` and on the tensor product are stated as
  existence of a `Module ℂ` instance with prescribed scalar action. The Library
  has no named complex structure on these carriers, and the source does not
  name one either.
- The complex structure on `A` is the given `Module ℂ A`; the formula
  `c • a` in clause 2 uses it.

## Scope and dependencies

This file states the remark and proves nothing. A proof belongs to a separate
`lean.proof@1` task targeting `ComplexScalarsStatement`.

The other assertions of I.3.2 are published: the Lemma (I.3.2.1) in
`NonUnitalModuleCornerInductionStatements`, the Proposition and Theorem in
`NonUnitalModuleCornerSimpleStatements`, and the related constructions listed
there.

The file imports only `Langlands.Algebra.NonUnitalModuleCornerInduction`
(environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`). It uses `tensorAddCommGroup e Z`
as an explicit `letI` and does not install the right corner action as a local
instance; `tmul` already selects it.
