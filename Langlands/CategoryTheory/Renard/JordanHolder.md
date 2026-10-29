# Proof of Renard A.VI.3: the Jordan–Hölder theorem in an abelian category

This module proves the published statement
`Langlands.Renard.JordanHolderStatement C` of
`Langlands.CategoryTheory.Renard.JordanHolderStatements` for every
`C : Type u` with `[Category.{v} C]` and `[Abelian C]`. The object universe `u`
and the Hom universe `v` are independent. The statement is David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated 9 July
2026, Appendix A.VI.3, printed page 263 / PDF page 269. Its meaning and the
indexing of the factors are explained in the statement's own Markdown. This
module imports the statement by Lean name and does not change it.

For an object `X`, two published composition chains `c : CompositionChain X n`
and `d : CompositionChain X m` are given. The proof yields `n = m` and a
bijection `e : Fin n ≃ Fin m` such that every actual factor `c.factor i` is
isomorphic to `d.factor (e i)`. These factors are the actual cokernels
`B (i + 1) / B i` of the chains' subobject inclusions. A bijection of indices
retains multiplicities. The length-zero case needs no separate treatment.

No hypothesis is added. There is no Grothendieck, AB6, `WellPowered`,
smallness, concreteness, module, finite-dimensionality, finite-type or
`JordanHolderLattice` assumption. The axioms used are only `propext`,
`Classical.choice` and `Quot.sound`.

## Declarations

All declarations are in namespace `Langlands.Renard`.

| Declaration | Type |
| --- | --- |
| `jordanHolder` | `∀ (C : Type u) [Category.{v} C] [Abelian C], JordanHolderStatement C` |
| `simple_cokernel_ofLE_iff_covBy` | `∀ {C : Type u} [Category.{v} C] [Abelian C] {X : C} (A B : Subobject X) (h : A ≤ B), Simple (cokernel (Subobject.ofLE A B h)) ↔ A ⋖ B` |

`jordanHolder` is the proof of the target. `simple_cokernel_ofLE_iff_covBy` is
an internal criterion that the proof needs. It is not a numbered statement of
the book. For subobjects `A ≤ B` of `X`, the actual quotient `B/A` is simple
exactly when `B` covers `A` among the subobjects of `X`. Here `A ⋖ B` is
Mathlib's `CovBy`: `A < B` and no subobject lies strictly between them. The
criterion uses no hypothesis beyond `[Abelian C]`.

The remaining declarations are private helpers:

- `le_of_ofLE_comp_π_eq_zero`: if `A ≤ B`, `D ≤ B`, and the inclusion of `D`
  into `B` followed by the projection `B ⟶ B/A` is zero, then `D ≤ A`.
- `eq_of_epi_ofLE`: if `D ≤ B` and the inclusion `D ⟶ B` is an epimorphism,
  then `D = B`.
- `not_isZero_cokernel_ofLE`: if `A < B`, the quotient `B/A` is not zero.
- `subobjectJordanHolderLattice X`, also installed as an instance local to this
  module: a `JordanHolderLattice` structure on `Subobject X` whose maximality
  relation is `CovBy`.
- `intervalQuotient p`: for a pair `p = (A, B)` of subobjects, the cokernel of
  the inclusion of `A ⊓ B` into `B`.
- `intervalQuotient_eq`: if `A ≤ B`, then `intervalQuotient (A, B)` equals
  the actual cokernel of `Subobject.ofLE A B h`.
- `intervalIso_quotient`: Mathlib's interval relation
  `JordanHolderLattice.Iso p q` implies an isomorphism between
  `intervalQuotient p` and `intervalQuotient q`.
- `compositionChainSeries c`: the Mathlib `CompositionSeries (Subobject X)` of
  length `n` with exactly the subobjects of the chain `c`.

## Proof route

Renard says that the theorem follows from the Noether isomorphisms A.VI.2(9).
The proof here uses the published second isomorphism
`Langlands.Renard.secondIso` from `Langlands.CategoryTheory.RenardNoetherIsomorphisms`.
It combines that isomorphism with Mathlib's order-theoretic theorem
`CompositionSeries.jordan_holder` from `Mathlib.Order.JordanHolder`. It also uses
the published helpers `exists_lift_of_comp_cokernel_π` and
`mono_cokernel_desc_of_factors` from the same Noether module.

### The cover criterion

Write `ι` for the inclusion `Subobject.ofLE A B h` and `π` for the projection
`B ⟶ B/A`.

Helpers. If the inclusion of `D` followed by `π` is zero, it lifts through `ι`
by `exists_lift_of_comp_cokernel_π`. The lift commutes with the arrows into
`X`, so `D ≤ A`. If the inclusion `D ⟶ B` is an epimorphism, it is an
isomorphism, since monomorphisms that are epimorphisms are isomorphisms in an
abelian category. Its inverse shows `B ≤ D`. If `A < B` and `B/A` were zero,
then `π` would be zero. The first helper with `D = B` would give `B ≤ A`, a
contradiction.

Simple implies cover. If `A = B`, then `ι` is the identity, hence an
epimorphism, and its cokernel is zero. A simple object is not zero, so
`A < B`. Now let `A ≤ D ≤ B`, and consider the inclusion of `D` followed by `π`.
If this composite is zero, the first helper gives `D ≤ A`, so `D = A`.
Otherwise it is a nonzero morphism to a simple object, hence an epimorphism by
Mathlib's `epi_of_nonzero_to_simple`. Then the inclusion `D ⟶ B` is an
epimorphism. Indeed, suppose `g : B ⟶ Z` vanishes on `D`. Then `g` vanishes on
`A`, because `ι` factors through `D`. So `g` factors as `π` followed by some
map `B/A ⟶ Z`. That map vanishes after the epimorphic composite, so it is
zero, and `g = 0`. The second helper gives `D = B`. Mathlib's
`covBy_iff_lt_and_eq_or_eq` turns these two facts into `A ⋖ B`.

Cover implies simple. Mathlib's `simple_of_cosimple` reduces simplicity of
`B/A` in an abelian category to this: every epimorphism `f : B/A ⟶ Z`
satisfies `IsIso f ↔ f ≠ 0`. Let `k = π ≫ f`. Let `D` be the subobject of `X`
given by `kernel.ι k` followed by `B.arrow`. Then `A ≤ D ≤ B`, because
`ι ≫ k = 0`. By the cover property, `D = A` or `D = B`.

- If `D = A`, then every morphism killed by `k` factors through `ι`. Hence
  `f`, which equals the map `cokernel.desc ι k` induced by `k`, is a
  monomorphism by `mono_cokernel_desc_of_factors`. As an epimorphism and a
  monomorphism, `f` is an isomorphism. It is nonzero, because `B/A` is
  nonzero.
- If `D = B`, then `kernel.ι k` has a right inverse, so `k = 0`. Since `π` is
  an epimorphism, `f = 0`. An isomorphism `0` would make `B/A` zero, so `f` is
  not an isomorphism, matching `f = 0`.

### The Jordan–Hölder lattice on actual subobjects

The proof equips `Subobject X` with a `JordanHolderLattice` structure inside
this module only; the target theorem takes no such hypothesis. Its maximality
relation is `CovBy`. A cover is a strict inequality. If two distinct
subobjects are both covered by `Z`, their join is `Z` by Mathlib's
`WCovBy.sup_eq`.

The remaining law asks: if `A ⋖ A ⊔ B` and `B ⋖ A ⊔ B`, then `A ⊓ B ⋖ A`.
Only the second hypothesis is used. By the cover
criterion, the quotient `(B ⊔ A)/B` is simple. Public `secondIso` gives an
isomorphism `A/(B ⊓ A) ≅ (B ⊔ A)/B`, so `A/(B ⊓ A)` is simple too. The criterion
then gives `B ⊓ A ⋖ A`, and commutativity of `⊓` and `⊔` gives the law.

### Interval quotients

Mathlib's relation `JordanHolderLattice.Iso` on pairs of subobjects is the
equivalence relation generated by `(A, A ⊔ B) ~ (A ⊓ B, B)` whenever
`A ⋖ A ⊔ B`. To interpret it, the module uses a total quotient on all pairs:
for `(A, B)` it takes the cokernel of the inclusion of `A ⊓ B` into `B`. When
`A ≤ B`, this is exactly the actual cokernel `B/A`, because `A ⊓ B = A`. Being
isomorphic is reflexive, symmetric and transitive. Each generating pair has
isomorphic quotients `(A ⊔ B)/A ≅ B/(A ⊓ B)`, again by public `secondIso`.
Mathlib's `JordanHolderLattice.Iso.rel` therefore shows that related pairs have
isomorphic total quotients.

### The theorem

A published chain `c : CompositionChain X n` gives the Mathlib composition
series `compositionChainSeries c`. Its length is `n` and its terms are exactly
`c.subobject`. Each step is a cover: the chain's factor is simple, and the
cover criterion applies. The published endpoint equations `subobject 0 = ⊥`
and `subobject (Fin.last n) = ⊤` show that the series of `c` and of `d` have
the same first and last terms.

`CompositionSeries.jordan_holder` then yields `e : Fin n ≃ Fin m`. For each
`i`, the interval `(c.subobject i.castSucc, c.subobject i.succ)` is related to
`(d.subobject (e i).castSucc, d.subobject (e i).succ)`. The interval
interpretation gives an isomorphism of their total quotients. Since both
intervals are ordered, these quotients are the actual factors `c.factor i` and
`d.factor (e i)`. Equality of the cardinalities of `Fin n` and `Fin m` gives
`n = m`.

If `n = 0`, the same argument applies. The equivalence `Fin 0 ≃ Fin m` forces
`m = 0`, and the factor condition is vacuous.

## Development evidence

A development check of this module succeeded with no errors or warnings. The
inspection reported a theorem with independent universe levels `u, v` and only
`propext`, `Classical.choice` and `Quot.sound`. This is not acceptance; exact
target validation, the Lake build and independent review remain to be done.
