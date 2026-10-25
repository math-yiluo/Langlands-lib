# Idempotented rings and their corners

## Source and scope

This unit implements the ring portion of David Renard, *Représentations des groupes réductifs p-adiques*, French version dated **9 July 2026**, I.1.1–I.1.2, printed pages 6–7 / PDF pages 12–13. The registered source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, retained at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`. The title and cited original pages were read. No project errata entry was present when this unit was prepared. The adjacent 2020 edition is not used.

All declarations live in `Langlands.Algebra`, with the corner API in its `Idempotent` namespace. The ambient type `A : Type u` carries Mathlib's associative `NonUnitalRing` structure. There is no commutativity, characteristic, nontriviality, topology, dimension, or scalar-field assumption. An ambient ring may have a unit, but none is required or chosen. In particular, the corner of the zero idempotent is allowed to be the trivial unital ring. The construction uses Mathlib's actual `IsIdempotentElem`, `NonUnitalSubring`, and `NonUnitalRingHom` infrastructure.

This unit contains concrete definitions and their intrinsic laws. It does not construct module categories, nondegenerate parts, adjunctions, or categorical filtered colimits. The union theorem below is solely an equality of sets; it does not assert a categorical universal property.

## Corners: I.1.1, printed page 6

`Idempotent A` is a dedicated structure with an ambient element `val : A` and its Mathlib idempotence proof `property : IsIdempotentElem val`. It coerces to the ambient element, and `Idempotent.ext` identifies two idempotents with equal underlying elements. The dedicated structure prevents Lean from inheriting an unrelated order from an ordered ambient ring. Thus an index is an actual ambient element together with its idempotence proof, rather than an abstract label for an assumed corner.

For an idempotent `e`, `Idempotent.corner e : NonUnitalSubring A` has carrier

```text
{a : A | e * a * e = a}.
```

The zero, addition, negation, and multiplication closure fields are proved from ring laws. `mem_corner` is exactly this membership characterization. `sandwich_eq_iff` and `mem_corner_iff` identify it with the pair of equations `e * a = a` and `a * e = a`. This two-sided reformulation is derived by multiplying the sandwich equation on each side and using `e * e = e`; its converse substitutes the two equations.

`self_mem_corner` puts `e` in its own corner. `mem_corner_iff_exists` proves that the carrier is exactly the image of `b ↦ e * b * e`, matching Renard's `eAe`. `mem_corner_iff_left_right_image` gives the source's equality `eAe = eA ∩ Ae` in membership form: an element belongs to the corner if and only if it can be written both as `e * b` and as `c * e`. Idempotence makes those two image conditions equivalent to the two fixed-point equations. These are literal images of multiplication in the ambient nonunital ring.

`Idempotent.Corner e` is the type of elements of `e.corner`. Its nonunital ring structure is inherited from that subring. Its `One` instance is the element `e`, with membership proved by idempotence. `Idempotent.Corner.ring` supplies an actual `Ring` instance: the two fixed-point equations prove the identity laws; natural and integer casts are repeated addition of this unit. No ring laws are postulated as extra input fields.

`Idempotent.Corner.toAmbient e : Corner e →ₙ+* A` is Mathlib's subring inclusion. `toAmbient_injective` proves injectivity, and `toAmbient_one` says that its value on the corner's identity is `e`. This correctly treats the ambient ring as possibly nonunital.

## Order and absorption: I.1.1 lemma, printed page 6

The `PartialOrder (Idempotent A)` instance defines `e ≤ f` by `e.corner ≤ f.corner`. Here the subring order is set inclusion. Reflexivity and transitivity come from inclusion. For antisymmetry, the two containments imply `e * f = e` and `e * f = f`, hence equality of the ambient elements and of their idempotent structures. The dedicated `Idempotent` type ensures that the inferred `LE`, `Preorder`, and `PartialOrder` all come from this corner order even if the ambient ring already has an order.

The following declarations expose all clauses of I.1.1(i):

| Declaration | Meaning |
| --- | --- |
| `le_iff_corner_le e f` | `e ≤ f` if and only if `eAe` is contained in `fAf` |
| `le_iff_mem_corner e f` | `e ≤ f` if and only if `e` belongs to `fAf` |
| `le_iff_sandwich e f` | `e ≤ f` if and only if `f * e * f = e` |
| `le_iff_mul e f` | `e ≤ f` if and only if `f * e = e` and `e * f = e` |

The auxiliary `corner_le_iff_mem` proves the main inclusion criterion before the order instance is installed. Inclusion sends `e` into `f`'s corner. Conversely, the two absorption identities for `e` and `f`, together with the fixed-point identities for an arbitrary element of `e`'s corner, put that element in `f`'s corner. These are associativity calculations; they require no commutativity.

`mul_eq_of_le` is I.1.1(ii): if `e ≤ f` and `e * a = a`, then `f * a = a`. Its proof substitutes `e * a` for `a` and uses `f * e = e`. The derived companion `mul_eq_of_le_right` proves the corresponding right equation using `e * f = e`.

`Idempotent.Corner.inclusion h : Corner e →ₙ+* Corner f`, for `h : e ≤ f`, is the actual subring inclusion. `inclusion_injective` proves it is injective. `toAmbient_inclusion` says that inclusion leaves the ambient element unchanged. `toAmbient_inclusion_one` records that the image of the smaller corner's identity is still `e`, while the larger corner's identity maps to `f`. These inclusions are nonunital ring homomorphisms; no unit-preserving claim is made when the idempotents differ.

## Finite local units: I.1.2, printed page 7

`IsIdempotented A : Prop` is the predicate

```text
∀ s : Finset A, ∃ e : Idempotent A, ∀ a ∈ s, e * a * e = a.
```

This matches Renard's definition for every finite set of ambient elements. The displayed equation has the opposite orientation from `a = eae` in the source, which is immaterial. The quantifier order requires one common idempotent for the entire set. The empty set is included.

`IsIdempotented.iff_two_sided_local_units` is the derived equivalent formulation with `e * a = a` and `a * e = a`, retaining the same idempotent and quantifier order. It applies `sandwich_eq_iff` under the quantifiers. `iff_finite_set` gives the same condition for `s : Set A` with `s.Finite`, using Mathlib's conversions between finite sets and finsets. This shows the use of `Finset` does not impose extra mathematical data on Renard's definition.

`of_ring R` proves the first ring assertion of I.1.2 Remark 1: every unital ring is idempotented. It chooses the actual identity of `R` for every finite set. The remark's assertions about modules are outside this unit.

`finite_family` extends the predicate to any family `a : ι → A` with `[Finite ι]`. The index type has an independent universe `v`, while `A` has universe `u`. It applies the finite-set condition to the image of a finite enumeration. This is an internal reformulation of the finite-set definition, not an additional hypothesis.

`finite_upper_bound` proves the lemma immediately after the definition: every `s : Finset (Idempotent A)` has a common upper bound. It applies the defining predicate to the image of `s` in `A`, then uses `le_iff_sandwich`. `finite_family_upper_bound` expresses the same property for a family in any independently chosen finite index universe, including an empty family. Its proof applies `finite_family` to the underlying ambient idempotents.

`exists_mem_corner` applies the predicate to a singleton and proves that every ambient element belongs to some actual unital corner. `iUnion_corners` packages exactly this result as

```text
(⋃ e : Idempotent A, (e.corner : Set A)) = Set.univ.
```

This implements the set-theoretic union equality in I.1.2. Renard also writes a direct-limit equality there; implementing that categorical statement requires a separate diagram and universal property and is not claimed here.
