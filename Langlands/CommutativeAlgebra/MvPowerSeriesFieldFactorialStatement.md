# Formal power series in finitely many variables over a field are factorial

`Langlands.CommutativeAlgebra.MvPowerSeriesFieldFactorial.{u, v}` is the
following `Prop`-valued definition:

```lean
∀ (K : Type u) [Field K] (σ : Type v) [Finite σ],
  UniqueFactorizationMonoid (MvPowerSeries σ K)
```

It says that for every field `K` in universe `u` and every finite type `σ` in
universe `v`, the ring `MvPowerSeries σ K` of formal power series over `K` in
the variables indexed by `σ` is a unique factorization monoid. Since this ring
is nontrivial, this says that it is a unique factorization domain. In the
notation of the Stacks Project, with `d` the number of elements of `σ`, it says
that `K[[X_1, ..., X_d]]` is a UFD.

## The Mathlib notions used

The module imports only `Mathlib.RingTheory.MvPowerSeries.Basic` and
`Mathlib.RingTheory.UniqueFactorizationDomain.Defs`. It uses Mathlib's `Field`,
`Finite`, `MvPowerSeries` and `UniqueFactorizationMonoid` unchanged and
introduces no new notion.

- `MvPowerSeries σ K` is the type of functions `(σ →₀ ℕ) → K`, a formal power
  series sending each monomial exponent to its coefficient, with the usual
  commutative ring structure. The class `UniqueFactorizationMonoid` is applied
  to the `CommMonoidWithZero` structure coming from this ring structure.
- `Finite σ` says that there is a bijection between `σ` and `Fin n` for some
  natural number `n`. Any such bijection identifies `MvPowerSeries σ K` with
  `MvPowerSeries (Fin n) K`, the ring `K[[X_1, ..., X_n]]`.
- `UniqueFactorizationMonoid α` is a class that extends `IsCancelMulZero α`.
  Its two further fields say that the relation `DvdNotUnit` is well founded
  (here `DvdNotUnit a b` means `a ≠ 0` and `b = a * x` for some non-unit `x`)
  and that an element is irreducible if and only if it is prime. Mathlib's
  annotation on the class says to use it together with `IsDomain` to express a
  unique factorization domain.
- `IsDomain α` extends `IsCancelMulZero α` and `Nontrivial α`. Mathlib has an
  instance `Nontrivial (MvPowerSeries σ R)` for every nontrivial `R`
  (`Mathlib/RingTheory/MvPowerSeries/Basic.lean`), and a field is nontrivial.
  So the proposition also gives `IsDomain (MvPowerSeries σ K)`: the ring
  satisfies `0 ≠ 1` and has no zero divisors.

## Agreement with the Stacks definition

Stacks Definition 10.120.4 (Tag 034S, on the page of Section 10.120, Tag 034O)
calls a domain `R` a unique factorization domain if every nonzero nonunit `x`
is a product of irreducible elements, and
any two such factorizations `x = a_1 ⋯ a_m = b_1 ⋯ b_n` have `n = m` and a
permutation `τ` with `a_i` and `b_τ(i)` associates. In a domain, Stacks'
"irreducible" (Definition 10.120.1, Tag 034P: nonzero, not a unit, and in every
factorization `x = yz` the factor `y` is a unit or an associate of `x`) agrees
with Mathlib's `Irreducible` (not a unit, and in every factorization `x = yz`
one factor is a unit), and Stacks' "associates" (`x = uy` with `u` a unit)
agrees with Mathlib's `Associated`.

For a commutative ring that is a domain, Mathlib's `UniqueFactorizationMonoid`
and the Stacks definition agree:

- If `UniqueFactorizationMonoid R` holds, then `WfDvdMonoid.exists_factors`
  gives, for each nonzero `a`, a multiset of irreducible elements whose product
  is associated to `a`. If `a` is not a unit, the multiset is nonempty, and the
  unit can be absorbed into one factor. `UniqueFactorizationMonoid.factors_unique`
  says that two multisets of irreducible elements with associated products are
  related by `Multiset.Rel Associated`, that is, they have the same size and
  their elements can be paired into associates. This gives the uniqueness
  required by Stacks.
- Conversely, `UniqueFactorizationMonoid.of_existsUnique_irreducible_factors`
  builds `UniqueFactorizationMonoid R` from `IsCancelMulZero R`, existence of
  irreducible factorizations up to associates for nonzero elements, and their
  uniqueness up to `Multiset.Rel Associated`. Both follow from the Stacks
  definition: a unit has the empty factorization, and products that are only
  associated become equal after multiplying one factor by a unit.

## Scope

The field `K` is arbitrary: there is no hypothesis on algebraic closedness,
characteristic, perfectness or cardinality. The index type `σ` is any finite
type, not only `Fin n`, and may be empty; then `MvPowerSeries σ K` is
isomorphic to the field `K`. The universes `u` and `v` are independent and
arbitrary; the Stacks Project does not track universes. The proposition adds no
regularity, Noetherian or completeness hypothesis and no certificate, and it
asserts none of these properties. It says nothing about power series over rings
that are not fields, or in infinitely many variables.

## Original sources and provenance

The proposition is a derived special case of two Stacks Project results, not a
single numbered statement there.

- Stacks Remark 10.160.9 ([Tag 032C](https://stacks.math.columbia.edu/tag/032C)),
  in Section 10.160 (the Cohen structure theorem): "If `k` is a field then the
  power series ring `k[[X_1, ..., X_d]]` is a Noetherian complete local regular
  ring of dimension `d`." The remark carries no proof of its own. The retained
  files are `032C.html` (SHA-256
  `7d652971eb7ac804f0fb4ca44cac3bc122ad86266b2f1de8546a93b5de23572e`) and the
  whole Section 10.160 as `0323.html` (SHA-256
  `9d6b732c706275cda63bd18865b0c7b7723a65d02bd1b8765ed2d6efa0730e86`) in the
  registered literature source
  `stacks-cohen-power-series-regular-032C-2026-10-31`, fetched on
  31 October 2026. The tag page has no comments. The two comments on
  Section 10.160 (#8740 and the maintainers' reply #9337) concern the wording
  of the proof of Theorem 10.160.8, not Remark 10.160.9.
- Stacks Lemma 15.123.2 ([Tag 0AG0](https://stacks.math.columbia.edu/tag/0AG0)):
  "A regular local ring is a UFD." Its proof first recalls that a regular local
  ring is a domain (Lemma 10.106.2) and then argues by induction on the
  dimension. The retained files `0AG0.html` (SHA-256
  `785af7cb4e040abda98bcbe4414785a4c2367059925a01b6d5524c44455008b7`),
  `034O.html` (Section 10.120 with Definitions 10.120.1 and 10.120.4, SHA-256
  `cdcf8897e69e6cf37c2bd119f936c7dddbda5581f703860f10c6aa66aef485a3`) and
  `0FJH.html` (Section 15.123, SHA-256
  `4d7d1fd5b54c96e6db5f7378903cee09078195a2787ed962edf5195878491bcc`) are in
  the registered literature source `stacks-regular-local-ufd-2026-10-29`.
  On 31 October 2026 the current official pages for Tags 0AG0, 034O and 0FJH
  were byte-identical to these files. The tag page for 0AG0 has no comments.
  The two comments on Section 15.123 (#6705 and the reply #6908) suggest adding
  further results on power series over regular UFDs; they do not correct
  Lemma 15.123.2.

Composing the two results: for a finite `σ` with `d` elements, a bijection
`σ ≃ Fin d` identifies `MvPowerSeries σ K` with `K[[X_1, ..., X_d]]`, which is a
regular local ring by Remark 10.160.9 and hence a UFD by Lemma 15.123.2. The
Lean proposition records only this conclusion.

## Special cases in Mathlib

At the pinned Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`:

- One variable. `PowerSeries R` is an `abbrev` for `MvPowerSeries Unit R`, and
  `Mathlib/RingTheory/PowerSeries/Inverse.lean` has the instance
  `UniqueFactorizationMonoid k⟦X⟧` for every field `k` (obtained, like the
  instance `IsDiscreteValuationRing k⟦X⟧` there, from the factorization of every
  nonzero series as a unit times a power of `X`). So the case `σ = Unit` is a
  Mathlib instance. Other one-element types need transport along a renaming
  equivalence.
- Iterated series. `Mathlib/RingTheory/PowerSeries/Ideal.lean` has the instance
  `UniqueFactorizationMonoid R⟦X⟧` for every principal ideal domain `R`. Since
  `k⟦X⟧` is a discrete valuation ring, this covers `k⟦X⟧⟦Y⟧`, which is
  isomorphic to, but not syntactically, a two-variable `MvPowerSeries`.
- Zero variables. For empty `σ`, `MvPowerSeries.isEmptyEquiv` identifies
  `MvPowerSeries σ K` with `K`, which is a unique factorization monoid as a
  field.

Mathlib has no theorem that `MvPowerSeries σ K` is a unique factorization
monoid for a general finite `σ`, no theorem that a regular local ring is a
unique factorization domain, and no `IsRegularLocalRing` instance for
`MvPowerSeries`.

## Proof boundary

The Lean file only defines this proposition; it supplies no proof. A separate
proof must establish this exact proposition. The Library already contains
ingredients for one: `Langlands.CommutativeAlgebra.MvPowerSeriesFactorial.uniqueFactorizationMonoid_of_coord`
proves `UniqueFactorizationMonoid (MvPowerSeries (Fin n) K)` for every field `K`
and every `n`, given a coordinate-change hypothesis that
`Langlands.CommutativeAlgebra.MvPowerSeriesFactorial.exists_algEquiv_coeff_single_zero_ne_zero`
provides. The general finite `σ` would then follow by transport along
`MvPowerSeries.renameEquiv`; this transport is not part of the present module.
