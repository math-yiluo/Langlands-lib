# Proof: formal power series in finitely many variables over a field are factorial

This module proves the Library proposition
`Langlands.CommutativeAlgebra.MvPowerSeriesFieldFactorial.{u, v}` from
`Langlands.CommutativeAlgebra.MvPowerSeriesFieldFactorialStatement`:

```lean
theorem mvPowerSeriesFieldFactorial : MvPowerSeriesFieldFactorial.{u, v}
```

That is, for every field `K : Type u` and every finite type `σ : Type v`, the
ring `MvPowerSeries σ K` is a `UniqueFactorizationMonoid`. The universes `u` and
`v` stay independent and arbitrary, and no hypothesis is used beyond those in
the statement: the field is arbitrary (any characteristic, finite or infinite)
and `σ` may be empty.

The module imports the statement module, the Library modules
`Langlands.CommutativeAlgebra.MvPowerSeriesFactorial` and
`Langlands.CommutativeAlgebra.MvPowerSeriesCoordinateChange`, and
`Mathlib.RingTheory.MvPowerSeries.Rename`. It adds only the one theorem above.

## Route

The statement's Markdown cites Stacks Remark 10.160.9 (Tag 032C,
`k[[X_1, ..., X_d]]` is a regular local ring) and Stacks Lemma 15.123.2
(Tag 0AG0, a regular local ring is a UFD). This proof does not go through
regular local rings. It uses the Library's earlier proof that
`MvPowerSeries (Fin n) K` is factorial, which runs by induction on `n` with the
Weierstrass preparation theorem, and transports that result to an arbitrary
finite index type by renaming the variables.

## The proof

After introducing `K`, its `Field` instance, `σ` and its `Finite` instance, the
proof proceeds in three steps.

1. **A `Fintype` structure on `σ`.** `nonempty_fintype σ` (Mathlib,
   `Mathlib/Data/Fintype/Basic.lean`) gives `Nonempty (Fintype σ)` from
   `Finite σ`; `cases` on it puts a `Fintype σ` instance in context. Write
   `d = Fintype.card σ`.

2. **The case `Fin d`.** The Library theorem

   ```lean
   theorem Langlands.CommutativeAlgebra.MvPowerSeriesFactorial.uniqueFactorizationMonoid_of_coord
       (K : Type*) [Field K]
       (hcoord : ∀ (n : ℕ) (f : MvPowerSeries (Fin (n + 1)) K), f ≠ 0 →
         ∃ φ : MvPowerSeries (Fin (n + 1)) K ≃ₐ[K] MvPowerSeries (Fin (n + 1)) K,
           ∃ k : ℕ, MvPowerSeries.coeff (Finsupp.single 0 k) (φ f) ≠ 0)
       (n : ℕ) : UniqueFactorizationMonoid (MvPowerSeries (Fin n) K)
   ```

   (`Langlands/CommutativeAlgebra/MvPowerSeriesFactorial.lean`) proves
   factoriality of `K[[X_1, ..., X_n]]` for every `n`, given the coordinate
   change `hcoord`: every nonzero series in `n + 1` variables becomes, after a
   `K`-algebra automorphism, a series with a nonzero coefficient at some pure
   power `X 0 ^ k` of the first variable. The Library theorem

   ```lean
   theorem Langlands.CommutativeAlgebra.MvPowerSeriesFactorial.exists_algEquiv_coeff_single_zero_ne_zero
       {K : Type*} [CommRing K] {n : ℕ}
       {f : MvPowerSeries (Fin (n + 1)) K} (hf : f ≠ 0) :
       ∃ φ : MvPowerSeries (Fin (n + 1)) K ≃ₐ[K] MvPowerSeries (Fin (n + 1)) K,
         ∃ k : ℕ, MvPowerSeries.coeff (Finsupp.single 0 k) (φ f) ≠ 0
   ```

   (`Langlands/CommutativeAlgebra/MvPowerSeriesCoordinateChange.lean`) supplies
   exactly this, over any commutative ring and hence over our field `K`, so
   `fun _ _ hf => exists_algEquiv_coeff_single_zero_ne_zero hf` is a valid
   `hcoord`. Applying `uniqueFactorizationMonoid_of_coord K` with it at
   `n = d` gives `hfin : UniqueFactorizationMonoid (MvPowerSeries (Fin d) K)`.

3. **Renaming the variables.** `Fintype.equivFin σ : σ ≃ Fin d` (Mathlib,
   `Mathlib/Data/Fintype/EquivFin.lean`) is a bijection, and Mathlib's
   `MvPowerSeries.renameEquiv K (Fintype.equivFin σ)` (in
   `Mathlib/RingTheory/MvPowerSeries/Rename.lean`) is the induced `K`-algebra
   isomorphism `MvPowerSeries σ K ≃ₐ[K] MvPowerSeries (Fin d) K`. The proof
   takes its underlying multiplicative equivalence, inverts it to get
   `MvPowerSeries (Fin d) K ≃* MvPowerSeries σ K`, and applies Mathlib's
   `MulEquiv.uniqueFactorizationMonoid`
   (`Mathlib/RingTheory/UniqueFactorizationDomain/Basic.lean`), which for
   commutative monoids with zero `α` and `β` turns `e : α ≃* β` and
   `UniqueFactorizationMonoid α` into `UniqueFactorizationMonoid β`. Applied to
   `hfin`, this is the goal `UniqueFactorizationMonoid (MvPowerSeries σ K)`.

## Checks

The development check of this module (`lean_check` with Lake build, diagnostic
`ee4d5371-26bf-4860-9bae-eb29c866d351`) reported no errors or warnings. The
inspection of `Langlands.CommutativeAlgebra.mvPowerSeriesFieldFactorial`
reported a theorem with universe parameters `u` and `v` whose axioms are only
`propext`, `Classical.choice` and `Quot.sound`. The proof contains no `sorry`,
`admit` or new axiom.

## Provenance

The proof was written for this module by Worker 1131; the same five-line
argument was compiled privately when the statement was published (statement
task `e1114eaa-f3be-4863-920c-3746e31d9a07`). Its mathematical content is in
the two imported Library theorems, written for proof task
`7d63b52e-e715-47d0-a015-331cfa8a4b6d` (`uniqueFactorizationMonoid_of_coord`
by Worker 254, `exists_algEquiv_coeff_single_zero_ne_zero` by Worker 1131),
and in the Mathlib declarations named above.
