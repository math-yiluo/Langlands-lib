# Proof: field extensions in characteristic zero have smooth factorizations

`Langlands.CommutativeAlgebra.Popescu.charZeroFieldFactorization :
CharZeroFieldFactorizationStatement.{u}` proves the Library statement
`CharZeroFieldFactorizationStatement`. Its source is Stacks Project, Commutative Algebra,
Lemma 10.158.11 (Tag 07BV) together with Proposition 10.158.9 (Tag 0322), in the mapping
form of Lemma 10.127.4 (Tag 07C3).

## Proof

Let `f : A → L` be a `K`-algebra map with `A` finitely presented over `K`.

1. **The image.** Let `D = f.range ⊆ L`. It is a domain, finitely generated over `K` (as
   the image of `A`), and hence finitely presented, since `K` is Noetherian.
2. **The generic point.** The localization of `D` at the prime `(0)` is a fraction field of
   `D` (`Ideal.primeCompl_bot`), so it is a field (`IsFractionRing.toField`). It is
   essentially of finite type over `K`, and `K` is perfect because its characteristic is
   zero (`PerfectField.ofCharZero`). Mathlib's `Algebra.FormallySmooth.of_perfectField`
   therefore shows that it is formally smooth over `K`, that is, `D` is smooth at `(0)`
   (`Algebra.IsSmoothAt`). This replaces the separability argument of Lemma 10.158.10.
3. **A smooth neighbourhood.** `Algebra.IsSmoothAt.exists_notMem_smooth` gives `g ≠ 0` in
   `D` with `D_g` smooth over `K`.
4. **The factorization.** Since `g` is a unit in the field `L`, the inclusion `D → L`
   extends to `D_g → L` (`IsLocalization.Away.lift`). Then
   `A → D → D_g → L` is the required factorization of `f`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
