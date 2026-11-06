# Central simple algebras over a separably closed field

Lean module: `Langlands.Algebra.CentralSimple.SeparablyClosedSplitting`
(`Langlands/Algebra/CentralSimple/SeparablyClosedSplitting.lean`).

## Mathematical content

Let `F` be a separably closed field and `B` a finite-dimensional central simple
algebra over `F` (in Lean: `[Field F] [IsSepClosed F] [Ring B] [Algebra F B]
[FiniteDimensional F B] [Algebra.IsCentral F B] [IsSimpleRing B]`). Then `B` is
isomorphic, as an `F`-algebra, to a full matrix algebra `Matrix (Fin n) (Fin n) F`
with `n` positive, and necessarily `n * n = finrank F B`, so `n` is the natural
square root of the dimension.

This is Milne, *Algebraic Groups* (2022 corrected reprint), Proposition 24.21,
printed p. 522 (PDF p. 533): "The only central simple algebras over a separably
closed field `k` are the matrix algebras `M_n(k)`." Milne's standing convention
(Section 24d, printed p. 521) is that all algebras are finite-dimensional over
`k`, which is the hypothesis `FiniteDimensional F B` here; his degree `[A : k]` is
`Module.finrank F B` and his reduced degree (footnote 3) is the matrix size `n`.
Milne's `n ≥ 1` (Example 24.15) is the positivity statement.

The module contains no hypothesis about scalar extension, splitting fields or
maximal subfields; everything is proved from pinned Mathlib.

## Declarations

- `mem_bot_of_isSeparable_of_isSepClosed F D (hx : IsSeparable F x)`: in a
  division ring `D` that is an algebra over a separably closed field `F`, every
  separable element `x` lies in `⊥ : Subalgebra F D`, i.e. is a scalar.
- `bot_eq_top_of_isSepClosed F D`: if moreover `D` is finite-dimensional and
  central over `F`, then `(⊥ : Subalgebra F D) = ⊤`.
- `algebraMap_bijective_of_isSepClosed F D`: under the same hypotheses the
  structure map `algebraMap F D` is bijective.
- `isCentral_of_algEquiv_matrix (e : B ≃ₐ[F] Matrix (Fin n) (Fin n) D)`, for
  `[NeZero n]` and `B` central over `F`: the coefficient algebra `D` is central
  over `F`. Here `D` is any ring with an `F`-algebra structure in the same
  universe as `B`.
- `finrank_eq_mul_self_of_algEquiv_matrix (e : B ≃ₐ[F] Matrix (Fin n) (Fin n) F)`:
  `Module.finrank F B = n * n` (for any field `F` and any `F`-algebra `B`).
- `exists_algEquiv_matrix_of_isSepClosed F B`: there are `n` with `NeZero n` and an
  `F`-algebra equivalence `B ≃ₐ[F] Matrix (Fin n) (Fin n) F`.
- `finrank_eq_sqrt_mul_sqrt_of_isSepClosed F B`:
  `finrank F B = Nat.sqrt (finrank F B) * Nat.sqrt (finrank F B)`.
- `sqrt_finrank_pos_of_isSepClosed F B`: `0 < Nat.sqrt (finrank F B)`. This only
  uses that `B` is a nontrivial finite-dimensional algebra (the simple-ring
  hypothesis supplies nontriviality); the separably closed and central hypotheses
  are omitted from its statement.
- `sepClosedChart F B : B ≃ₐ[F] Matrix (Fin (Nat.sqrt (finrank F B)))
  (Fin (Nat.sqrt (finrank F B))) F`: a chosen chart, normalised to the matrix size
  `Nat.sqrt (finrank F B)`. It is defined by `Classical.choice` from the
  existence theorem and transported along `Matrix.reindexAlgEquiv` and `finCongr`;
  nothing is claimed about which chart is chosen. Its size, together with
  `finrank_eq_sqrt_mul_sqrt_of_isSepClosed` and `sqrt_finrank_pos_of_isSepClosed`,
  gives Milne's reduced degree and the identity `[B : F] = n²`.

## Implemented proof

The Lean route differs in its second step from Milne's proof, which uses the
separable maximal subfield of Theorem 24.20; here Mathlib's Jacobson–Noether
theorem is used instead.

1. **Wedderburn–Artin.** `B` is Artinian (`IsArtinianRing.of_finite F B`), so
   Mathlib's `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite F B` gives
   `n` with `NeZero n`, a division ring `D` finite over `F` and
   `e : B ≃ₐ[F] Matrix (Fin n) (Fin n) D` (Milne 24.17).
2. **Centrality of `D`** (`isCentral_of_algEquiv_matrix`). The matrix algebra is
   central by `Algebra.IsCentral.of_algEquiv`. For `z` in the centre of `D`, the
   scalar matrix `Matrix.scalar (Fin n) z` lies in the centre of the matrix algebra
   (`Matrix.subalgebraCenter_eq_scalarAlgHom_map`), so it equals `algebraMap F _ c`
   for some `c : F`; comparing the `(0, 0)` entries gives `z = algebraMap F D c`.
3. **`D = F`** (`bot_eq_top_of_isSepClosed`). If `⊥ ≠ ⊤` in `Subalgebra F D`, then
   `D` is a noncommutative algebraic (finite-dimensional) central division algebra,
   and `JacobsonNoether.exists_separable_and_not_isCentral'` provides a separable
   element `x ∉ ⊥`. But over a separably closed field the minimal polynomial of a
   separable element is irreducible and separable, hence of degree one
   (`IsSepClosed.degree_eq_one_of_irreducible`), so `x` is a scalar
   (`minpoly.mem_range_of_degree_eq_one`); contradiction. Thus `algebraMap F D` is
   injective (`FaithfulSMul.algebraMap_injective`) and surjective, and
   `AlgEquiv.ofBijective (Algebra.ofId F D)` is an `F`-algebra isomorphism `F ≃ D`.
4. **Chart.** Composing `e` with `AlgEquiv.mapMatrix` of the inverse isomorphism
   gives `B ≃ₐ[F] Matrix (Fin n) (Fin n) F`.
5. **Dimension.** An `F`-linear equivalence with `n × n` matrices gives
   `finrank F B = n * n` (`Module.finrank_matrix`), hence `Nat.sqrt (finrank F B)
   = n` by `Nat.sqrt_eq`; this also reindexes the chosen chart in
   `sepClosedChart`. Positivity of the square root is `Nat.sqrt_pos` with
   `Module.finrank_pos`.

The result holds in every characteristic and at independent universes `uF` of the
field and `uB` of the algebra.
