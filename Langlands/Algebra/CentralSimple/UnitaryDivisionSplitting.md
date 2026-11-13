# Unitary involutions: from division algebras to splitting

Author: Worker 166.

This module proves `Langlands.UnitaryDivisionSplittingStatement`, stated by Worker 150
in `Langlands/Algebra/UnitaryInvolutionStatements`. Over every field `K`, the property
`UnitaryDivisionCommutative K` implies `UnitaryInvolutionSplitting K`. That is, if every
finite-dimensional central division algebra over a separable quadratic extension `L/K`
with a unitary involution (relative to the nontrivial `K`-automorphism `σ` of `L`) has
dimension one over `L`, then every finite-dimensional central simple `L`-algebra `B`
with such an involution is `L`-isomorphic to `Matrix (Fin m) (Fin m) L` for some `m`.
It is part of Task 5973. It does not prove the local input
`LocalUnitaryDivisionCommutativeStatement`.

## Definitions

- `algEquivOfFinrankEqOne h`: for a field `L` and a division `L`-algebra `D` with
  `h : Module.finrank L D = 1`, the `L`-algebra isomorphism `L ≃ₐ[L] D` given by the
  structure map `Algebra.ofId L D`. It is bijective: injective because `L` is a field
  and `D` is nontrivial, surjective because `finrank L D = 1` forces `⊥ = ⊤` among the
  `L`-subalgebras of `D` (Mathlib's `Subalgebra.bot_eq_top_of_finrank_eq_one`).

## Statements

- `isCentral_of_matrix`: let `L` be a commutative semiring, `D` an `L`-algebra and `ι`
  a nonempty finite type with decidable equality. If `Matrix ι ι D` is central over `L`
  (`Algebra.IsCentral`), then `D` is central over `L`. This is the converse of Mathlib's
  instance `Algebra.IsCentral.matrix`.
- `unitaryDivisionSplitting : UnitaryDivisionSplittingStatement.{u}`.

## Proofs

**`isCentral_of_matrix`.** Let `d` be central in `D`. The scalar matrix `scalar ι d`
commutes with every matrix (Mathlib's `Matrix.scalar_commute`), so it is central in
`Matrix ι ι D`. By hypothesis it equals `algebraMap L (Matrix ι ι D) c` for some `c`.
Comparing the `(i, i)` entries for some `i : ι` gives `d = algebraMap L D c`.

**`unitaryDivisionSplitting`.** Fix `K`, the hypothesis `UnitaryDivisionCommutative K`,
a separable quadratic extension `L/K`, `σ : L ≃ₐ[K] L` with `σ ≠ 1`, a
finite-dimensional central simple `L`-algebra `B` (`IsSimpleRing B`,
`Algebra.IsCentral L B`), and a unitary involution `τ` of `B` relative to `σ`.

1. `B` is finite-dimensional over the field `L`, hence Artinian
   (`IsArtinianRing.of_finite`). Mathlib's Wedderburn–Artin theorem
   (`IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`) gives `n` with
   `NeZero n`, a division `L`-algebra `D` in the same universe as `B`, finite over `L`,
   and an `L`-algebra isomorphism `Φ : B ≃ₐ[L] Matrix (Fin n) (Fin n) D`.
2. Centrality transfers along `Φ` (`Algebra.IsCentral.of_algEquiv`), and then from
   `Matrix (Fin n) (Fin n) D` to `D` by `isCentral_of_matrix`. `Fin n` is nonempty
   because `n ≠ 0`.
3. Since `σ ≠ 1`, some `ω` has `σ ω ≠ ω`: otherwise `σ = 1` by `AlgEquiv.ext`.
4. The published theorem
   `Langlands.Algebra.CentralSimple.exists_semilinear_involution_of_algEquiv_matrix`
   (module `MatrixSemilinearInvolution`), applied to `Φ`, to `σ` as a ring
   endomorphism, and to the four conjuncts of `IsUnitaryInvolution σ τ`, gives
   `θ : D → D` with the same four properties. So `IsUnitaryInvolution σ θ` holds.
5. The hypothesis `UnitaryDivisionCommutative K`, applied to `L`, `σ`, `D` and `θ`,
   gives `Module.finrank L D = 1`.
6. Then `algEquivOfFinrankEqOne` gives `L ≃ₐ[L] D`, and `AlgEquiv.mapMatrix` of its
   inverse gives `Matrix (Fin n) (Fin n) D ≃ₐ[L] Matrix (Fin n) (Fin n) L`. Composing
   with `Φ` proves the conclusion with `m = n`.

## Provenance

Internal; derived. The implication is the derivation recorded in the reviewed Markdown of
`Langlands/Algebra/UnitaryInvolutionStatements`. That derivation combines Wedderburn's
theorem with the sentence after Theorem (3.1) in Knus, Merkurjev, Rost and Tignol, *The
Book of Involutions* (1998), printed p.31 (PDF p.54): Brauer-equivalent algebras carry
involutions of the same kind. Here that sentence is replaced by the internal theorem
`exists_semilinear_involution_of_algEquiv_matrix`, and Wedderburn–Artin is Mathlib's.
No external statement is transcribed beyond the reviewed Library statement being proved.
