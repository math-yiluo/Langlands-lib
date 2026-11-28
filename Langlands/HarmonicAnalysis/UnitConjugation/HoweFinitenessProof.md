# Howe's finiteness theorem on the Lie algebra of the unit group of a semisimple local algebra: proof

The module `Langlands.HarmonicAnalysis.UnitConjugation.HoweFinitenessProof` proves the
proposition `Langlands.HarmonicAnalysis.LieAlgebraHoweFinitenessStatement.{u, v}` (module
`HoweFinitenessStatement`) as the theorem `Langlands.HarmonicAnalysis.lieAlgebraHoweFiniteness`.

The statement: for every nonarchimedean local field `F : Type u` of characteristic zero, every
finite-dimensional semisimple `F`-algebra `A : Type v` with its module topology, every compact
`ω ⊆ A` and every open additive subgroup `L` of `A`, the image of `J(ω) = invariantSupportedIn ω`
under the restriction `restrictToLatticeTests L` to the `L`-invariant Schwartz–Bruhat functions is
finite-dimensional. This is Howe's theorem, Harish-Chandra's Theorem 12.1 (*Admissible invariant
distributions on reductive p-adic groups*, notes by DeBacker and Sally, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions`, Part II, §12, printed p. 62), for
`G = Aˣ`; the universes `u` and `v` are independent, and finite products and nonsplit simple
factors are included.

## Proof

The theorem is `lieAlgebraHoweFinitenessReduction semisimpleIdempotentOrder`:

- `UnitConjugation.lieAlgebraHoweFinitenessReduction` (module `HoweFinitenessReduction`) proves
  `SemisimpleIdempotentOrderStatement → LieAlgebraHoweFinitenessStatement`, following
  Harish-Chandra's §§11–13 with lattices `ϖ ^ s R` of a compact open order `R`, kernel flags of
  nilpotent elements split by idempotents of `R` (module `KernelFlagCommutator`), and decreasing
  averages of coset indicators (module `IdempotentGradingAverage`);
- `UnitConjugation.semisimpleIdempotentOrder` (module `IdempotentOrderProof`) proves
  `SemisimpleIdempotentOrderStatement`, the existence of such an order, from the Wedderburn–Artin
  theorem, the integer rings of division algebras (module `DivisionIntegers`) and integral
  Gaussian elimination (module `MatrixIdempotentOrder`).

The route differs from Harish-Chandra's as described in the Markdown of
`HoweFinitenessReduction`: no Cartan decomposition, Jacobson–Morozov triple, submersion theorem or
Newton iteration is used.
