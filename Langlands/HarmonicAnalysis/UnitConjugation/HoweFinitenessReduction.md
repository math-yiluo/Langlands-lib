# Howe's finiteness theorem from idempotent generators in a compact open order

The module `Langlands.HarmonicAnalysis.UnitConjugation.HoweFinitenessReduction` states, as
`Langlands.HarmonicAnalysis.UnitConjugation.LieAlgebraHoweFinitenessReductionStatement.{u, v}`,
the implication

`SemisimpleIdempotentOrderStatement.{u, v} → LieAlgebraHoweFinitenessStatement.{u, v}`

and proves it (`lieAlgebraHoweFinitenessReduction`). The premise
(module `IdempotentOrderStatement`) says that a finite-dimensional semisimple algebra `A` over a
nonarchimedean local field `F` has a compact open order `R` (a compact open subring stable under
the integers of `F`) such that every left ideal of `A` is `A e` for an idempotent `e ∈ R`. The
conclusion (module `HoweFinitenessStatement`) is Howe's finiteness theorem, Harish-Chandra's
Theorem 12.1, for `F` of characteristic zero: for compact `ω ⊆ A` and open `L`, the image of
`J(ω) = invariantSupportedIn ω` under `restrictToLatticeTests L` is finite-dimensional. The
module does not prove the premise. The universes `u` of `F` and `v` of `A` are independent.

## Nilpotent approximation

In the section on the nilpotent cone, `F` is a field and `A` a finite-dimensional `F`-algebra.

- `regularCharCoefficients F x : Fin (finrank F A) → F`: the coefficients of the characteristic
  polynomial of left multiplication by `x` below the leading one.
- `regularCharCoefficients_conj`: invariance under `x ↦ g x g⁻¹` for units `g`.
- `regularCharCoefficients_eq_zero_iff`: the coefficients vanish exactly when `x` is nilpotent
  (`LinearMap.isNilpotent_iff_charpoly` and injectivity of `Algebra.lmul`).
- `continuous_regularCharCoefficients` (`F` a topological ring, `A` with its module topology):
  the coefficients are polynomials in the matrix entries of left multiplication in a basis, and
  these entries are linear, hence continuous.
- `isClosed_setOf_isNilpotent` (also `[T2Space F]`): the nilpotent elements form a closed set.
- `exists_nhds_nilpotentApproximation`: let `K` be compact, `V` open containing the nilpotent
  points of `K`, and `ω` compact. There are neighbourhoods `U_F` of `0` in `F` and `U_A` of `0`
  in `A` such that `x ∈ V` whenever `x ∈ K`, `c ∈ U_F`, `a ∈ ω`, `g` a unit and
  `c • (g a g⁻¹) - x ∈ U_A`. Proof: the set of `((x, a), (c, e))` with
  `χ(x + e) ≠ χ(c • a)` (`χ = regularCharCoefficients F`) is open and contains
  `((K \ V) × ω) × {(0, 0)}`; the tube lemma gives a product neighbourhood, and
  `x + e = g (c a) g⁻¹` would contradict conjugation invariance. This is the topological form of
  the Library's `nilpotentApproximation` (module `NilpotentApproximation`), which is stated for
  normed algebras.

## Howe's theorem for the lattices `ϖ ^ s R`

`finiteDimensional_restrict_orderLevel`: let `F` be a nonarchimedean local field of
characteristic zero, `A` a finite-dimensional semisimple `F`-algebra with its module topology,
`R` a compact open order of `A` in which every left ideal has an idempotent generator,
`ϖ ≠ 0` with `valuation F ϖ < 1`, `s : ℤ` and `ω` compact. Then
`(invariantSupportedIn ω).map (restrictToLatticeTests (ϖ ^ s R))` is finite-dimensional.

Proof, with `L = ϖ ^ s R`:

1. *Normalized nilpotent elements.* The "unit sphere" `S = R \ ϖ R` is compact, and so is its
   set `Nil` of nilpotent elements. For `X₀ ∈ Nil` with `X₀ ^ n = 0`,
   `exists_isKernelFlagSplitting` splits the kernel flag of `X₀` by orthogonal idempotents of
   `R`, `IsKernelFlagSplitting.mul_mul_eq_zero_self` and
   `IsKernelFlagSplitting.exists_commutator_eq` (characteristic zero, semisimplicity) give the
   hypotheses of `exists_decreasing_average`, which yields numbers `a(X₀)`, `t(X₀)`.
2. *Finite cover.* The open sets `X₀ + ϖ ^ a(X₀) R` cover the compact `Nil`. Choose a finite
   subcover with union `V`. Let `t_max` be the supremum in `ℕ` of the thresholds `t(X₀)` for the
   selected centres, with value `0` for the empty subcover.
3. *Thresholds.* `exists_nhds_nilpotentApproximation` for `K = S`, `V`, `ω` gives `U_F`, `U_A`;
   choose `t₁` with `ϖ ^ h ∈ U_F` for `h ≥ t₁` and `n₁` with `ϖ ^ n₁ R ⊆ U_A`. Put
   `T₀ = t_max + t₁ + n₁ + |s| + 1`, the compact set `K = ϖ ^ (-T₀) R`, the height
   `height x = min {n : ℕ | x ∈ ϖ ^ (-n) R}`, and the set
   `B = {x | 1_{x + L} vanishes on the closure of ω^G}`.
4. *Vanishing.* Every `T ∈ J(ω)` is invariant and vanishes on `1_{x + L}` for `x ∈ B`, so
   `J(ω) ≤ vanishingOnLatticeCosets L B`.
5. *Decreasing averages.* Let `x ∉ B`, `x ∉ K`, and `h = height x`; then `h > T₀`, and
   `X' = ϖ ^ h x ∈ S`. Since `x + L` meets the closure of `ω^G`, it contains some `g a g⁻¹` with
   `a ∈ ω`; then `ϖ ^ h (g a g⁻¹) - X' ∈ ϖ ^ (s + h) R ⊆ U_A`, so `X' ∈ V`, say
   `X' ∈ X₀ + ϖ ^ a(X₀) R`. As `h ≥ t(X₀)`, `exists_decreasing_average` with
   `λ = X' - X₀` gives an `L`-invariant test `f` supported in `ϖ ^ (1 - h) R`, hence on
   elements of height `< h`, with `T f = T (1_{x + L})` for invariant `T`
   (`ϖ ^ (-h) (X₀ + λ) = x`).
6. The Library's `howeFinitenessFromAverages` (Harish-Chandra's Theorem 11.1 / Lemma 11.2)
   gives finite-dimensionality of the restrictions of `vanishingOnLatticeCosets L B`, hence of
   those of `J(ω)` (`Submodule.finiteDimensional_of_le`).

## The reduction

`lieAlgebraHoweFinitenessReduction`: given the premise, `F`, `A`, `ω` and an open additive
subgroup `L` of `A`, take the order `R`, an element `ϖ ≠ 0` with `valuation F ϖ < 1`
(`Valuation.IsNontrivial.exists_lt_one`) and `s` with `ϖ ^ s R ⊆ L`
(`exists_orderLevel_subset`). Every `L`-invariant test is `ϖ ^ s R`-invariant, so
`restrictToLatticeTests L` is `restrictToLatticeTests (ϖ ^ s R)` followed by restriction to the
smaller space of tests; the image of `J(ω)` is the image of a finite-dimensional space under a
linear map.

## Source and comparison

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, notes by
DeBacker and Sally, University Lecture Series 16, AMS, 1999, source ID
`harish-chandra-1999-admissible-invariant-distributions` (PDF page = printed page + 15),
Part II, §§11–13, printed pp. 58–69: Theorem 11.1 and Lemma 11.2 (height induction), Lemma 11.9
(compactness of `N ∩ S`), Lemmas 12.2–12.4 and Theorem 12.1, and Theorem 13.1. The route differs
from Harish-Chandra's in three places. Lemma 12.2 (`ω^G ⊆ L₁ + N`, proved with the Cartan
decomposition) is replaced by the nilpotent approximation above, which only needs the invariance
of the characteristic polynomial; Harish-Chandra's well adapted lattices and Jacobson–Morozov
triples are replaced by the order `R` of the premise and the kernel flags of nilpotent elements
(module `KernelFlagCommutator`); and his Theorem 13.1 is replaced by
`exists_decreasing_average` (module `IdempotentGradingAverage`). Harish-Chandra states the
theorem for lattices; open subgroups contain lattices `ϖ ^ s R`, which gives the form of
`LieAlgebraHoweFinitenessStatement`.
