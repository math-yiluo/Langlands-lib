# Admissibility of real standard modules

Lean module: `Langlands.Representation.Archimedean.RealStandardModuleAdmissible`.

This module proves that the `(𝔤𝔩_n(ℝ), O(n))`-module of every real standard module of the
Library is admissible. It states this as `RealStandardAdmissibleStatement` and proves it as
`realStandardAdmissible`. It also proves the sharper bound that a matrix representation of
degree `d` of `O(n)` occurs at most `d` times. No hypothesis on the blocks is needed.

Notation: `GL_n(ℝ)` is `Langlands.GeneralLinear n ℝ`, `O(n)` is
`unitaryCompact ℝ n` (as a subgroup of `GL_n(ℝ)`) or `Matrix.unitaryGroup (Fin n) ℝ` (as a
group). `principalSeries ℝ n χ` is the Library's normalized smooth principal series
(`StandardModule`): the smooth functions `f` on `GL_n(ℝ)` with
`f(diag(a) · u · g) = principalSeriesCharacter ℝ n χ a · f(g)` for invertible diagonal entries
`a` and upper unipotent `u`, where
`principalSeriesCharacter ℝ n χ a = ∏ᵢ χ i (a i) · |a i|^((n-1)/2 - i)` (positions
`i = 0, …, n-1`) is the product of the characters `χ i` and the square root `δ_B^{1/2}` of the
modulus character of the upper triangular Borel subgroup. The arguments below only use that two
functions of the same principal series have the same multiplier. For a right-translation-stable
subspace `V` of functions, `kFiniteRep V hVK` is right translation by `O(n)` on the
`O(n)`-finite functions of `V`
(`PrincipalSeriesGKModule`), and `gkIntertwiners ρ d τ` is the space of `O(n)`-intertwiners
from the matrix representation `τ` of degree `d` to `ρ` (`GKModule`).

## The statement

`RealStandardAdmissibleStatement`: for every `n : ℕ` and every list `ds : List RealBlock`,
`IsAdmissibleGKModule (realStandardRep n ds)`. That is, for every continuous matrix
representation `τ : O(n) →* Matrix (Fin d) (Fin d) ℂ`, the space
`gkIntertwiners (realStandardRep n ds) d τ` of `O(n)`-intertwiners from `τ` into the
`O(n)`-finite functions of `realStandardModule n ds` is finite-dimensional. Here
`realStandardRep n ds` is the Library's `O(n)`-action on the `O(n)`-finite part of the real
standard module (`RealStandardModuleGKModule`). The statement puts no condition on `ds`, so it
also covers lists of blocks whose ranks do not add up to `n`.

The same real assertion is the first conjunct of the Library's
`Langlands.Automorphic.ArchimedeanStandardAdmissibleStatement` (module
`Langlands.Automorphic.CuspidalArchimedeanComponentStatement`), where it is paired with the
complex counterpart; this module proves only the real conjunct.

Provenance. The statement is derived content, modelled on Knapp 1986, Proposition 8.4 and
Remark (1) after it (pp. 207-208). There, `G` is a connected linear reductive group, `S = MAN`
is a parabolic subgroup, `σ` is an irreducible unitary representation of `M`, and the induced
Hilbert-space representation `U(S, σ, ν)` is shown to be admissible with
`[U(S, σ, ν)|_K : τ] ≤ dim τ`, by Frobenius reciprocity for `K`. This module does not use that
result or any identification of the Library's models with classical parabolic induction.
Instead it proves the analogous finiteness and multiplicity bound directly for the Library's
function models on `GL_n(ℝ)`, which is not connected: for every right-translation-stable
subspace of a Library principal series, and in particular for `realStandardModule n ds`, with
multiplicity measured as the dimension of the intertwiner space on `O(n)`-finite functions. The
statement holds for every list `ds`; when the ranks of the blocks do not add up to `n`, the
Library's `realStandardModule n ds` is still a subspace of a principal series, but it is not
claimed to be a classical induced representation. The bound `≤ d` holds for every matrix
representation of degree `d`, irreducible or not, so continuity of `τ` is not used.

## Lemmas proved here

* `exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact` (Iwasawa decomposition): every
  `g ∈ GL_n(ℝ)` is `diag(a) · u · k` with `a : Fin n → ℝˣ`, `u` upper unipotent and
  `k ∈ O(n)`. The proof applies the Library's
  `TriangularUnitary.exists_upperTriangular_mul_unitary` (proved there through a Cholesky
  factorization of `g gᴴ`) to the matrix of `g`,
  giving `g = b · w` with `b` invertible upper triangular and `w` orthogonal. The diagonal
  entries of `b` are nonzero, since `det b` is their product
  (`Matrix.det_of_isUpperTriangular`). With `D = diag(b₁₁, …, bₙₙ)`, the matrix `D⁻¹ · b` is
  upper triangular (a product of block-triangular matrices) with ones on the diagonal, and
  `g = D · (D⁻¹ · b) · w`.
* `eq_of_eqOn_unitaryCompact_of_mem_principalSeries`,
  `eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact`: two functions of the same principal
  series that agree on `O(n)` are equal. Write `g = diag(a) · u · k` and apply the
  transformation law of both functions.
* `gkIntertwinerValueAtOne V hVK d τ`: for a right-translation-stable subspace `V` of
  functions on `GL_n(ℝ)`, the linear map sending an intertwiner `T` to the linear functional
  `x ↦ (T x)(1)` on `ℂ^d`.
* `gkIntertwiner_apply_unitary`: `(T x)(k) = (T (τ(k) x))(1)` for `k ∈ O(n)`. Indeed
  `T (τ(k) x) = ρ(k) (T x)` is the right translate of `T x` by `k`, whose value at `1` is
  `(T x)(k)`.
* `gkIntertwinerValueAtOne_injective`: if `V` lies in a principal series, then
  `gkIntertwinerValueAtOne` is injective. If `S` and `T` give the same functional, then by the
  previous lemma `S x` and `T x` agree on `O(n)` for every `x`, so they are equal.
* `finrank_gkIntertwiners_kFiniteRep_le`: the intertwiner space has dimension at most
  `dim (ℂ^d)^* = d`, by injectivity into the dual of `ℂ^d`.
* `isAdmissibleGKModule_kFiniteRep`: hence `kFiniteRep V hVK` is admissible for every
  right-translation-stable subspace `V` of a principal series.
* `finrank_gkIntertwiners_realStandardRep_le` and `realStandardAdmissible`: the case
  `V = realStandardModule n ds`, which lies in the principal series of
  `realPositionCharacter ds` by the Library's `realStandardModule_le_principalSeries`.

This is the Frobenius-reciprocity argument of Knapp's proof restricted to what is needed:
evaluation at `1` embeds `Hom_K(τ, V)` into `Hom(τ, ℂ)`, because a function of the principal
series is determined by its restriction to `K`.

## Sources

* A. W. Knapp, *Representation Theory of Semisimple Groups: An Overview Based on Examples*,
  Princeton University Press, 1986. Proposition 8.4 and Remark (1), pp. 207-208 (PDF pages
  221-222 of the retained scan): admissibility of induced representations and the bound
  `[U(S, σ, ν)|_K : τ] ≤ dim τ`; the proof uses Frobenius reciprocity (Theorem 1.14).
