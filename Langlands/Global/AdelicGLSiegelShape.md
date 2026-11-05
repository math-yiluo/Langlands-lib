# Siegel sets for the actual adelic `GL(n)`

This module defines Siegel sets `Ω_N · diag(C) · A(c) · K` in the actual adelic group
`AdelicGL F n = GL(n, 𝔸_F)`. It proves that every element of `GL(n, 𝔸_F)` lies in such a
set after left multiplication by a rational invertible matrix. The compact sets `Ω_N` and
`C` and the constant `c` depend only on `F` and `n`. Here `F : Type u` is an arbitrary
number field and `n : ℕ` is arbitrary, including `n = 0`. The adele ring is the full
`Adeles F = AdeleRing (𝓞 F) F` with its actual topology. The absolute value of ideles is the
Library's normalized `IdeleAbsoluteValue.full F`. All declarations are in the namespace
`Langlands.Global.PrimitiveAdelicHeight`.

## Provenance

The statements are derived. Springer, *Reduction theory over global fields* (1994),
registered as `springer-1994-reduction-global-fields`, SHA256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`, §2.1 (printed
pp. 211–212, PDF pp. 5–6), works with a connected reductive `G`, a minimal parabolic `P`
and a maximal split torus `S ⊆ P`. It fixes a compact set `K` with
`G(A)⁰ = K.(S(A) ∩ G(A)⁰).P(A)⁰`, defines `S(c)` as the set of `s ∈ S(A) ∩ G(A)⁰` "such
that `|α(s)| ≤ c` all `α ∈ Δ`", and puts `𝒮(c) = K.S(c).P(A)⁰`. Its fundamental set theorem
(F) reads: "If `G` is isotropic there is `c` with `G(A)⁰ = 𝒮(c).G(k)`." Remark 2.2(a)
(printed p. 212) uses a compact set `K₁` with `L(A)⁰ = K₁.L(k)` for the Levi group `L` of
`P` to rewrite this as `G(A)⁰ = K.K₁.S.U(A)G(k)`, and then, using 1.7, as
`G(A)⁰ = K'.T(c).K''.G(k)` with compact sets `K' ⊂ G(A)⁰` and `K'' ⊂ U(A)`.

This module proves a statement of the same kind for `G = GL(n)` and the upper triangular
Borel subgroup, with the following differences.

* The group is all of `GL(n, 𝔸_F)`, not `G(A)⁰`. The center is absorbed into the positive
  real factor.
* The rational matrix acts on the left, and the Siegel set is written in the order
  unipotent part, Levi part, positive real torus part, compact part:
  `γ g = N · diag(ω) · diag(a) · κ`. Springer's `K.S(c).P(A)⁰` with `G(k)` on the right
  becomes a set of this shape after inversion. That conversion is not formalized here.
* For `GL(n)` the Levi group of the Borel subgroup is the diagonal torus. Its part is split
  into a compact set `C` of norm-one ideles in each diagonal entry (the analogue of `K₁`)
  and positive real ideles `a i`. The chamber condition is `|a (i + 1)| ≤ c · |a i|`. Its
  direction comes from the inversion in the previous item.
* `K` is the explicit compact subgroup `standardCompact F n` of
  `Langlands.Global.AdelicGLStandardCompact`.

The proof does not follow Springer's §2. It combines the project's `GL(n)` reduction
`exists_reduction_GL` (from `Langlands.Global.PrimitiveAdelicGLn`, which goes back to the
minimality argument in the proof of Springer's Proposition 1.10) with three further Library
inputs. These are the triangular–compact factorization of `AdelicGLStandardCompact`, the
compact fundamental set for norm-one ideles modulo principal ideles
(`NormOneIdeleClass.exists_isCompact_fundamentalSet`), and the rational reduction of
unitriangular adelic matrices into a compact box (`exists_isCompact_unitriangular_reduction`,
from `Langlands.Global.PrimitiveAdelicUnipotent`). The definitions, constants and the form of
the statements are internal to the project's route.

## Triangular and diagonal matrices

Over a commutative ring `R`, for `n : ℕ`:

* `diag_mul_of_isUpperTriangular hA hB i`: for upper triangular `A` and `B`,
  `(A * B) i i = A i i * B i i`.
* `isUpperTriangular_inv hg`: if `g : GL (Fin n) R` has upper triangular value, so does
  `g⁻¹`.
* `inv_diag_mul_diag hg i`: for such `g`, `(g⁻¹) i i * g i i = 1`.
* `diagonalUnit g hg i : Rˣ` is the diagonal entry `g i i` of an upper triangular
  invertible `g`, as a unit with inverse `(g⁻¹) i i`.
* `diagonalGL d : GL (Fin n) R` is the invertible diagonal matrix with unit diagonal entries
  `d i`.
* `map_diagonalGL f d`: applying a ring homomorphism `f` to `diagonalGL d` gives the diagonal
  matrix with entries `f (d i)`.
* `isUnitriangular_mul_diagonal hP s hs`: if `P` is upper triangular with `P i i = s i` for
  units `s i`, then `P * diag((s i)⁻¹)` is unitriangular (`IsUnitriangular`, from
  `PrimitiveAdelicUnipotent`: upper triangular with all diagonal entries `1`).
* `IsUnitriangular.diagonal_conj hN d`: if `N` is unitriangular, so is
  `diag(d) * N * diag(d⁻¹)`.

## Two inequalities

* `chamber_le`: for real numbers with `0 < m`, `0 < Ti`, `0 < Tj`, `0 ≤ Ui`, `0 ≤ M`,
  `Si * Ti = Ui`, `Sj * Tj = Uj`, `Ti ≤ c * Tj`, `m ≤ Ui` and `Uj ≤ M`, one has
  `Sj ≤ c * M / m * Si`.
* `full_bounds_of_local F hm hfin hinf`: let `x` be an idele equal to `1` at every finite
  place, with `m ≤ ‖x w‖ ≤ M` at every infinite place `w` and `0 ≤ m`. Then its normalized
  absolute value lies in `[m ^ d, M ^ d]`, where `d = Module.finrank ℚ F`. The proof uses the
  sum of the multiplicities of the infinite places, which is `d`
  (`NumberField.InfinitePlace.sum_mult_eq`).

## The Siegel set

* `siegelSetGL F n Ω_N C c : Set (AdelicGL F n)`, for a set `Ω_N` of adelic `n × n`
  matrices, a set `C` of ideles and `c : ℝ`. It is the set of `h` such that there are a
  matrix `N`, ideles `ω : Fin n → Ideles F`, positive reals `r : Fin n → ℝ≥0ˣ` and
  `κ : AdelicGL F n` with
  * `h = N · diag(ω) · diag(a) · κ` as matrices, where `a i = PositiveRealIdeles.full F (r i)`
    is the idele with value `r i` at every infinite place and `1` at every finite place;
  * `N ∈ Ω_N`, `ω i ∈ C` for every `i`, and `κ ∈ standardCompact F n`;
  * `|a j| ≤ c · |a i|` whenever `i + 1 = j`, for the normalized absolute value `|·|`.

## Main theorem

* `exists_rational_mul_mem_siegelSetGL F n`: there are `Ω_N`, `C` and `c` such that
  * `Ω_N` is compact and consists of unitriangular matrices;
  * `C` is compact and contained in `NormOneIdeleClass.normOneIdeles F`;
  * `0 < c`;
  * for every `g : AdelicGL F n` there is `γ : RationalGL F n` with
    `AdelicGL.rational F n γ * g ∈ siegelSetGL F n Ω_N C c`.

Proof. Take `c₀, B` from `exists_reduction_GL F n`, `Ω_N` from
`exists_isCompact_unitriangular_reduction F n` and `C` from
`NormOneIdeleClass.exists_isCompact_fundamentalSet F`. Put `m = (√n · B)⁻¹`,
`M = (√n · B)ⁿ`, `d = [F : ℚ]`, and take `c = max 1 (c₀ · M^d / m^d)`.

Given `g`, apply `exists_reduction_GL` to `g⁻¹`. This gives `g⁻¹ γ = k b` with `k` bounded
unimodular and `b` upper triangular with diagonal ideles `t i` satisfying
`|t i| ≤ c₀ |t (i + 1)|`. By `exists_upperTriangular_mul_mem_standardCompact`,
`k⁻¹ = β κ` with `κ ∈ standardCompact F n`, `β` upper triangular, `β` equal to `1` at the
finite places and with diagonal norms in `[m, M]` at the infinite places. Hence
`γ⁻¹ g = p κ` with `p = b⁻¹ β` upper triangular. Its diagonal ideles are
`s i = (t i)⁻¹ u i`, where `u i` is the `i`-th diagonal entry of `β`. By
`full_bounds_of_local`, `m^d ≤ |u i| ≤ M^d`.

Let `a i` be the positive real idele with `|a i| = |s i|` (via `scalarRoot`). Then
`s i (a i)⁻¹` has norm one. The fundamental set gives `f i ∈ Fˣ` with
`ω i = f i · s i (a i)⁻¹ ∈ C`, so `s i = (f i)⁻¹ ω i a i`. Write `p = N' diag(s)` with `N'`
unitriangular. Then

`diag(f) γ⁻¹ g = (diag(f) N' diag(f)⁻¹) · diag(ω) · diag(a) · κ`.

The conjugate `N'' = diag(f) N' diag(f)⁻¹` is unitriangular. The unipotent reduction gives
a rational unitriangular `μ` with `μ N'' ∈ Ω_N`. The rational matrix
`μ · diagonalGL f · γ⁻¹` is the required one. For the chamber condition,
`|a i| = |s i| = |u i| / |t i|`, so `chamber_le` and `|t i| ≤ c₀ |t (i + 1)|` give
`|a (i + 1)| ≤ c₀ M^d / m^d · |a i| ≤ c · |a i|`.

Nothing is asserted about the size or uniqueness of the representation, about finiteness
statements of Siegel sets, or about general reductive groups.
