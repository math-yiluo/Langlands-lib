# The rank-one case of the equal-rank real-place functional equation

Intermediate result towards the proof of
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`. The module
splits the Library statement
`RealEqualFunctionalEquationStatement` by the rank index `r` and proves the case `r = 0`
(`GL₁ × GL₁`) from the Library proposition
`Langlands.LocalFactor.RealArchimedeanTateStatement` (Tate's local theory at the real
place). It does not prove `RealArchimedeanTateStatement` and does not prove the
equal-rank statement for `r > 0`; both remain explicit hypotheses of the entry
proposition. Every declaration in the module is proved, and no axioms are added.

All declarations are in the namespace `Langlands.Global.RankinSelbergGlobal`. The module
repeats the Library's local Borel measurable-space instances on `GL_(n+1)(ℝ)`,
`N_(n+1)(ℝ)` and the quotient `N_(n+1)(ℝ) \ GL_(n+1)(ℝ)` from
`ArchimedeanFunctionalEquationStatement`, so the restated body elaborates with the same
instances.

## Declarations

- `RealEqualAtRankStatement r : Prop` (a definition). It is the body of
  `RealEqualFunctionalEquationStatement` with the rank index `r` fixed: the same
  quantifiers (number field `F` in universe `u` with compact adele quotient, unitary
  additive character `ψ` trivial on `F`, cuspidal realizations `T, Td, T', Td'` of
  `GL_(r+1)` with `Td`, `Td'` contragredient to `T`, `T'`, real place `v` with
  `ψ_v = ψ_a`, real-place parameters `d, d', dd, dd'`, quotient measure `D`, archimedean
  restrictions `W` of Whittaker functions for `ψ` and `W'` for `ψ⁻¹`, Schwartz function
  `Φ` on `ℝ^(r+1)`) and the same nine conclusions: integrability of both integrands and
  holomorphy of both integrals on `Re s > σ`, meromorphic `M`, `Md` agreeing with them
  there, and the functional equation
  `L(s, d × d')⁻¹ Md(1 - s) = ω'_v(-1)^r ε(s, d × d', ψ_a) L(1 - s, dd × dd')⁻¹ M(s)`
  for `s` outside a discrete subset of `ℂ`. Only the position of `∀ r` changes: in the
  Library statement it comes after `F`, `ψ` and the triviality hypothesis.

- `realEqualFunctionalEquationStatement_iff`:
  `RealEqualFunctionalEquationStatement ↔ ∀ r, RealEqualAtRankStatement r`. Both
  directions reorder the arguments; Lean checks that the bodies agree.

- `realEqualAtRankStatement_zero`: `RealArchimedeanTateStatement` implies
  `RealEqualAtRankStatement 0`. The proof applies `RealRankZero.realEqual_rankZero_global`
  (module `RealRankZeroEqual`) with the additive character `ψ.complex`; the hypotheses
  that `ψ` is trivial on `F` and that `ψ_a` is its component at `v` are not needed.

- `RealEqualRankZeroReductionStatement : Prop` (the entry proposition):
  `RealArchimedeanTateStatement → (∀ r, 0 < r → RealEqualAtRankStatement r) →
  RealEqualFunctionalEquationStatement`, in every universe `u`.

- `realEqualRankZeroReductionStatement`: proof of the entry proposition. By
  `realEqualFunctionalEquationStatement_iff` it suffices to prove
  `RealEqualAtRankStatement r` for every `r`; for `r = 0` this is
  `realEqualAtRankStatement_zero`, for `r > 0` the second hypothesis.

## The proof of the case `r = 0`

The proof is in five helper modules, each with paired Markdown:

1. `Langlands.LocalFactor.Archimedean.RealTateZeta`: the real Tate zeta integral
   `Z(f, e, u) = ∫ f(x) sgn(x)^e |x|^(u-1) dx` of a Schwartz function, its integrability
   and holomorphy on `Re u > 0`.
2. `RealRankZeroHaar`: every quotient measure `D.measure` on `N₁(ℝ) \ GL₁(ℝ) ≅ ℝˣ` is a
   nonzero multiple of `|x|⁻¹ dx` (uniqueness of Haar measure on `ℝˣ`).
3. `RealRankZeroLocal`: if `W = C · χ_c ∘ det` and `W' = C' · χ_{c'} ∘ det`, then both
   rank-one integrals are constant multiples of real Tate zeta integrals of the line
   restriction of `Φ` and of its Fourier transform. The nine conclusions follow from
   `RealArchimedeanTateStatement` (main theorem `realEqual_rankZero`).
4. `RealRankZeroPlace`: for `GL₁` the operator algebra of a realization is commutative,
   so Schur's lemma makes compact and Lie operators scalars on an irreducible realization.
   The `GL₁` Whittaker coefficient is the cusp form itself. A realization on which `-1`
   and the Lie operator of `1` at `v` act by `χ_c(-1)` and `c.exponent` transforms by
   `χ_c ∘ det` under `GL₁(ℝ)` at `v`.
5. `RealRankZeroParameter`: through a real-place parameter `[character c]` these scalars
   are `χ_c(-1)` and `c.exponent` (test vector `χ_c ∘ det` in the standard module); the
   contragredient parameter has the same parity and the negated exponent; every
   real-place Whittaker restriction of a cuspidal realization of `GL₁` is
   `C · χ_c ∘ det`.

`RealRankZeroEqual` combines these: the parameters are single character blocks (rank
one), `W` and `W'` are multiples of characters, the contragredient parameters satisfy the
hypotheses of `realEqual_rankZero`, and `ω'_v(-1)^0 = 1`.

## Provenance

Internal intermediate result towards `RealPlaceFunctionalEquationStatement`. The case `n = n' = 1` of Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), Theorem 2.1, at a real place is Tate's
local functional equation at `ℝ` (Tate's thesis; Cassels–Fröhlich 1967, Chapter XV,
§2.4–2.5), which the Library states as `RealArchimedeanTateStatement`. The split by rank
and the reduction of the rank-one global restrictions to Tate integrals are internal to
this project.
