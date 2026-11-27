# The archimedean numerator of the open-cell integral

Module `Langlands.Global.Factors.CuspidalPairEisensteinArchimedeanNumeratorStatement`.

The module defines the archimedean part of the open-cell integral of
[CuspidalPairEisensteinPartialOpenCell.md](CuspidalPairEisensteinPartialOpenCell.md) and
states `Langlands.Global.CuspidalPairEisensteinArchimedeanNumeratorStatement.{u}`, a
Prop-valued statement. The module states it and does not prove it.

## Definitions

In namespace `Langlands.Global.CuspidalPairEisenstein`, for a number field `F` and ranks
`r t : ℕ`:

- `archimedeanMatrix F r t X`: for `X ∈ M_((t+1)×(r+1))(F_∞)` (`InfiniteAdeles F`), the
  adelic matrix with entries `(X_(ij), 0)`: archimedean component `X` and component `0` at
  every finite place.
- `archimedeanOpenCellHaar F r t`: a Haar measure (`Measure.addHaar`) on the additive group
  `M_((t+1)×(r+1))(F_∞)` for its Borel σ-algebra, which is not made an instance.
- `archimedeanOpenCellIntegrand ψ φ s X = openCellIntegrand ψ φ s (archimedeanMatrix F r t X)`,
  that is `W_M(φ_s)(w u'(X, 0)) conj(ψ(X_(t,0), 0))` in the notation of `openCellIntegrand`.
- `archimedeanOpenCellIntegral ψ φ s`: the Bochner integral of
  `archimedeanOpenCellIntegrand ψ φ s` for `archimedeanOpenCellHaar F r t`.

## Statement

Let `F : Type u` be a number field with `[CompactSpace (AdeleQuotient F)]`, let `T`, `T'` be
actual cuspidal realizations of `GL_(r+1)` and `GL_(t+1)` with unitary central characters
(`HasUnitaryCentralCharacter`), and let `ψ : AddChar (Adeles F) ℂ` satisfy
`RankinSelbergGlobal.IsStandardAdditiveCharacter F ψ`. Then there is a finite set `S₁` of
finite places such that for every `s₀ : ℂ` with `Re s₀ = 0` there are

- a function `φ` on `GL_(r+t+2)(𝔸)` with `CuspidalPairEisenstein.IsSection T T' φ` and
  `CuspidalPairEisenstein.IsSphericalSectionOutside T T' S₁ φ`, and
- a function `c : ℂ → ℂ`, meromorphic on `ℂ`, analytic at `s₀` with `c s₀ ≠ 0`,

and a real `σ` such that for every `s` with `σ < Re s` the function
`archimedeanOpenCellIntegrand ψ φ s` is integrable for `archimedeanOpenCellHaar F r t` and
`c s = archimedeanOpenCellIntegral ψ φ s`.

The set `S₁` is chosen before `s₀`; `φ`, `c` and `σ` may depend on `s₀`.

## Source

F. Shahidi, *On certain L-functions*, Amer. J. Math. 103 (1981) (`shahidi-1981-certain-l`):

- Proof of Theorem 5.1, pp. 351–352 (PDF pages 56–57). For a factorizable section
  `φ = ⊗_v φ_v` the Fourier coefficient is the product `∏_v W_v(g_v)` of local Whittaker
  values (p. 351). At an archimedean place the local component converges absolutely for
  `Re s` large, being dominated by the corresponding intertwining integral; for `Re s` large
  it coincides with the local Whittaker functional `λ_v` fixed on p. 351, and its analytic
  continuation follows from Proposition 3.2. By Propositions 3.1 or 3.2 the local data at
  the places of `S` (which contains the archimedean places) may be chosen with
  `W_v(e_v) ≠ 0` (p. 352).
- Proposition 3.2, p. 333 (PDF page 38): over an archimedean field and for fine inducing
  data, the Whittaker functional given by analytic continuation of the Jacquet integrals is
  entire in the induction parameter.
- Example after Theorem 4.1, p. 344 (PDF page 49): for `G = GL_(n+m)` and
  `M = GL_n × GL_m` the local components of a unitary cuspidal representation are fine at
  the archimedean places.

The statement is this archimedean part of the proof, written for the open-cell integrand
restricted to the matrices `(X, 0)` with vanishing finite components. For a factorizable
section the integrand at `(X, 0)` is the archimedean integrand
`W_∞(φ_(∞,s))(w u'(X)) conj(ψ_∞(X_(t,0)))` times the product over the finite places of the
local values at `w` of the finite components. These values do not depend on `s`, since `w`
lies in the maximal compact subgroup, and they equal `1` at the places where the finite
components are the normalized spherical vectors. The integral over `M_((t+1)×(r+1))(F_∞)` is
then a constant times Shahidi's archimedean local component. The constant and the Haar
normalization are absorbed into `c`.

## Comparison with the source

- Shahidi treats each archimedean place separately; here the archimedean places are taken
  together through the product `F_∞` of the archimedean completions, and the finite
  components enter through the value of the global integrand at matrices with vanishing
  finite part.
- The statement asks for a meromorphic `c` on `ℂ`, regular and nonzero at `s₀`; Shahidi's
  continuation is entire.
- The integrability for `Re s` large is Shahidi's absolute convergence of the archimedean
  local component (p. 352).
- The set `S₁` is existential and chosen before `s₀`: it can contain the finite places where
  the chosen cusp forms are ramified, as in Shahidi's choice of `S` on p. 351.
