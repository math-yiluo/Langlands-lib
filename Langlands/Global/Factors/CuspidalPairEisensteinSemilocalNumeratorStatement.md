# The semilocal numerator of the open-cell integral

`Langlands.Global.CuspidalPairEisensteinSemilocalNumeratorStatement.{u}` (module
`Langlands.Global.Factors.CuspidalPairEisensteinSemilocalNumeratorStatement`) is a
Prop-valued statement. The module states it and does not prove it.

It is the part of the proof of Shahidi (1981), Theorem 5.1, at the finitely many omitted
finite places and at the archimedean places, for the upper two-block parabolic of
`GL_(r+t+2)` with inducing data `π ⊗ (π')^∨`. It is written for the partial open-cell
integral `partialOpenCellIntegral` of
[CuspidalPairEisensteinPartialOpenCell.md](CuspidalPairEisensteinPartialOpenCell.md).

## Statement

Let `F : Type u` be a number field with `[CompactSpace (AdeleQuotient F)]`, let `T`, `T'` be
actual cuspidal realizations of `GL_(r+1)` and `GL_(t+1)` with unitary central characters,
let `ψ : AddChar (Adeles F) ℂ` satisfy `RankinSelbergGlobal.IsStandardAdditiveCharacter`
(continuous, nontrivial, unitary and trivial on `F`), and let `S` be a finite set of finite
places. Then there is a finite set `S₀` of finite places with `S ⊆ S₀` such that for every
`s₀ : ℂ` with `Re s₀ = 0` there are

- a function `φ` on `GL_(r+t+2)(𝔸)` with `CuspidalPairEisenstein.IsSection T T' φ` and
  `CuspidalPairEisenstein.IsSphericalSectionOutside T T' S₀ φ` (a section built from cusp
  forms spherical outside `S₀`), and
- a function `c : ℂ → ℂ`, meromorphic on `ℂ`, analytic at `s₀` with `c s₀ ≠ 0`,

and a real `σ` with `c s = partialOpenCellIntegral ψ S₀ φ s` for every `s` with `σ < Re s`.

The set `S₀` is chosen before `s₀`; the section `φ`, the function `c` and the half-plane may
depend on `s₀`. The statement involves no spectral presentation. The equality is between
`c` and the Bochner integral `I_(S₀)(φ, s)`; it carries no separate convergence claim.

## Source

F. Shahidi, *On certain L-functions*, Amer. J. Math. 103 (1981) (`shahidi-1981-certain-l`):

- Proof of Theorem 5.1, pp. 351–352 (PDF pages 56–57). For a factorizable section
  `φ = ⊗_v φ_v` the local factor `W_v(e_v)` is the value of the local Whittaker functional
  `λ_v` fixed on p. 351 on the extension of the local vector `φ_v`. For `v ∈ S` (Shahidi's `S` contains the archimedean places) this factor continues
  analytically by Proposition 3.2 at archimedean `v` and by Proposition 3.1 at finite `v`,
  and by these propositions the local section vector `φ_v` (and hence its extension to the
  induced space) may be chosen so that `W_v(e_v) ≠ 0` (p. 352). The functional itself is
  not changed by this choice.
- Proposition 3.1, p. 332 (PDF page 37): over a non-archimedean field the Jacquet–Whittaker
  integral `∫_(N') ⟨f(n' w_θ), e⟩ conj(χ(n')) dn'` converges, is entire in the induction
  parameter, and for every parameter some `f` gives a nonzero value. Here `w_θ` is the Weyl
  element defined in the paragraph preceding the proposition, `N'` is the unipotent radical
  of the standard parabolic `P' = M'N'` with `M' = M_(w_θ(θ))`, and `⟨f(g), e⟩` is the value at the Levi identity `e`
  of the Whittaker function `f(g)`.
- Proposition 3.2, p. 333 (PDF page 38): over an archimedean field and for fine inducing
  data, the Whittaker functional obtained by analytic continuation of the Jacquet integrals
  is entire in the parameter.
- Example after Theorem 4.1, p. 344 (PDF page 49): for `G = GL_(n+m)` and
  `M = GL_n × GL_m` the local components of a cuspidal representation are unitary, hence
  fine at every archimedean place.

In the statement, `I_(S₀)(φ, s)` is the open-cell integral over the adelic matrices that are
integral at every finite place outside `S₀`. Let `φ` be factorizable, built from cusp forms
spherical outside `S₀`, and let the finite components of `ψ` outside `S₀` have conductor
`𝒪_v`. At each finite `v ∉ S₀` the factor of the integrand on `M(𝒪_v)` is then constant,
equal to the value `⁰W_v(e_v)` at the identity of the Levi Whittaker function of the
spherical inducing data. If, as in Shahidi (p. 352), the spherical inducing vectors `φ_v`
are normalized so that `⁰W_v(e_v) = 1` for `v ∉ S₀`, this factor is `1`, and `I_(S₀)(φ, s)` is, up to a positive constant from the Haar
normalization, Shahidi's semilocal product `∏_(v ∈ S₀ ∪ ∞) W_v(e_v)`. In another
normalization of the spherical data the factors are scalars `⁰W_v(e_v)`, whose
product is absorbed into the local data at the places of `S₀` and the archimedean places.
The function `c` is the meromorphic continuation of `I_(S₀)(φ, s)`.

## Comparison with the source

- The set `S₀` is existential and may be enlarged beyond `S`. This leaves room to include
  the finite places where `ψ_v` does not have conductor `𝒪_v` and the places where the
  local components of `T` and `T'` or the chosen cusp forms are ramified, as in Shahidi's
  choice of `S` on p. 351.
- The finite places of `S₀` and the archimedean places are treated together: `c` is the
  continuation of the whole semilocal integral. Shahidi obtains it as the finite product of
  the local values for a factorizable section.
- The statement asks for meromorphy of `c` on all of `ℂ`, regularity and nonvanishing at
  `s₀`. Shahidi's Propositions 3.1 and 3.2 give entire local factors.
- The hypothesis of unitary central characters gives unitary cuspidal components, which is
  the case of the Example on p. 344.
