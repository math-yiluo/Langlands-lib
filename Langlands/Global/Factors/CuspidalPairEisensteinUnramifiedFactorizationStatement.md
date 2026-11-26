# Unramified factorization of the open-cell integral

`Langlands.Global.CuspidalPairEisensteinUnramifiedFactorizationStatement.{u,uQ}` (module
`Langlands.Global.Factors.CuspidalPairEisensteinUnramifiedFactorizationStatement`) is a
Prop-valued statement. The module states it and does not prove it.

It is the unramified half of the proof of Shahidi (1981), Theorem 5.1, for the upper
two-block parabolic of `GL_(r+t+2)` with inducing data `π ⊗ (π')^∨`, written for the
open-cell integral `openCellIntegral` of
[CuspidalPairEisensteinOpenCell.md](CuspidalPairEisensteinOpenCell.md) and the partial
open-cell integral `partialOpenCellIntegral` of
[CuspidalPairEisensteinPartialOpenCell.md](CuspidalPairEisensteinPartialOpenCell.md).

## Statement

Let `F : Type u` be a number field with `[CompactSpace (AdeleQuotient F)]`, let `T`, `T'` be
actual cuspidal realizations of `GL_(r+1)` and `GL_(t+1)` with unitary central characters,
and let `P`, `P'` be spectral presentations of them in the factor universe `uQ`. Let `Pd` be
a spectral presentation of the contragredient realization `dualRealization T'` (the
realization of `(π')^∨` used by the sections). Let `S` be a finite set of finite places with
`P.exceptional ⊆ S`, `P'.exceptional ⊆ S` and `Pd.exceptional ⊆ S`. Let
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)` be trivial on `F`, with
`FunctionalEquationComparison.FiniteAdditiveSupport ψ S`: at every finite place `v ∉ S` the
canonical component `ψ_v` exists and has additive conductor `0`, that is, conductor `𝒪_v`.

Then for every `φ` with `CuspidalPairEisenstein.IsSection T T' φ` and
`CuspidalPairEisenstein.IsSphericalSectionOutside T T' S φ` (a section built from cusp forms
spherical outside `S`) there is a real `σ` such that for every
`s` with `σ < Re s` for which `openCellIntegrand ψ.complex φ s` is integrable for
`openCellHaar F r t`,

`partialEulerProduct P P' hP hP' (1 + s) * openCellIntegral ψ.complex φ s =
  partialOpenCellIntegral ψ.complex S φ s`.

The integrability is a hypothesis; on a right half-plane it is the statement
`CuspidalPairEisensteinOpenCellConvergenceStatement`
([CuspidalPairEisensteinOpenCellConvergenceStatement.md](CuspidalPairEisensteinOpenCellConvergenceStatement.md)).

In formulas, `L^S(1 + s, π × π') · I(φ, s) = I_S(φ, s)`, where
`L^S(w, π × π') = ∏_(v ∉ S) L(w, π_v × π'_v)` is
`RankinSelbergGlobal.partialEulerProduct` of the two original presentations (the
unconditional product of `partialEulerFactor`, which by
`RankinSelbergGlobal.exists_partialEulerFactor_convergence` converges absolutely on a right
half-plane), `I(φ, s)` is the open-cell integral and `I_S(φ, s)` is the open-cell integral
over the matrices integral outside `S`. The half-plane may depend on `φ`.

## Source and normalizations

F. Shahidi, *On certain L-functions*, Amer. J. Math. 103 (1981) (`shahidi-1981-certain-l`),
proof of Theorem 5.1, pp. 351–352 (PDF pages 56–57). For a factorizable section the Fourier
coefficient is `∏_v W_v(e_v)` for `Re s` large (p. 351), and "it is a result of W. Casselman
and J. A. Shalika [3] that for every `v ∉ S`, `W_v(e_v) = ∏_j L(1 + a_j s, π_v, r_j)⁻¹`"
(p. 352). For `v ∉ S`, Shahidi normalizes the spherical inducing vector `φ_v` so that
`⁰W_v(e_v) = 1` (p. 352): `⁰W_v(e_v)` is the value at the identity of the Levi Whittaker
function of `φ_v`, and with this normalization the value `W_v(e_v)` of the local
Jacquet–Whittaker functional `λ_v` of p. 351 on the extension of `φ_v` is the reciprocal
Euler factor. For spherical data multiplied by a scalar both
values are multiplied by it. The local result is W. Casselman and J. Shalika, *The unramified principal
series of p-adic groups II. The Whittaker function*, Compositio Math. 41 (1980)
(`casselman-shalika-1980-whittaker`), Theorem 5.4, p. 227 (PDF page 22): the Jacquet
integral of the normalized spherical vector of an unramified principal series at the
identity is the product over the positive roots `α` of `1 − q^(−1) χ(a_α)`. For a section
induced in stages from the Levi `M`, with the Levi Whittaker functional normalized to be
`1` on the spherical vector of the Levi, the factors of the positive roots of `M` cancel
and the factors of the roots of the unipotent radical remain (Shahidi (1981), p. 352).

For `GL_(r+t+2)` and the Levi `GL_(r+1) × GL_(t+1)` there is one representation `r_1`, the
action of the dual Levi on the Lie algebra of the dual unipotent radical,
`Std_(r+1) ⊗ Std_(t+1)^∨`, with `a_1 = r + t + 2` (Shahidi (1981), §2.3, pp. 324–325). The
section is twisted by `heightPower`, the power `δ_P^(s/(r+t+2))` of the modulus character
`δ_P(diag(m_1, m_2)) = |det m_1|^(t+1) |det m_2|^(−(r+1))`, so Shahidi's `1 + a_1 z` is
`1 + s`. With the inducing block `(π'_v)^∨` in the second block, whose Satake parameters
are the inverses `b_j^(−1)` of those of `π'_v`, each root crossing the two blocks gives the
factor `1 − a_i b_j q_v^(−1−s)`. So at every finite `v ∉ S` the local factor is
`L(1 + s, π_v × π'_v)⁻¹ = ∏_(i,j) (1 − a_i b_j q_v^(−1−s))`, the reciprocal of
`partialEulerFactor P P' hP hP' v (1 + s)`. The multisets `a`, `b` are the spectra that
`P`, `P'` supply at `v` (`HasSphericalHeckeSpectrum`, normalized as recorded in the
Markdown of `CuspidalPairEisensteinCoefficientStatement`). For `r = t = 0` the local factor
can be checked directly: `w u'(y) = [[0, 1], [1, y]]` has Levi part `diag(y⁻¹, y)` for
`|y|_v > 1`, and the sum of the integrand over `y ∈ F_v / 𝒪_v` is
`1 − a b q_v^(−1−s)`, because `∑_(|y| = q_v) conj ψ_v(y) = −1` and the sums over the shells
`|y| = q_v^k`, `k ≥ 2`, vanish.

For a factorizable section whose spherical inducing vectors `φ_v` are normalized as in
Shahidi so that `⁰W_v(e_v) = 1` at the finite `v ∉ S`, the integrand factor at each such `v` is `1` on the set `U_S` of
`partialOpenCellIntegral` (see
[CuspidalPairEisensteinPartialOpenCell.md](CuspidalPairEisensteinPartialOpenCell.md)), and
the statement is the identity
`I(φ, s) = (∏_(v ∉ S) L(1 + s, π_v × π'_v)⁻¹) · I_S(φ, s)`, multiplied by the absolutely
convergent nonzero product `L^S(1 + s, π × π')`. For spherical data normalized otherwise
the factor at `v` on `M(𝒪_v)` is the scalar `⁰W_v(e_v)`, and the full integral at `v` is
`⁰W_v(e_v) · L(1 + s, π_v × π'_v)⁻¹` by homogeneity. The statement compares the integrals
`I` and `I_S` of the same section, so these scalars occur on both sides and the identity
needs no normalization of the spherical data; this is also why it can be stated for every
section built from cusp forms spherical outside `S`, factorizable or not.

The measure normalization is that of the global measure `openCellHaar` on both sides: no product decomposition of the measure
appears in the statement, and the local factors are those of the normalization
`vol(M_((t+1)×(r+1))(𝒪_v)) = 1`.

## Deviations from the source

- Shahidi's set `S` contains the archimedean places. Here `S` is a set of finite places; the
  archimedean places are inside `I_S`, where no condition is imposed.
- Shahidi factors the coefficient of a factorizable section into the local values
  `W_v(e_v)` of the functionals `λ_v` on the extensions of the local vectors `φ_v`. The
  statement makes no factorization assumption: it is stated for every section spherical
  outside `S`. Both sides are linear in `φ`, and the unramified factor depends only on the
  local components at `v ∉ S`.
- The statement is the multiplied form of the identity, with the partial integral `I_S` in
  place of Shahidi's semilocal product `∏_(v ∈ S) W_v(e_v)`.
- The hypotheses of unitary central characters are those of
  `CuspidalPairEisensteinLocalNumeratorStatement`.
- The presentation `Pd` of the contragredient realization does not enter the conclusion. It
  supplies spherical Hecke spectra of the second inducing block at the places outside `S`.
  At such places these are the inverses of the spectra of `P'`: this is the content of the
  Library module `Langlands.Automorphic.ContragredientSphericalSpectrum`, which proves that
  contragredient cuspidal realizations have inverse spherical spectra wherever both are
  presented. A presentation of `dualRealization T'` exists by
  `Automorphic.cuspidalDualPresentationExistence`; its exceptional set can be added to `S`.
- The section is required to be built from cusp forms spherical outside `S`
  (`IsSphericalSectionOutside`), not only to be right invariant under `GL(𝒪_v)` for
  `v ∉ S`. This is the form in which Shahidi's factorizable sections are given.
