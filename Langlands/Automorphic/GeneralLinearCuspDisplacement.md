# Small right translates of deep unipotent orbits in the adelic quotient

This module proves that a continuous cusp function on the positive rational
quotient of adelic `GL_n` is controlled, away from one compact set, by its
oscillation under small right translations.

## Setting

Let `F` be a number field, `n : ℕ` and
`G = GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)`.
Fix the parabolic–cocharacter theorem `hPD`, connected reductivity `hG`
and the positive-central data `T`, `i`, `hi`, `I`, `e` and `hc`. Write
`A = AdelicGroupPoints F G`, `Γ = positiveRationalSubgroup F G T i`,
`Q = PositiveRationalQuotient F G T i` and `q · a` for
`LeftCosetSpace.rightTranslate Γ a q`.

## Statement

`exists_compact_cuspDisplacementCover`: assume `0 < n` and let `U` be a
neighborhood of `1` in `A`. There is a compact `D ⊆ Q` with the following
property. Let `ψ : C(Q, ℂ)` be such that
`positiveQuotientContinuousPullback F G T i ψ` lies in
`normalizedParabolicCuspidalSubrepresentation F G hPD hG`. If `q ∉ D`
and `‖ψ q - ψ (q · a)‖ ≤ M` for every `a ∈ U`, then `‖ψ q‖ ≤ M`.

## Proof

The private lemma `norm_le_of_matrixConstantTerm_zero` is the mean-value
step. Let `f` be a continuous rational function on `GL_n(𝔸_F)` satisfying
`Langlands.Automorphic.IsCuspidal`, let `a + b = n` with `a, b > 0`, and
suppose `‖f g - f (u(Y) g)‖ ≤ M` for every `Y ∈ M_{a×b}(𝔸_F)`, where
`u(Y)` is `Langlands.GeneralLinear.blockUnipotent`. Then `‖f g‖ ≤ M`.
The block constant term of `f` at `g` vanishes, and `matrixQuotientHaar`
is a probability measure, so `f g` is the integral of
`f g - f (u(X) g)` over the compact quotient `M_{a×b}(F \ 𝔸_F)`. The
integrand is integrable by `integrable_constantTermIntegrand` and bounded
by `M`.

For the statement, transport `U` through
`GeneralLinearGroupPoints.adelicHomeomorph` and `AdelicGL.pair`. This gives
an open archimedean neighborhood `U∞` of `1` and an open subgroup `L` of
`GL_n` of the finite adeles whose products lie in `U`. The subgroup comes
from the nonarchimedean structure `finiteAdelicGL_nonarchimedeanGroup`.
`OperatorRealization.exists_cusp_cover`, in
`Langlands.Automorphic.CuspidalAdmissible.Finiteness`, applied to `L` and
`U∞`, gives a compact `Ω` of adelic matrices. Up to rational left
translation and the central torus, every adelic matrix lies in `Ω` or is
absorbed along a maximal block (`OperatorRealization.CuspAbsorbed`).

Let `d = [F : ℚ] · n`, `c g = -log |det g| / d`, and let
`p g = [g · centralTorus F n (c g)] ∈ Q`. The map `p` is continuous, and
`D = p(Ω)` is compact. Given `q`, choose a representative `x` of norm
one, using surjectivity of `positiveQuotientHomeomorph`. The cusp cover
gives a rational `γ`, `t : ℝ` and `z` with `γ x = z · centralTorus F n t`.

- If `z ∈ Ω`, then `|det x| = 1`, `absDet_centralTorus` and
  `absDet_rational_mul` force `t = c z`, so `q = p z ∈ D`. This case
  contradicts `q ∉ D`.
- If `z` is absorbed along a block `a + (n - a) = n`, set
  `z' = z · centralTorus F n t`, a representative of `q`. The function
  `continuousGeneralLinearEquiv F n` of the pullback of `ψ` is cuspidal
  in the matrix sense, by
  `mem_normalizedGeneralLinearParabolicCuspidal_iff`. For every `Y` the
  absorption, together with centrality of the torus
  (`centralTorus_commute`), writes `u(Y) z'` as a rational element times
  `z'` times an element of `U`. Rational elements lie in `Γ`
  (`rationalSubgroup_le_positiveRationalSubgroup`). Hence the value of
  this function at `u(Y) z'` is `ψ (q · a)` for some `a ∈ U`, and the
  mean-value step gives `‖ψ q‖ ≤ M`.

## Provenance

The cusp cover is the reduction-theory input of the Library's sup-norm
finiteness argument for cusp forms in
`Langlands.Automorphic.CuspidalAdmissible.Finiteness`. This module's
statement is internal: it combines that cover with the vanishing of
constant terms, rather than with the rapid-decay estimate of Getz–Hahn,
*An Introduction to Automorphic Representations* (2024),
Proposition 9.4.7 (printed p. 257).
