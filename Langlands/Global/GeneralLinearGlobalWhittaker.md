# Global Whittaker functions on `GL_n`

Module `Langlands.Global.GeneralLinearGlobalWhittaker` defines the global
Whittaker function of a function on `GL_{r+1}(𝔸)` and the objects that the
Whittaker expansion (Getz–Hahn, Theorem 11.3.6) is indexed by. Everything is
built on the actual general linear group scheme
`GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)` over
`Spec F` and on its adelic points. This is a definition module. Its only
theorem is that `N_n(𝔸)` is closed (`isClosed_upperUnipotent_adelicPoints`,
proved). The statement that uses these definitions is
`WhittakerExpansionStatement` (module
`Langlands.Global.GeneralLinearWhittakerExpansionStatement`).

## Sources

- J. Getz and H. Hahn, *An introduction to automorphic representations*
  (2024), registered as `getz-hahn-2024-automorphic-representations`
  (PDF page = printed page + 11 in Chapter 11):
  - Definition 11.2.1, p.294 (PDF page 305): a character of `N(𝔸)` trivial
    on `N(F)` is generic if its local components are nontrivial on every
    simple root group.
  - Example 11.1, pp.294–295 (PDF pages 305–306): `N_n` is the upper
    unitriangular group. For global `F`, every character of `N_n(𝔸)` that is
    trivial on `N_n(F)` has the form
    `n ↦ ψ(m_1 x_{12} + ⋯ + m_{n-1} x_{(n-1)n})` with `m_i ∈ F` and
    `ψ : F \ 𝔸 → ℂ^×` nontrivial. It is generic if and only if every `m_i` is
    nonzero, and it is the standard character when all `m_i = 1`.
  - (11.6), p.297 (PDF page 308): the global `ψ`-Whittaker function
    `W_ψ^φ(g) = ∫_{[N]} φ(ng) conj(ψ(n)) dn`. The conjugation bar was checked
    on the rendered page. It agrees with (11.7), `W(ng) = ψ(n)W(g)`.
- J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in: An
  Introduction to the Langlands Program (2004), registered as
  `cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3), §1.1,
  p.199 (PDF page 202): the character `ψ(n) = ψ(x_{1,2} + ⋯ + x_{n-1,n})` of
  `N_n` and the Whittaker function
  `W_φ(g) = ∫_{N_n(k) \ N_n(𝔸)} φ(ng) ψ⁻¹(n) dn`.
- J. A. Shalika, *The multiplicity one theorem for GL_n*, Ann. of Math. 100
  (1974), registered as `shalika-1974-multiplicity-one` (PDF page = printed
  page − 169), §5, p.187 (PDF page 18): `W_f(x) = ∫ f(ux) χ(u) du` for a
  non-degenerate character `χ` trivial on `U_k`, and p.188 (PDF page 19): the
  points `d[x] = diag(x, 1_{n-m})`.

## Definitions

- `subgroupCharacterCoefficient F G U χ f g` is
  `∫_{U(F) \ U(𝔸)} f(u g) conj(χ(u)) du`. Here `G` is an affine group scheme
  locally of finite type over `Spec F`, `U` is a subgroup functor whose adelic
  points are closed in `G(𝔸)`, and `χ` is any function on `U(𝔸)`. The domain
  of integration is the actual quotient `AdelicSubgroupPoints.RationalQuotient`
  of `U(𝔸)` by the principal image of `U(F)`, with left cosets `U(F)u`. The
  measure is `normalizedRationalQuotientHaarMeasure`, the quotient of Haar
  measure on `U(𝔸)` scaled to total mass one. It is a probability measure
  when the quotient is compact
  (`normalizedRationalQuotientHaarMeasure_isProbabilityMeasure`). The
  integrand is evaluated at the representative `Quotient.out x` of each
  class. Suppose `f` is left invariant under `U(F)` (for example a function on
  `G(F) \ G(𝔸)`) and `χ` is a character trivial on `U(F)`. Then the integrand
  does not depend on the representative, so on the quotient it equals the
  descended function `U(F)u ↦ f(ug) conj(χ(u))` pointwise. The choice of
  representatives therefore causes no measurability issue. As for every
  Bochner integral, the value is `0` when the integrand is not integrable.
- `cornerMatrix r A` is the block-diagonal matrix `diag(A, 1)` of size
  `r + 1`. It is `Matrix.fromBlocks A 0 0 1`, reindexed along
  `finSumFinEquiv : Fin r ⊕ Fin 1 ≃ Fin (r + 1)`, so `A` occupies the first `r`
  rows and columns and the last diagonal entry is `1`. It is a monoid
  homomorphism (proved), and `cornerEmbedding r = Units.map (cornerMatrix r)`
  is the embedding `γ ↦ diag(γ, 1)` of `GL_r` into `GL_{r+1}`. This is
  Shalika's `d[γ]` for `m = n - 1` and the matrix `(γ 1)` of Getz–Hahn (11.8).
- `upperUnipotentWeight n i = -i`, and `upperUnipotent F n` is the block
  unipotent subgroup functor
  `GroupScheme.GeneralLinear.blockUnipotent (Fin n) (CommRingCat.of F)` for
  these weights. Its points are the matrices that agree with the identity at
  every position `(i, j)` with `-i ≤ -j`, that is `j ≤ i`. These are the
  upper unitriangular matrices, Getz–Hahn's `N_n`. The two local instances
  supply `IsAffine` and `Smooth` for the general linear group scheme from the
  published `isAffine_groupScheme` and `smoothStatement`.
- `isClosed_upperUnipotent_adelicPoints` (proved), registered as the instance
  `upperUnipotentAdelicPointsIsClosed`: `N_n(𝔸)` is closed in `GL_n(𝔸)`. The
  functor is the range of the closed immersion `blockUnipotentHom`
  (`isRepresentedBy_blockUnipotent`, `isClosedSubgroup_blockUnipotentHom`).
  Represented closed subgroups have closed adelic points
  (`AdelicSubgroupPoints.isClosed_adelicPoints_range`).
- `genericCharacter F r ψ m` is the function
  `n ↦ ψ(m_0 n_{0,1} + ⋯ + m_{r-1} n_{r-1,r})` on `N_{r+1}(𝔸)`, for any
  function `ψ : 𝔸 → ℂ` respecting addition (`AddChar`) and any `m : Fin r → F`.
  Indices are `0`-based, so `n_{i,i+1}` is the matrix entry at
  `(i.castSucc, i.succ)` under `GeneralLinearGroupPoints.adelicEquiv`.
  Getz–Hahn's `x_{12}, …, x_{(n-1)n}` with `n = r + 1` are `1`-based. Since
  `(uu')_{i,i+1} = u_{i,i+1} + u'_{i,i+1}` for upper unitriangular `u`, `u'`,
  it is a character of `N_{r+1}(𝔸)` (not proved here). If `ψ` is trivial on
  `F` it is trivial on `N_{r+1}(F)`. The hypotheses that make it a generic
  character in the sense of Example 11.1 are stated where it is used: `ψ`
  continuous, trivial on `F` and nontrivial, and every `m i ≠ 0`. With all
  `m i = 1` it is the standard character attached to `ψ`, which is Cogdell's
  `ψ(n)`.
- `generalLinearWhittakerFunction F r ψ m f` is
  `subgroupCharacterCoefficient` for `N_{r+1}` and `genericCharacter F r ψ m`,
  that is, the global Whittaker function
  `W(g) = ∫_{N(F) \ N(𝔸)} f(ng) conj(ψ_N(n)) dn` of Getz–Hahn (11.6), with the
  measure of total mass one. For a continuous character `ψ` of the compact
  group `F \ 𝔸`, `conj ψ = ψ⁻¹`, so this is also Cogdell's formula. Shalika
  integrates against `χ` itself, which amounts to replacing `χ` by
  `conj χ`, another non-degenerate character.
- `rationalUpperUnipotent F r` is `N_r(F)`: the rational points of
  `upperUnipotent F r`, mapped into `GL_r(F)` by
  `GeneralLinearGroupPoints.rationalEquiv`.
- `UnipotentRationalCosets F r` is the quotient of `GL_r(F)` by
  `QuotientGroup.rightRel (rationalUpperUnipotent F r)`. Its classes are the
  right cosets `N_r(F)γ`, so it is Getz–Hahn's and Cogdell's index set
  `N_{n-1}(F) \ GL_{n-1}(F)` for `n = r + 1`.
- `cornerAdelicPoint F r γ` is `diag(γ, 1)` for `γ ∈ GL_r(F)`, as a point of
  the group scheme `GL_{r+1}` over `𝔸`: the principal image of
  `cornerEmbedding r γ`, transported by `GeneralLinearGroupPoints.adelicEquiv`.

## Relation to the Library

`Langlands.Automorphic.CuspidalWhittaker` (Worker 1709) constructs the
classical Whittaker coefficient on the matrix carrier `AdelicGL` as iterated
column integrals, for the proof of local genericity. Its Markdown says it
does not prove the integral formula. The present module gives the integral
definition on the group-scheme carrier. The two function spaces are compared
by `continuousGeneralLinearEquiv`. That machinery may help in proving the
expansion.
