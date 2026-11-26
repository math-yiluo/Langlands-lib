# The Levi Whittaker coefficient of a twisted section

Module `Langlands.Global.Factors.CuspidalPairEisensteinOneplace`, namespace
`Langlands.Global.CuspidalPairEisenstein.Oneplace`.

Let `P = M U` be the upper two-block parabolic of `GL_(r+t+2)` (`blockShape r t`), `φ` a
section in the sense of `CuspidalPairEisenstein.IsSection T T' φ`, and
`φ_s = φ · H^s` the section twisted by Shahidi's power `H^s = δ_P^(s/(r+t+2))`
(`heightPower`). The module computes the generic Whittaker coefficient `W_M(φ_s)` along the
Levi (`leviWhittaker`, see [CuspidalPairEisensteinOpenCell.md](CuspidalPairEisensteinOpenCell.md))
at Levi translates, and its behaviour under a Levi element supported at one unramified finite
place.

## Content

### Invariance of `H^s` and of `W_M`

- `twisted φ s = φ · H^s`.
- `exists_parabolic_factor'`: every adelic `g` is `p k` with `p ∈ P(𝔸)` and `k` in the standard
  maximal compact subgroup (from `exists_isStandardIwasawaFactorization`).
- `heightPower_mul_compact`, `heightPower_unipotent_mul`, `heightPower_levi_mul`: `H^s` is right
  invariant under the standard maximal compact subgroup, left invariant under `U(𝔸)`, and
  `H^s(m k) = exp(s/(r+t+2) · log δ_P(m))` (from `heightPower_eq` and
  `parabolicCharacter_section`, `parabolicCharacter_unipotent`).
- `leviWhittaker_mul_right`, `leviWhittaker_mul_right_of_invariant`: right translation commutes
  with `W_M`.
- `leviPair_conj_mem`, `levi_conj_mem`: Levi elements normalize `U(𝔸)`;
  `leviWhittaker_unipotent_mul`: `W_M(f)` is left `U(𝔸)`-invariant when `f` is;
  `twisted_unipotent_mul`: `φ_s` is left `U(𝔸)`-invariant (the corresponding clause of
  `IsSection` and `heightPower_unipotent_mul`).
- `parabolic_eq_unipotent_mul_levi`, `unipotentPart_mem` and
  **`leviWhittaker_levi_mul_parabolic`**: `W_M(φ_s)(m p k) = W_M(φ_s)(m m_p k)`, where `m_p` is
  the Levi part of `p ∈ P(𝔸)`.

### The Levi characters

- `leviOf x z = diag(x, z)` as an adelic Levi element, `leviPair_eq_leviEmbedding`,
  `leviPair_mul_levi`; `leviFst`, `leviSnd` (the two blocks).
- `leviCharacter_leviOf`: `δ_P(diag(x, z)) = |det x|^(t+1) / |det z|^(r+1)`;
  `leviCharacter_leviOf_of_det`, `determinantNorm_unipotentAdelic`,
  `leviCharacter_leviOf_unipotent_mul`: `δ_P` is unchanged under left multiplication by a
  pair of upper unitriangular adelic matrices; `leviHalfCharacter_eq_of_leviCharacter_eq`.
- `levFactor s m = δ_P(m)^(1/2) · exp(s/(r+t+2) · log δ_P(m))`, the factor
  `δ_P^(1/2 + s/(r+t+2))`; `levFactor_unipotent_mul`, `levFactor_mul` (multiplicativity).

### Slices and the Levi formula

- `IsSliceSum T T' φ k I c ξ₁ ξ₂`: at `k`, the normalized Levi slice
  `m ↦ δ_P(m)^(-1/2) φ(m k)` is `∑_(i ∈ I) c_i ξ₁ᵢ(m₁) ξ₂ᵢ(m₂)` for cusp forms `ξ₁ᵢ` of `T` and
  `ξ₂ᵢ` of `dualRealization T'`. `exists_isSliceSum`: a section built from cusp forms spherical
  outside `S` (`IsSphericalSectionOutside`) has such a sum at every `k` of the standard
  maximal compact subgroup, with vectors spherical outside `S`.
- `twisted_levi_mul`: `φ_s(m k) = levFactor s m · ∑_i c_i ξ₁ᵢ(m₁) ξ₂ᵢ(m₂)`.
- `whittaker_eq_sum`: the Library global Whittaker coefficient of a function that is a finite
  combination `∑_i d_i ξ_i(u G)` on `N(𝔸)` is `∑_i d_i W_(ξ_i)(G)`, with `W_ξ` the cusp
  Whittaker function `cuspWhittaker`.
- **`leviWhittaker_levi_mul`**: for an adelic Levi element `m = diag(m₁, m₂)`,
  `W_M(φ_s)(m k) = levFactor s m · ∑_i c_i W_(ξ₁ᵢ)(m₁) W_(ξ₂ᵢ)(m₂)`.

### One unramified place

- `comp F n v g`: the component at the finite place `v` of an adelic matrix; `comp_apply`;
  `comp_leviFst_mem`, `comp_leviSnd_mem`: the blocks of a parabolic element integral at `v`
  are integral at `v`; `comp_mem_localIntegral_of_mem_standardCompact`.
- **`cuspWhittaker_localPoint_mul`**: for a cusp form `x` spherical outside `S`, `v ∉ S`, a
  point `g` integral at `v` and `h ∈ GL_(n+1)(F_v)`, `W_x(ι_v(h) g) = W°(h; a) W_x(g)`, where
  `a` is the Satake tuple of the presentation at `v` and `W°` the spherical Whittaker
  function. It is derived from the Library theorem
  `UnramifiedWhittaker.unramifiedWhittakerFactorization`, which states the case of a point
  with component `1` at `v`, by moving the component of `g` at `v` into the local argument
  and using the right `GL_(n+1)(𝒪_v)`-invariance of `W°`.
- `localLevi F r t v m₁ m₂`: the adelic Levi element with blocks `m₁`, `m₂` at `v` and `1`
  elsewhere; `determinantNorm_localInclusion`, `leviCharacter_localLevi`
  (`δ_P(localLevi v m₁ m₂)` is the local modulus `Shahidi.twoBlockModulus`),
  `twoBlockModulus_pos`, `levFactor_localLevi`
  (`levFactor s (localLevi v m₁ m₂) = δ_P(m₁, m₂)^(1/2 + s/(r+t+2))`).
- **`leviWhittaker_localLevi_mul`**: for a section built from cusp forms spherical outside
  `S`, a place `v ∉ S` where the component `ψ_v` of `ψ` is integrally trivial in the sense of
  the hypotheses `hθ₁`, `hθ₂`, Satake tuples `a` of `P` and `c` of `Pd` at `v`, a point `g`
  integral at `v` and local blocks `m₁`, `m₂`:
  `W_M(φ_s)(ι_v(diag(m₁, m₂)) g) = leviValue(m₁, m₂) · W_M(φ_s)(g)`, where
  `leviValue(m₁, m₂) = δ_P(m₁, m₂)^(1/2 + s/(r+t+2)) W°(m₁; a) W°(m₂; c)` is
  `Shahidi.UnramifiedSection.leviValue`
  (see [UnramifiedOpenCellSection.md](../../Representation/Shahidi/UnramifiedOpenCellSection.md)).
- `finiteComponent_symm`, `symm_leviFst_localLevi_mul`, `symm_leviSnd_localLevi_mul`,
  `alg_aux₁`, `alg_aux₂`: bookkeeping identities used in that proof.

## Proof of `leviWhittaker_localLevi_mul`

Write `g = p k` (`exists_parabolic_factor'`) with `p ∈ P(𝔸)` integral at `v` and `k` in the
standard maximal compact subgroup, and let `m_p` be the Levi part of `p`. By
`leviWhittaker_levi_mul_parabolic`, both sides are values of `W_M(φ_s)` at Levi elements times
`k`: `ι_v(diag(m₁, m₂)) m_p k` and `m_p k`. Take a slice sum at `k` with vectors spherical
outside `S` (`exists_isSliceSum`) and apply `leviWhittaker_levi_mul` to both. The factor
`levFactor` is multiplicative, and its value at `localLevi v m₁ m₂` is
`δ_P(m₁, m₂)^(1/2 + s/(r+t+2))`. In each term, the cusp Whittaker functions of the two blocks
at `ι_v(m_j) m_(p,j)` are `W°(m_j) W(m_(p,j))` by `cuspWhittaker_localPoint_mul`, since the
blocks `m_(p,j)` are integral at `v` (`comp_leviFst_mem`, `comp_leviSnd_mem`). The product
`W°(m₁; a) W°(m₂; c)` factors out of the finite sum.

## Provenance

The computation is the global part of the proof of Shahidi (1981), Theorem 5.1, pp. 351–352
(`shahidi-1981-certain-l`): for a section induced from cusp forms and `v` outside the
ramification, the Whittaker coefficient of the Levi slices factors at `v` through the
spherical Whittaker functions of the local components, normalized to be `1` at the identity
(Shahidi (1981), p. 352). The organization into the lemmas above is internal.
