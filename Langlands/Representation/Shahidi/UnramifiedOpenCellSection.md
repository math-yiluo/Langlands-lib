# The normalized spherical section of the two-block induced representation

Module `Langlands.Representation.Shahidi.UnramifiedOpenCellSection`, namespace
`Langlands.Shahidi.UnramifiedSection`.

Let `K` be a `p`-adic field (`PadicField p`) with its canonical valuation, ring of integers `𝒪`
and residue cardinality `q`, and let `P = M U` be the upper two-block parabolic of
`GL_((r+1)+(t+1))(K)` (`shape r t`, the two-block shape `twoBlocks (r+1) (t+1)`). The module
constructs the function `sectionFunction` that satisfies the hypothesis of
`Shahidi.UnramifiedOpenCellSumStatement`
([UnramifiedOpenCellSumStatement.md](UnramifiedOpenCellSumStatement.md)): the normalized
spherical vector of the representation induced from `W°(·; a) ⊗ W°(·; c) ⊗ δ_P^(s/(r+t+2))`,
in its Whittaker model along the Levi.

## Content

- `integralGroup K r t`: the integral matrices `GL_((r+1)+(t+1))(𝒪)`
  (`Conductor.integralSubgroup` of the canonical integers); `mem_integralGroup_iff` (entries
  of `k` and `k⁻¹` integral).
- `mem_parabolic_of_upperTriangular` and `exists_parabolic_mul`: every
  `x ∈ GL_((r+1)+(t+1))(K)` is `g k` with `g ∈ P` and `k` integral. The proof uses the
  Library Iwasawa decomposition `GeneralLinear.Iwasawa.exists_iwasawa` (upper unitriangular
  times torus times integral) and a uniformizer `ϖ`.
- `leviFirst`, `leviSecond`: the diagonal blocks of an element of `P`, with
  `leviFirst_apply`, `leviSecond_apply` (entries) and multiplicativity `leviFirst_mul`,
  `leviSecond_mul`, `leviFirst_inv`, `leviSecond_inv`; `levi_mem_integral`: the blocks of an
  integral element of `P` are integral.
- `upperP X` (the radical matrix `u(X)` as an element of `P`) and `leviP m₁ m₂` (the
  block-diagonal matrix `diag(m₁, m₂)`), with `leviP_val`, `leviFirst_leviP`,
  `leviSecond_leviP`, `leviFirst_upperP`, `leviSecond_upperP`.
- `leviValue hϖ ψ a c s m₁ m₂ =
  δ_P(m₁, m₂)^(1/2 + s/(r+t+2)) · W°(m₁; a) · W°(m₂; c)`, where
  `δ_P(m₁, m₂) = |det m₁|^(t+1) / |det m₂|^(r+1)` is `Shahidi.twoBlockModulus` and `W°` is the
  Library spherical Whittaker function `GeneralLinear.Spherical.sphericalWhittaker` for the
  standard character of `ψ`. `leviValue_mul_integral`: it is unchanged under right
  multiplication of `m₁`, `m₂` by integral matrices, when `ψ` has conductor `𝒪`
  (`isIntegrallyTrivial_of_conductor`, `twoBlockModulus_mul_integral`,
  `determinantNorm_mul_integral`). `leviValue_one`: its value at `(1, 1)` is `1`.
- `sectionFunction hϖ ψ a c s x`: `leviValue` of the diagonal blocks of a chosen parabolic
  factor `g` of `x = g k`.
- `sectionFunction_parabolic_mul`: `f(g k) = leviValue(g₁, g₂)` for every `g ∈ P` and integral
  `k`, where `g₁`, `g₂` are the diagonal blocks of `g`.
- **`sectionFunction_law`**: `f(u(X) diag(m₁, m₂) k) = leviValue(m₁, m₂)`, the hypothesis of
  `Shahidi.UnramifiedOpenCellSumStatement`.
- `sectionFunction_mul_integral` (right invariance under `GL(𝒪)`) and
  `sectionFunction_integral` (`f(k) = 1` for integral `k`).

`leviValue_mul_integral`, `leviValue_one` and the statements about `sectionFunction` assume
that `ψ` has additive conductor `0`, that is, conductor `𝒪`.

## Proofs

`sectionFunction_parabolic_mul` is the well-definedness of the section: if `g k = g₀ k₀` with
`g, g₀ ∈ P` and `k, k₀` integral, then `g⁻¹ g₀ = k k₀⁻¹` is an integral element of `P`, so its
diagonal blocks are integral (`levi_mem_integral`), and the blocks of `g₀` are those of `g`
times these integral blocks (`leviFirst_mul`); `leviValue_mul_integral` concludes. The other
statements follow from it: `u(X) diag(m₁, m₂)` is the product `upperP X * leviP m₁ m₂` in `P`,
whose blocks are `m₁` and `m₂`.

## Provenance

The normalized spherical section of an unramified induced representation is the vector used
in Casselman–Shalika (1980), §5, p. 227 (`casselman-shalika-1980-whittaker`), and, induced in
stages from the Levi `GL_(r+1) × GL_(t+1)` with the Levi Whittaker functional normalized to be
`1` on the spherical vector, in Shahidi (1981), proof of Theorem 5.1, p. 352
(`shahidi-1981-certain-l`). The construction from the Iwasawa decomposition and the
uniqueness of the Levi part up to integral matrices are the standard ones.
