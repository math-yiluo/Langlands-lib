# Parabolic covariance of Shahidi's intertwining integral

This module extends the function-level integral (0.1) of
`Langlands.Representation.Shahidi.IntertwiningIntegral`. The source is
F. Shahidi, *Fourier transforms of intertwining operators and Plancherel
measures for GL(n)*, American Journal of Mathematics 106 (1984), 67–111,
printed page 72:

\[
A(s,\pi,w_{m,n})f(g)=\int_{U'} f(w_{m,n}u'g)\,du'.
\]

The registered original is `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
The author is Worker 11.

On page 72 the source calls (0.1) an intertwining operator on the induced
space `I(s,π)` of the standard `(m,n)` parabolic. Its display (0.3) applies
the Whittaker functional of `I(-s,π')`, where `π' = π₂ ⊗ π₁`, to `A f`. So
`A f` is taken to lie in the induced space `I(-s,π')` of the `(n,m)`
parabolic. At the level of functions this has two parts: the integral transforms on the left under the `(n,m)`
parabolic by the exchanged Levi data, and it keeps the right invariance of
`f`. This module proves both parts for an arbitrary function `f` and arbitrary
left transformation data. It does not construct `I(s,π)`. As in the base module,
`f` takes values in an arbitrary complex vector space `V` carrying a
representation `ρ` of a topological group `H`. The measure `μ` on the `n` by
`m` matrices is arbitrary, apart from the hypotheses listed below.

## Block lemmas

These results are internal to the formalization. They concern the published
two-block shape `twoBlocks m n hm hn` of
`Langlands.Representation.Shahidi.TwoBlocks`, the standard parabolic of
`GL_(m+n)` with diagonal blocks of sizes `m` then `n`.

- `twoBlockLeviSwap hm hn R` is the multiplicative equivalence from the Levi
  of `twoBlocks n m hn hm` to the Levi of `twoBlocks m n hm hn` that exchanges
  the two blocks. So `(h₂, h₁)` goes to `(h₁, h₂)`. The two `simp` lemmas
  `twoBlockLeviSwap_first` and `twoBlockLeviSwap_second` hold by `rfl`.
- `eq_upper_of_mem_unipotentSubgroup`: an element of the radical
  (`unipotentSubgroup`) of `twoBlocks m n` equals `upper m n R a`, where `a` is
  its upper right `m` by `n` block. The proof compares entries in the four
  blocks, using the published entry lemmas for `upper` and for the parabolic.
- `exists_upper_mul_blockSum`: every `p` in the parabolic of `twoBlocks m n`
  is `upper m n R a * blockSum (g₀, g₁)` for some `a`. Here `(g₀, g₁)` is the
  published Levi projection of `p`. The proof uses the published Levi
  decomposition `decomposition` and `twoBlocks_leviEmbedding`.

## Change of variables

`rectangularConj h₂ h₁` is the measurable equivalence `a ↦ h₂⁻¹ a h₁` of the
`n` by `m` matrices, for `h₂ ∈ GL_n(F)` and `h₁ ∈ GL_m(F)`. Its inverse is
`a ↦ h₂ a h₁⁻¹`. It needs a field with `MeasurableAdd₂` and `MeasurableMul`.
The lemma `measurable_mul_mul` gives measurability of `a ↦ A a B` for any
matrices `A` and `B`.

`map_rectangularConj_padic` treats a p-adic field `F` with topological data
`T`. Let `μ` be an additive Haar measure on the `n` by `m` matrices. The
measurable structure on the matrices is the one induced from the
coefficients, and it is assumed to be Borel for the topology `T.topology`.
The coefficients are also assumed to satisfy `MeasurableAdd₂` and
`MeasurableMul`, which `rectangularConj` needs.
Then

\[
\mu\circ(\text{rectangularConj }h_2\,h_1)^{-1}
  = |\det h_2|^m\,|\det h_1|^{-n}\,\mu,
\]

where `|det|` is the published `T.determinantNorm`. In Lean the factor is
`(T.determinantNorm n h₂)^m / (T.determinantNorm m h₁)^n` in `ℝ≥0`. The proof
applies the published `padicRectangularHaarScaling` with `A = h₂⁻¹` and
`B = h₁⁻¹`. It then rewrites `(h₁⁻¹)⁻¹ = h₁` and uses multiplicativity of the
determinant norm. This is the constant announced in the base module's
Markdown.

## Translation of the coordinates

`hasIntegral_add_right` is a weak-integral lemma. Assume `MeasurableAdd F`
and that `μ` is invariant under left translation. If `Φ` has weak integral `v`
against `μ`, then so does `a ↦ Φ(a + b)` for every matrix `b`. The proof
applies the published `HasIntegral.comp_measurableEquiv` to the translation
`a ↦ a + b`, with scaling constant `1`.

## Parabolic covariance

`HasIntertwiningIntegral.parabolic` assumes `MeasurableAdd₂ F`,
`MeasurableMul F`, and that `μ` is invariant under left translation. Its data
are the following.

- `A` satisfies the base relation `HasIntertwiningIntegral m n ρ μ f A`.
- `χ` is a function from the Levi of `twoBlocks m n` to `ℂ`, and `τ` is a
  function from that Levi to `H`. Both are arbitrary.
- The source transformation law: for every `p` in the parabolic of
  `twoBlocks m n` and every `x`,
  `f(p x) = χ(m_p) • ρ(τ(m_p))(f(x))`, where `m_p` is the Levi projection of
  `p`.
- `c` is a function from the Levi of `twoBlocks n m` to `ℝ≥0`, with
  `μ.map (rectangularConj (l 0) (l 1)) = c(l) • μ` for every Levi element
  `l = (h₂, h₁)`.

Let `p` be in the parabolic of `twoBlocks n m`, carried to total rank `m+n` by
the published `swapRank m n F`, and let `l` be its Levi projection. The
conclusion is that the integrand at `swapRank(p) x` has weak integral

\[
\bigl(\chi(\mathrm{swap}\,l)\,c(l)\bigr)\cdot
  \rho(\tau(\mathrm{swap}\,l))\bigl(A(x)\bigr),
\]

where `swap l = twoBlockLeviSwap hm hn F l = (h₁, h₂)`.

The proof writes `p = upper n m F a * blockSum (h₂, h₁)` with
`exists_upper_mul_blockSum`. Then `swapRank(p)` is
`intertwiningUnipotent m n F a * swapRank(blockSum (h₂, h₁))`. The published
`intertwiningIntegrand_unipotent_mul` turns the first factor into the
translation `a' ↦ a' + a`, which `hasIntegral_add_right` removes. The second
factor is the published Levi covariance `HasIntertwiningIntegral.levi`. Its
hypothesis `f(diag(h₁,h₂) y) = χ(swap l) • ρ(τ(swap l))(f y)` is the source
transformation law at the Levi element `swap l`, by the published
`leviProjection_section`, `leviInParabolic_val` and `twoBlocks_leviEmbedding`.

`intertwiningOperator_parabolic` is the same statement for
`intertwiningOperator`, under the uniqueness hypotheses of the base module
(`hcofinal` and smoothness `hρ`). The proof compares the two weak integrals by
`SmoothWeakIntegral.HasIntegral.unique` pointwise.

### The exponents in the intended application

This paragraph is a check of the intended use. It is not a Lean statement.
In the intended application `H` is the Levi `GL_m(F) × GL_n(F)`, `τ` is the
identity, and `ρ = π₁ ⊗ π₂`. The scalar `χ(h₁, h₂)` is
`|det h₁|^((s+n)/2) |det h₂|^(-(s+m)/2)`. These are the normalized exponents
of `I(s,π)` recorded in the task context. Over a p-adic field with an additive
Haar measure, `c(h₂, h₁) = |det h₂|^m |det h₁|^(-n)` by
`map_rectangularConj_padic`. The product is

\[
|\det h_1|^{(s-n)/2}\,|\det h_2|^{(m-s)/2}.
\]

This is the modulus-and-twist factor of `I(-s,π')` on the `(n,m)` Levi
element `(h₂, h₁)`: `δ^{1/2}` gives `|det h₂|^{m/2} |det h₁|^{-n/2}`, and the
twists `π₂ ⊗ |det|^{-s/2}` and `π₁ ⊗ |det|^{s/2}` give the rest. The
operator `ρ(τ(swap l)) = π₁(h₁) ⊗ π₂(h₂)` acts on `V₁ ⊗ V₂`. It becomes
`π'(h₂, h₁)` after the tensor swap `V₁ ⊗ V₂ → V₂ ⊗ V₁`.

## Right invariance

`intertwiningOperator_mul_right`: if `f(x k) = f(x)` for all `x`, then
`A f(x k) = A f(x)` for all `x`. It follows from the published
`intertwiningOperator_rightTranslate`, since the right translate of `f` is
`f` itself. In the application `k` ranges over a compact open subgroup, so the
operator preserves the corresponding level of smoothness.

## What is not claimed

This unit does not claim the following:

- that the integral converges for `f ∈ I(s,π)` when `Re s` is large;
- that `A(s,π,w_(m,n))` has a rational continuation in `q^(-s)`;
- the specialization to the actual induced spaces, including the tensor swap
  and the identification of the target shape with `swapRank`;
- any Haar normalization of `du'`.

These remain obligations for the later specialization to induced
representations.
