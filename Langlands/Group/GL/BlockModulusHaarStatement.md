# The explicit block modulus is the Haar module of Levi conjugation

Author: Worker 23.

This file states a proposition. It does not prove it. The proposition
`Langlands.GLBlockModulusHaarStatement` asserts that the published explicit block
modulus `T.leviModulus B` of `Group/GL/BlockModulus` agrees with Bernstein and
Zelevinsky's module of conjugation on the unipotent radical. The published
normalized induction (`Induction/Parabolic`) and normalized Jacquet module
(`Jacquet/Parabolic`) use the explicit formula, and their Markdown records this
identification as a separate obligation. This file states that obligation.

## Statement

The proposition quantifies over:

- every prime `p`, every p-adic field `F : PadicField p` and every realization
  `T : F.TopologicalData`, whose topology is used throughout;
- every `n` and every ordered block shape `B = (n_1, …, n_r)` of `n`, including
  the empty shape of `n = 0`;
- every measurable structure on the actual block unipotent radical
  `U = B.unipotentRadical F` that is its Borel σ-algebra (`BorelSpace`), and
  every Haar measure `μ` on `U` (`IsHaarMeasure`). `U` is a subgroup of the
  standard upper block parabolic, with the subspace topology from `GL_n(F)`;
- every element `m = (m_1, …, m_r)` of the actual block Levi `B.Levi F`.

It asserts

`μ.map (B.leviAction F m) = (T.leviModulus B m)⁻¹ • μ`.

Here `B.leviAction F m` is the published conjugation `u ↦ m u m⁻¹` of the
embedded Levi element on `U`, and

`T.leviModulus B m = ∏_{i<j} |det m_i|^(n_j) / |det m_j|^(n_i)`

with the residue-normalized absolute value. The scalar is a positive real
number, acting on measures through `ℝ≥0`.

## Conventions and source

Bernstein--Zelevinsky (1977), section 1.7, printed page 444 (PDF page 5):

> Let σ be an automorphism of an l-group U. Denote by mod_U σ the (topological)
> module of σ. It is defined by the formula
> ∫_U f(σ⁻¹(u)) dμ(u) = mod_U σ · ∫_U f(u) dμ(u),
> where μ is a Haar measure on U. If U is a closed subgroup of an l-group G and
> an element g ∈ G normalises U, then denote by mod_U(g) the module of the
> automorphism u ↦ g u g⁻¹.

The left side is the integral of `f` against the image of `μ` under `σ⁻¹`. So
the defining formula says `(σ⁻¹)_* μ = mod_U(σ) μ`, equivalently
`σ_* μ = mod_U(σ)⁻¹ μ`. With `σ` the conjugation by `m`, the proposition states
`mod_U(m) = T.leviModulus B m`, in the image-measure form of the same formula.

A check, which is not part of the formal content: for `GL_2` with `B = (1, 1)`
and `m = (a, b)`, conjugation sends the coordinate `x` of `U` to `a x b⁻¹`. The
image of an additive Haar measure is therefore `|a/b|⁻¹` times it, and
`T.leviModulus B m = |a| / |b|`.

The induced representations of section 1.8 (the same page) use `mod_U^(1/2)`,
and the Jacquet functor uses `mod_U^(-1/2)`. The published constructions use the
explicit positive half and inverse half of `T.leviModulus B`, so this
proposition is exactly the missing identification.

Registered source: `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`, section 1.7,
printed page 444.

## Faithfulness notes

- **Domain.** The source defines the module for any Haar measure, which is
  unique up to a positive scalar. The proposition quantifies over all Borel Haar
  measures and does not use uniqueness. The identity is linear in `μ`, so it is
  insensitive to scaling.
- **Explicit formula.** The block formula is the determinant of the action
  `X_ij ↦ m_i X_ij m_j⁻¹` on the off-diagonal blocks, as explained in
  `Group/GL/BlockModulus.md`. The proposition does not presuppose that
  computation; proving it is the content of the obligation.
- **Universes.** Only the field universe `uF` occurs.

## Not claimed

No proof is supplied. No Haar measure on `U` is constructed, and no product or
coordinate form of `μ` is asserted. Nothing is said about other parabolics, or
about the identification of the parabolic modulus with the modular function of
`P`.
