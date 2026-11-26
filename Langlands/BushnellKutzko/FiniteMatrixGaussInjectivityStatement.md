# Injectivity of the finite matrix Gauss operator

## Statement

`Langlands.BushnellKutzko.FiniteMatrixGaussInjectivityStatement.{uK, uV}` is the proposition
that for

- every finite field `k : Type uK` (`[Field k] [Fintype k]`),
- every natural number `n` (the rank; `n = 0` is allowed),
- every additive character `ψ : AddChar k ℂ` with `ψ ≠ 1`, and
- every complex vector space `V : Type uV` and every representation
  `ρ : Representation ℂ (Matrix.GeneralLinearGroup (Fin n) k) V`,

the `ℂ`-linear operator

\[
  T_\rho(v) \;=\; \sum_{g\in \mathrm{GL}_n(k)} \psi(\operatorname{tr} g)\,\rho(g)v
\]

on `V` is injective. In Lean, `T_ρ` is the function
`fun v => ∑ g, ψ (Matrix.trace g.val) • ρ g v`, where `g.val` is the underlying matrix of the
unit `g` and `Matrix.trace` its trace.

- **The character.** `1 : AddChar k ℂ` is the trivial character `x ↦ 1` (Mathlib's `0` of
  `AddChar k ℂ` is the same character), so `ψ ≠ 1` says that `ψ(x) ≠ 1` for some `x ∈ k`
  (`AddChar.ne_one_iff`). The hypothesis is necessary: for the trivial character and the
  nontrivial character of `GL_1(𝔽_3) = 𝔽_3ˣ = {±1}` on `V = ℂ`, the operator is
  `1 + (−1) = 0`.
- **The representation.** `ρ` is arbitrary: it need not be irreducible, cuspidal or
  finite-dimensional. The statement assumes no choice of the characteristic `p` of `k`
  and no standard additive character.
- **Universes.** The field lives in `Type uK` and the representation space in `Type uV`, two
  independent universe parameters.
- **The finite sum.** `GL_n(k)` is finite; the sum uses the instance
  `Fintype.ofFinite (Matrix.GeneralLinearGroup (Fin n) k)`, and any two `Fintype` instances
  give the same sum.
- **Rank zero.** `GL_0(k)` has a single element, the empty matrix, whose trace is `0`; since
  `ψ(0) = 1` and `ρ(1)` is the identity, `T_ρ` is the identity of `V`.

The statement uses Mathlib's `AddChar`, `Matrix.GeneralLinearGroup`, `Matrix.trace` and
`Representation` and introduces no auxiliary definition. It asserts only injectivity: nothing
about the eigenvalues of `T_ρ` or their absolute values. This file states the result and does
not prove it.

## Source and provenance

The statement is a consequence, not a restatement, of Kondo's formula for the Gauss sums of the
irreducible representations of `GL_s` of a finite field (T. Kondo, *On Gaussian sums attached to
the general linear groups over finite fields*, J. Math. Soc. Japan 15 (1963), 244–255), as
cited by C. J. Bushnell and A. Fröhlich, *Non-abelian congruence Gauss sums and p-adic simple
algebras*, Proc. London Math. Soc. (3) 50 (1985), 207–264, §2.4, printed pp. 234–235 (PDF
pp. 28–29); source ID `bushnell-frohlich-1985-nonabelian-congruence-gauss-sums`.

**What the source states.** Let `ℓ` be a finite field of characteristic `p` and `s ≥ 1`.
Bushnell–Fröhlich fix the standard additive character `ψ_ℓ`, the composite of
`Tr_{ℓ/𝔽_p}` with `𝔽_p ≅ (1/p)ℤ/ℤ → ℂˣ`, `x ↦ e^{2πix}`, and put `ψ_{ℓ,s} = ψ_ℓ ∘ trd` on
`M_s(ℓ)`, with `trd` the matrix trace. The Kondo Gauss sum `𝔊(σ)` of an irreducible
representation `σ` of `GL_s(ℓ)` is defined by

\[
  \mathfrak G(\sigma)\,\sigma(1) \;=\; \sum_{x\in \mathrm{GL}_s(\ell)} \sigma(x)\,\psi_{\ell,s}(x)
  \qquad (2.4.11),
\]

so the operator `T_σ` of the statement, for `ψ = ψ_ℓ`, is the scalar `𝔊(σ)`. Kondo's formula
(2.4.12) writes `𝔊(σ)` as `± |ℓ|^{s(s−1)/2}` times a product of Gauss sums of characters of
finite extensions of `ℓ` (2.4.9), each nonzero by (2.4.10). Proposition (2.4.13) gives
`𝔊(σ_λ) 𝔊(σ̌_λ) = |M_s(ℓ)| · |ℓ|^{−|λ(1_Γ)|} · ω_λ(−1)` with `ω_λ` the central character, and
Corollary (2.4.16) says that this rational integer divides `|M_s(ℓ)|`, with equality up to sign
exactly in the non-deficient case. In particular `𝔊(σ) ≠ 0` for every irreducible `σ`.

**The deduction.** The source's assertion concerns irreducible `σ` and the standard character
`ψ_ℓ`; the statement here follows in three steps.

1. *Changing the character.* Take `ℓ = k` and `s = n`. Since the standard character `ψ_k`
   is nontrivial, the characters `x ↦ ψ_k(ax)`,
   `a ∈ k`, are pairwise distinct, and there are `|k|` of them, so every additive character of
   `k` has this form; a nontrivial `ψ` is `x ↦ ψ_k(ax)` for some `a ∈ kˣ`. For `n ≥ 1` and
   irreducible `σ`, substituting `g = a⁻¹h` gives
   `∑_g ψ(tr g) σ(g) = σ(a⁻¹·1) 𝔊(σ) = ω_σ(a)⁻¹ 𝔊(σ)`, a nonzero scalar, because the central
   scalar `a⁻¹·1` acts by the central character.
2. *Subrepresentations and commutation.* `T_ρ` is a linear combination of the operators
   `ρ(g)`, so it carries every subrepresentation `W` into itself, and its restriction to `W` is
   the operator `T` of the restricted representation. Since `tr(hgh⁻¹) = tr g`, reindexing the
   sum by `g ↦ hgh⁻¹` gives `T_ρ ρ(h) = ρ(h) T_ρ` for every `h ∈ GL_n(k)`. Hence on an
   irreducible finite-dimensional subrepresentation the restriction of `T_ρ` commutes with the
   group action and is a scalar by Schur's lemma, as (2.4.11) presupposes.
3. *Arbitrary representations.* For `v ∈ V`, the span `W` of the finite orbit `{ρ(g)v}` is a
   finite-dimensional subrepresentation. By Maschke's theorem (`ℂ` has characteristic zero),
   `W` is a direct sum of irreducible subrepresentations, and by steps 1 and 2 `T_ρ` acts on
   each by a nonzero scalar. Hence `T_ρ` is injective on `W`, and `T_ρ v = 0` forces `v = 0`.
   Rank zero is the identity case above.

## Use

**In the source.** In §2.4, (2.4.17)–(2.4.22), printed pp. 235–236 (PDF pp. 29–30),
Bushnell–Fröhlich apply Kondo's sums to tame irreducible representations `ρ` (their notation,
not the `ρ` of the statement) of the normalizer `G(𝔄)` of a principal order `𝔄` in
`A ≅ M_m(D)`. The unit quotient `U_0(𝔄)/U_1(𝔄)` is isomorphic to `GL_s(k_D)^r`, with `k_D` the
residue field of `D` (2.4.17), so every irreducible constituent of the restriction of `ρ` to
`U_0(𝔄)` is inflated from a tensor product `σ_1 ⊗ ⋯ ⊗ σ_r` of irreducible representations of
`GL_s(k_D)`. The element `τ'(ρ)` is defined by a sum over the unit quotient (2.4.19); Lemma
(2.4.21) gives `τ'(ρ) = ω_ρ(c⁻¹) ∏_i 𝔊(σ_i)`, with `ω_ρ` the central character of `ρ` and
`c ∈ Fˣ` as in (2.4.20)(ii), and Theorem (2.4.22) gives the same formula for the congruence
Gauss sum `τ(ρ)` when `ρ` has conductor `𝔓_𝔄`.

The proof of Theorem (3.3.8), printed pp. 259–260 (PDF pp. 53–54), treats the case where `A` is
not a division algebra. There `π` is an irreducible supercuspidal representation of `Aˣ`, and
`ρ = σ_0` is a *ramified* nondegenerate representation of `G = G(𝔄)` occurring in `π`. The
other elements `σ_i` (`i ≥ 1`) of the dual of `G` occurring in `π` are numbered so that
`𝔣(σ_i) | 𝔣(σ_{i+1})`, and `r` is the integer with `𝔣(σ_r) | 𝔣(ρ)` and `𝔣(σ_{r+1}) ∤ 𝔣(ρ)`
(these `σ_i` and this `r` are not those of §2.4). The source writes `σ'_i` for the
representation of `G` on the finite-dimensional space `V_{σ_i}` (so `ρ' = σ'_0`) and `σ̌'_i`
for the corresponding representation on `V̌_{σ_i}`. Let `Φ` be the characteristic function of
`1 + 𝔣(ρ)`, `Φ_0` that of `𝔄`, and `c ∈ G(𝔄)` an element with `c𝔄 = 𝔇_𝔄 𝔣(ρ)`. Then
`Φ̂(x) = (N𝔇_𝔄)^{−1/2} N𝔣(ρ)^{−1} Φ_0(cx) ψ_A(x)`, where the constant
`(N𝔇_𝔄)^{−1/2} N𝔣(ρ)^{−1}` is the measure `μ(𝔣(ρ))` of `𝔣(ρ)`, evaluated by (3.2.4). Substituting
`c⁻¹x` for `x` writes the zeta operator `Z(Φ̂, π̌, s)` as a series in `p^{−js}`, `j ≥ 0`. The
coefficient of `p^{−js}` is the prefactor `(N𝔇_𝔄)^{−1/2} N𝔣(ρ)^{−1} |c|^{−s}` times the
integral of `π̌(c⁻¹x) ψ_A(c⁻¹x)` over the `x ∈ 𝔄` with `|x| = p^{−j}`, and it vanishes for all
but one `j`. The coefficient for `j = 0` is (3.3.11), the prefactor times the integral over
`x ∈ U(𝔄)`. For `x ∈ U(𝔄)` the operator `π̌(c⁻¹x)` is block diagonal with diagonal blocks
`ρ̌'(c⁻¹x)`, `σ̌'_1(c⁻¹x)`, …, so (3.3.11) is block diagonal. With `μ^×` the measure for
`d^×x`, the `ρ̌'`-block of (3.3.11) is (3.3.12),
`(N𝔇_𝔄)^{−1/2} N𝔣(ρ)^{−1} |c|^{−s} μ^×(1 + 𝔣(ρ)) τ(ρ̌)` times the identity `1_0` of `V_{σ_0}`,
because that block's integrand is constant on cosets of `1 + 𝔣(ρ)`. This block is nonzero by
the hypothesis on `ρ`, so the coefficients with `j ≥ 1` vanish and `Z(Φ̂, π̌, s)` equals
(3.3.11); this is (3.3.13).

The quotient formula (3.3.14) is stated only for `1 ≤ i ≤ r`, that is, when `𝔣(σ_i)` divides
`𝔣(ρ)`. There the `σ̌'_i`-block of (3.3.13) is the prefactor
`(N𝔇_𝔄)^{−1/2} N𝔣(ρ)^{−1} |c|^{−s} μ^×(1 + 𝔣(ρ))` times the sum of `σ̌'_i(c⁻¹x) ψ_A(c⁻¹x)`
over `x ∈ U(𝔄)/(1 + 𝔣(ρ))`. The functional equation makes this block a nonzero scalar
operator on `V_{σ_i}`. If `𝔣(σ_i)` divides `𝔣(ρ)` properly and `σ_i` is ramified, the sum
vanishes by (2.3.11)(ii); this contradiction gives (3.3.15): if `σ_i` is ramified, then
`𝔣(ρ) | 𝔣(σ_i)`. If `𝔣(σ_i) = 𝔣(ρ)`, the sum is `τ(σ̌_i)` times the identity `1_i` of
`V_{σ_i}`, so the block is the prefactor times `τ(σ̌_i)`; as it is nonzero, `σ_i` is
nondegenerate. For `i > r`, `𝔣(σ_i)` does not divide `𝔣(ρ)`, and the source gives no quotient
formula for that block.

**At depth zero.** Let `F` be a nonarchimedean local field with ring of integers `𝔬`,
uniformizer `ϖ` and residue field `k`, and let `N ≥ 1`. Normalize the additive character `ψ_F`
of `F` to have conductor `𝔬` (trivial on `𝔬`, nontrivial on `ϖ⁻¹𝔬`); then
`ψ(t mod ϖ) = ψ_F(ϖ⁻¹t)`, for `t ∈ 𝔬`, is a nontrivial additive character of `k`. Let
`K_1 = 1 + ϖ M_N(𝔬)`, let `Φ` be its characteristic function, and let `Φ̂` be its Fourier
transform for the pairing `ψ_F(tr(xy))` on `M_N(F)`. Then `Φ̂` is supported on `ϖ⁻¹ M_N(𝔬)`,
where it is a nonzero constant times `ψ_F(tr y)`, so in `GL_N(F)` its support has determinant
order at least `−N`, with equality exactly on `ϖ⁻¹ GL_N(𝔬)`. Let `Π` be a smooth
representation of `GL_N(F)` on `V`, let `e` be the projection of `V` onto the fixed space `V^{K_1}`
given by averaging over `K_1`, and let `ρ` be the action of `GL_N(k) = GL_N(𝔬)/K_1` on
`V^{K_1}`. Substituting `x = ϖ⁻¹h` with `h ∈ GL_N(𝔬)` and summing over the cosets of `K_1`
shows that the part of the zeta operator `∫ Φ̂(x) |det x|^s Π(x) d^×x` over the shell
`ord det x = −N` equals

\[
  C \,\Pi(\varpi^{-1} I_N)\, T_\rho\, e ,
\]

with `C` a nonzero constant depending on `s` and the Haar measures and `T_ρ` the operator of
this statement for `ψ`. Since `Π(ϖ⁻¹ I_N)` is invertible (a nonzero scalar when `Π` has a
central character), the statement makes this operator injective on `V^{K_1}`, and when
`V^{K_1} ≠ 0` a smooth linear form detects a nonzero coefficient on that shell, without any
classification of the irreducible representations of `GL_N(k)`. The normalization matters:
for a character of conductor `ϖ𝔬` the support of `Φ̂` lies in `M_N(𝔬)` and the shell of order
`−N` contributes zero. The module `Langlands.BushnellKutzko.ShellIdentity` evaluates the
integral over a determinant shell from a monomial functional equation; this file contains
neither Kondo's formula nor this local calculation.

## An elementary proof route

The following route uses neither Kondo's formula nor the classification of the representations
of finite general linear groups; it is derived here, not taken from the sources above. For a
matrix `A ∈ M_n(k)` put

\[
  S_A(v) \;=\; \sum_{g\in \mathrm{GL}_n(k)} \psi(\operatorname{tr}(Ag))\,\rho(g)v ,
\]

so `T_ρ = S_I`. As in step 2 above, `T_ρ` commutes with every `ρ(h)`, hence with every `S_A`,
and `S_A` carries `ker T_ρ` into itself. For invertible `h`, reindexing by left multiplication
gives `S_A = ρ(h) S_{Ah}`; for invertible `A` this reads `S_A = ρ(A⁻¹) T_ρ`. The proof is by
strong induction on `n`; the case `n = 0` is the identity.

1. **No `U`-fixed vectors in the kernel (`n ≥ 2`).** Write matrices in blocks of sizes `1` and
   `n − 1`, let `P` be the parabolic subgroup of the matrices `[a B; 0 D]` (the stabiliser of
   the first coordinate line) and `U` its unipotent radical of the matrices `u_X = [1 X; 0 I]`.
   Let `v` be fixed by `U`. Since `ρ(g)v = ρ(g u_X)v`, averaging the summands of `T_ρ(v)` over
   right multiplication by `u_X` and using `tr(g u_X) = tr g + tr(CX)`, where `C` is the lower
   left block of `g = [a B; C D]`, gives

   \[
     T_\rho(v) = \frac{1}{|U|}\sum_{g}\Bigl(\sum_X \psi(\operatorname{tr}(CX))\Bigr)
       \psi(\operatorname{tr} g)\,\rho(g)v .
   \]

   The inner sum vanishes when `C ≠ 0` (additive orthogonality, below) and equals `|U|` when
   `C = 0`, so `T_ρ(v) = ∑_{g ∈ P} ψ(tr g) ρ(g)v`. Each `g ∈ P` factors uniquely as
   `diag(a, D) · u` with `u ∈ U`, and `tr g = a + tr D`; hence
   `T_ρ(v) = |U| · T₁ T_{n−1} (v)`, where `T₁` and `T_{n−1}` are the Gauss operators of the
   restrictions of `ρ` to `GL_1(k)` (as `a ↦ diag(a, I)`) and `GL_{n−1}(k)` (as
   `D ↦ diag(1, D)`). Both are injective by induction, so `ker T_ρ` contains no nonzero
   `U`-fixed vector.
2. **All `S_A(v)` vanish on the kernel.** Let `v ∈ ker T_ρ`. For invertible `A`,
   `S_A(v) = ρ(A⁻¹) T_ρ(v) = 0`. Let `A` be singular and `n ≥ 2`; extending a nonzero vector
   of `ker A` to a basis gives an invertible `h` such that the first column of `Ah` is zero.
   Then `(Ah) u_X = Ah` for all `X`, so left reindexing shows that `S_{Ah}(v)` is fixed by `U`;
   it lies in `ker T_ρ`, so it is `0` by step 1, and `S_A(v) = ρ(h) S_{Ah}(v) = 0`. For `n = 1`
   the only singular matrix is `A = 0`: the vector `S_0(v) = ∑_g ρ(g)v` is fixed by the whole
   group, on fixed vectors `T_ρ` acts by `∑_{x ∈ kˣ} ψ(x) = −1`, and `S_0(v) ∈ ker T_ρ`, so
   `S_0(v) = 0`.
3. **Fourier inversion.** For every `v`,

   \[
     \sum_{A\in M_n(k)} \psi(-\operatorname{tr}A)\,S_A(v)
       \;=\; \sum_{g} \Bigl(\sum_{A} \psi(\operatorname{tr}(A(g-I)))\Bigr)\rho(g)v
       \;=\; |M_n(k)|\, v ,
   \]

   since the inner sum vanishes for `g ≠ I` and equals `|M_n(k)|` for `g = I`. If
   `v ∈ ker T_ρ`, step 2 makes the left side zero, so `v = 0`. Linearity of `T_ρ` gives
   injectivity.

*Additive orthogonality.* Both vanishing sums are sums of `ψ ∘ f` over a finite `k`-vector
space, for a linear form `f`: `X ↦ tr(CX)` with `C ≠ 0`, and `A ↦ tr(AB)` with `B = g − I ≠ 0`.
A nonzero entry `B_{ij}` gives `f(t E_{ji}) = t B_{ij}` on the matrix unit `E_{ji}`, so `f` is
surjective onto `k` (likewise for `C`); as `ψ` is nontrivial, `ψ ∘ f` is a nontrivial additive
character and its sum is zero by `AddChar.sum_eq_zero_iff_ne_zero`.
