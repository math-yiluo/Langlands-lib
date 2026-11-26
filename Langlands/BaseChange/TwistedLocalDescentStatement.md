# Statement: local descent of the twisted constant term near a σ-regular point

Module `Langlands.BaseChange.TwistedLocalDescentStatement`. It states
`TwistedLocalDescentStatement.{u, v}` and supplies no proof.

## The statement

The data are those of `TwistedInducedCharacterFormulaStatement` without the representations:
nonarchimedean local fields `F` (universe `u`) and `E` (universe `v`), any characteristic,
with `E` an `F`-algebra carrying the `F`-module topology, `σ : E ≃ₐ[F] E` with
`IsCyclicAlgebra σ l`, a positive rank `n`, a block shape `B`, `δ ∈ GL_n(E)` norm associated
(`IsNormAssociated σ l δ γ`) with a regular semisimple `γ ∈ GL_n(F)`, a Levi class system
`m : Fin k → B.Levi F` for `γ` (`IsLeviClassSystem B γ m`), and `d : Fin k → B.Levi E` with
`x⁻¹ δ σ(x) = leviEmbedding (d j)` for some `x ∈ GL_n(E)` and `cyclicNorm σ l (d j i) =
baseChange F E (B.size i) (m j i)` for every block `i`.

The Haar measures `μG`, `μM`, `μU`, `μK` on `G = GL_n(E)`, `M = B.Levi E`,
`U = B.unipotentSubgroup E` and `K = GL_n(𝒪_E)` have the normalizations of
`TwistedVanDijkStatement` (volume one on `K`, `M(𝒪_E)`, `U ∩ K`; probability on `K`).

For every family of open sets `Ω j ⊆ M(E)` with `d j ∈ Ω j`, the statement asserts an open
neighbourhood `U₀` of `δ` in `G` such that for every test function `φ` supported in `U₀`
there are test functions `ψ j` on `M(E)` (`j ∈ Fin k`) with

1. `ψ j` supported in `twistedConjugacySaturation (leviAut σ B) (Ω j)`, the union of the
   twisted conjugates `y Ω_j σ(y)⁻¹` for `y ∈ M(E)`;
2. `∫ ψ j dμM = |D_{G/M,σ}(d j)|_F^{-1/2} ∫ φ dμG`, where
   `D_{G/M,σ}(d) = twistedRelativeParabolicDiscriminant B σ d = det_F(σ − Ad(d)⁻¹; 𝔤(E)/𝔪(E))`
   and `|·|_F` is `LocalField.residueNormalizedAbsoluteValue F`;
3. `∑ j, ψ j (x) = δ_P(x)^{1/2} ∫_U ∫_K φ(k⁻¹ x u σ(k)) dk du` for every `x ∈ M(E)`.

So the twisted constant term `φ^{P,σ}` of a test function supported near `δ` is the sum of
the `ψ j`. For an empty Levi class system (`k = 0`), condition 3 says that `φ^{P,σ}` vanishes.

## Origin and correspondence with the source

This is an internal formulation of the step of Henniart–Lemaire, *Changement de base et
induction automorphe pour GL_n en caractéristique non nulle*, Mém. SMF 124 (2011), II.4.5,
printed pp. 86–88 (PDF pp. 94–96), source ID
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, that turns the
van Dijk formula (2) into the character formula (3). The source derives that step from the
descent formula (1) for twisted orbital integrals (citing Laumon 1996, Prop. 4.4.9), the
twisted Weyl integration formula (II.2.10 (1), printed p. 72) for `M(E)` and for `G(E)`, and
the identity `D_{G/M,σ}(δ_η) = D_{G/M}(N(δ)_η)` (printed p. 88). Here the conclusion is
stated for test functions near one σ-regular point, which is the form the local character
values (`HasTwistedCharacterValue`) require; no character function or local integrability is
involved.

The support (condition 1), the mass (condition 2) and the decomposition (condition 3) are
the content of the statement: this file asserts them and does not prove them. The rest of
this section explains why they hold. Write `D = D_{G/M,σ}`, `N(x) = x σ(x) ⋯ σ^{l-1}(x)`,
and let twisted conjugation be `g⁻¹ x σ(g)`, as in II.2.3.

### Choice of the pieces

Shrink each window to an open `Ω'_j ⊆ Ω j` containing `d j` and let `S_j ⊆ M(E)` be the
`M(E)`-twisted conjugacy saturation of `Ω'_j`; it is open, stable under twisted conjugation
by `M(E)` and contained in `twistedConjugacySaturation (leviAut σ B) (Ω j)`. The pieces are
`ψ j = 1_{S_j} · φ^{P,σ}`, where `φ^{P,σ}(x) = δ_P(x)^{1/2} ∫_U ∫_K φ(k⁻¹ x u σ(k)) dk du`.
For `Ω'_j` small enough:

- every `x ∈ S_j` is σ-regular in `G(E)`, `D(x) ≠ 0`, and `|D(x)|_F = |D(d j)|_F`
  (`|D|_F` is locally constant where `D ≠ 0`, and `D(h⁻¹ x σ(h)) = D(x)` for `h ∈ M(E)`
  because `det_F` of `Ad(h⁻¹σ(h))` on `𝔤(E)/𝔪(E)` is a norm `N_{E/F}(σ(c)/c) = 1`);
- the `S_j` are pairwise disjoint: the norms of elements of `S_j` have block characteristic
  polynomials near those of the blocks of `m j`, and the `m j` are pairwise not
  `M(F)`-conjugate, so their tuples of block characteristic polynomials are distinct.

### Support and decomposition (conditions 1 and 3)

Let `U₀` be a small neighbourhood of `δ`. If `φ^{P,σ}(x) ≠ 0` for some `x ∈ M(E)`, then
`k⁻¹ x u σ(k) ∈ U₀` for some `u ∈ U(E)` and `k ∈ K`. The norm `N(x u)` lies in `P(E)` with
Levi component `N(x)` and is conjugate to `N(k⁻¹ x u σ(k))`, which is near a conjugate of
`N(δ)`, itself conjugate to `γ`. So the product of the block characteristic polynomials of
`N(x)` is near the characteristic polynomial of `γ`, which has distinct roots; by continuity
of roots the block characteristic polynomials are near those of the blocks of one `m j`.
Then `x` is `M(E)`-twisted conjugate to an element of `Ω'_j`. Indeed, work blockwise in
`GL_{n_i}(E)`: we may take the `i`-th block `d_i` of `d j` in the torus `T_i(E)`, where `T_i`
is the centralizer of its norm `N(d_i)`, the `i`-th block of `m j` (II.2.2, p. 63); the norm
`T_i(E) → T_i(F)` is open (II.2.10, p. 71), so the norms of the elements of `T_i(E)` near
`d_i` fill a neighbourhood of the regular semisimple element `N(d_i)` in `T_i(F)`, and their
characteristic polynomials fill a neighbourhood of that of `N(d_i)`; and two
σ-regular elements of `GL_{n_i}(E)` whose norms have the same characteristic polynomial are
twisted conjugate. Hence the
compact support of `φ^{P,σ}` lies in the disjoint union of the open sets `S_j`, each
`ψ j` is a test function supported in `S_j`, and `∑ j, ψ j = φ^{P,σ}`.

### Descent of orbital integrals

Let `x ∈ M(E)` with `D(x) ≠ 0` and `N(x)` regular semisimple. Its σ-centralizer
`G^σ_x = {g ∈ G(E) : g⁻¹ x σ(g) = x}` is contained in `M(E)`: such `g` commutes with
`N(x)` (since `σ^l = 1`), and an element commuting with a block-diagonal matrix with
distinct eigenvalues is block diagonal. Thus `G(E)` and `M(E)` have the common twisted
centralizer `G^σ_x`, and with one Haar measure on it the orbital integrals of II.2.3,
`Λ^G_σ(φ, x) = ∫_{G^σ_x\G(E)} φ(g⁻¹ x σ(g))` and
`Λ^M_σ(ψ, x) = ∫_{G^σ_x\M(E)} ψ(m⁻¹ x σ(m))`, are formed on the quotients by `G^σ_x`.
Formula (1) of II.4.5 is

`Λ^G_σ(φ, x) = |D(x)|_F^{-1/2} Λ^M_σ(φ^{P,σ}, x)`.

It comes from the substitution `u = x⁻¹ v⁻¹ x σ(v)` in `U(E)`: for such `x` the map
`v ↦ x⁻¹ v⁻¹ x σ(v)` is a homeomorphism of `U(E)` scaling Haar measure by
`|det_F(σ − Ad(x)⁻¹; 𝔲(E))|_F` (filtration of `U` by root heights), and
`δ_P(x)^{1/2} |det_F(σ − Ad(x)⁻¹; 𝔲(E))|_F = |D(x)|_F^{1/2}` (trace pairing between `𝔲`
and the opposite nilradical, `|det_F σ|_F = 1` and `δ_P(x) = |det_F(Ad(x); 𝔲(E))|_F`). So
`φ^{P,σ}(x) = |D(x)|_F^{1/2} ∫_{U(E) × K} φ((v k)⁻¹ x σ(v k)) dv dk`, an integral over
`U(E) × K` that involves no choice of coset representatives. Integrating over
`G^σ_x\M(E)` with `dg_E = dm_E du_E dk_E` (II.4.5, printed p. 86) gives (1).

### Mass (condition 2) by Weyl integration on the selected branches

Apply II.2.10 (1) to `G(E)` with `Θ = 1`. For `φ` supported in a small `U₀`, the
orbital integral `Λ^G_σ(φ, t)` of a point `t` of a maximal torus vanishes unless the twisted
orbit of `t` meets `U₀`. Only the torus `T ∈ 𝒯` conjugate to the centralizer of `γ`
contributes, near the `W_T(F)`-orbit of a point `t₀ ∈ T(E)` twisted conjugate to `δ`. The
`|W_T(F)|` points of that orbit are distinct in `T(E)^{σ-1}\T(E)` (the norm is injective
there and `N(t₀)` is regular) and give equal contributions (twisted conjugation by
`N_G(T)(F) ⊆ G(F)`), so

`∫ φ dg_E = ∫_{V₀} |D_G(N(t))|_F Λ^G_σ(φ, t) dt`

for a small neighbourhood `V₀` of `t₀` in `T(E)^{σ-1}\T(E)`. Apply II.2.10 (1) to `M(E)`
and `ψ j`: it is supported in `S_j`, so only the branch of one representative of the
`M(E)`-twisted class of `d j` contributes: a point `t_j` of the torus `T_j ∈ 𝒯^M`
that is `M(F)`-conjugate to the centralizer of `m j`, with `t_j` twisted conjugate to `d j` in `M(E)`.
In the same way, `∫ ψ j dm_E = ∫_{V_j} |D_M(N(t))|_F Λ^M_σ(ψ j, t) dt` for a small
neighbourhood `V_j` of `t_j`. On `V_j`, `Λ^M_σ(ψ j, t) = Λ^M_σ(φ^{P,σ}, t)` (`S_j` is
stable), formula (1) applies, `|D_G(N(t))|_F = |D_M(N(t))|_F |D_{G/M}(N(t))|_F` and
`D_{G/M}(N(t)) = D(t)` (printed p. 88), with `|D(t)|_F = |D(d j)|_F`. Hence

`∫ ψ j dm_E = |D(d j)|_F^{-1/2} ∫_{V_j} |D_G(N(t))|_F Λ^G_σ(φ, t) dt`.

Conjugation by an element `g_j ∈ G(F)` with `g_j⁻¹ T g_j = T_j` and
`g_j⁻¹ N(t₀) g_j = N(t_j)` carries `V₀` onto `V_j` (for `U₀` small), the measure on
`T(E)^{σ-1}\T(E)` onto that on `T_j(E)^{σ-1}\T_j(E)`, and preserves the integrand, which is
invariant under twisted conjugation in `G(E)`. The product `|D_G ∘ N| · Λ^G_σ(φ, ·) dt` does
not depend on the Haar measures chosen on the tori. So the last integral is `∫ φ dg_E`,
which is condition 2: each Levi class `j` contributes through its one representative `d j`,
with weight `|D_{G/M,σ}(d j)|_F^{-1/2}`.

## Weights

In `TwistedInducedCharacterFormulaStatement` the weight is the ordinary relative
discriminant at the norm, `relativeDiscriminantWeight B (m j) = |D_{G/M}(m j)|_F^{-1/2}`.
The Library theorem `twistedRelativeParabolicDiscriminant_eq_of_cyclicNorm` identifies
`D_{G/M,σ}(d j)` with `D_{G/M}(m j)` because the blockwise cyclic norms of `d j` are the
blocks of `m j`. The present statement keeps the twisted discriminant at `d j`, which is the
quantity in the descent formula (1).
