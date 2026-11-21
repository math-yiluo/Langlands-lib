# The cuspidal tests of the characterizing system of Eisenstein series

Source: J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), 187–234 (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`). The relevant places are:

- §6, Corollary 6.10 with (6.21) and (6.22), p.209: the cuspidal parts of the constant terms of
  `E(φ, λ)`, and the uniqueness of `E(φ, λ)` among automorphic forms satisfying (6.21);
- §8.4, pp.223–224: the non-homogeneous equations (8.2b) of the system `Ξ_fnl(λ)`, their
  consequence (8.3), and the proof of Proposition 8.4.

The module **states** a proposition; nothing is proved here. It isolates the part of BL
Proposition 8.4 that concerns the cuspidal equations (8.2b), so that it can be proved
separately from the Harish-Chandra equations (8.2a), the growth estimates and Lemma 8.1.

## The statement `Langlands.Global.EisensteinCuspidalTestSystemStatement`

The hypotheses are exactly those of `EisensteinSystemDominationStatement` (module
`AdelicEisensteinSystemDominationStatement`): `G` connected reductive over a number field `F`,
a parabolic `p : P → G` with unipotent radical `iU`, Levi `l`, split component `a` presented by
`r`, a maximal compact `K` with `P(𝔸)K = G(𝔸)` (`hK : IsIwasawaCompact p K`), a closed matrix
embedding `rho`, and an automorphic form `φ` on `U(𝔸)M(F) \ G(𝔸)`.

Conclusion: there are a real `R₀`, a `StandardParabolicFamily` `𝓕` (a maximal split torus, a
generic cocharacter and the standard parabolics `P_J`, `J ⊆ Δ₀`, with Levi and split component
`A_J`) and a maximal compact `K'` with `IsIwasawaCompact (𝓕.p Q) K'` for every standard `Q`,
such that for every `n` and every complex linear coordinate system
`e : ℂⁿ ≃ X^*(P) ⊗ ℂ` there are

- polynomials `D J b Q s ∈ ℂ[X]`, for standard indices `J`, `Q`, a point
  `b ∈ 𝓕.positiveSplitComponent J` (the positive real points of `A_J`, as a subgroup of
  `P_J(𝔸)`) and `s ∈ ℂⁿ`;
- natural numbers `deg J b Q`;

with `D J b Q s` monic of degree `deg J b Q` (independent of `s`), with nonzero constant
coefficient, and with every coefficient `s ↦ (D J b Q s).coeff k` an entire function on `ℂⁿ`
(`Differentiable ℂ`). Moreover, for every compact open subgroup `L ≤ G(𝔸_f)` and every real
`R` there is a family of scalar linear equations `eqn i s v = c i s` (`i ∈ Idx`, `s ∈ ℂⁿ`,
`eqn i s` a continuous linear form on `𝔉^R_L`, the Library's `UniformGrowthFrechetSpace`)
such that:

1. the system is analytic on `ℂⁿ` (`IsAnalyticSystem 𝓘(ℂ, Fin n → ℂ) eqn c`);
2. for every `s`, every solution `v` at `s`, every `J`, every `b ∈ A_J` positive and every
   `Q ≤ J`, the function
   `g ↦ ∑_{k ≤ deg} (D J b Q s).coeff k · C_Q v (b^k g)`
   lies in `𝓕.cuspidalAnnihilator (K'.comap ofInfinite) rho Q` (module
   `AdelicCuspidalAnnihilator`). Here `C_Q` is `𝓕.constantTerm Q`, applied to the underlying
   function of `v`, and `b^k g` is the product in `G(𝔸)` of the image of `b^k` under
   `P_J → G` with `g`. Thus the polynomial `D J b Q s` evaluated at the left translation
   `f ↦ f(b ·)` sends `C_Q v` into the cuspidal annihilator along `Q`;
3. for every `s` with `e s` `R₀`-regular (`r.IsRegularParameter hA hT R₀`), every
   `v ∈ 𝔉^R_L` whose underlying function is the Eisenstein series `E(φ, e s)`
   (`hK.eisensteinSeries φ (e s)`) is a solution at `s`;
4. for every `s` with `e s` `R₀`-regular, every solution `v` at `s` whose underlying function
   is an automorphic form on `G(F) \ G(𝔸)` (`IsAutomorphicFunctionOn` for
   `rationalSubgroup F G` and the archimedean part of `K`) has underlying function
   `E(φ, e s)`.

The statement writes the action of the polynomial `D J b Q s` as an explicit finite sum of left
translates. The sum runs over `k` up to the degree; all other coefficients vanish. The Library
already has operators for this shift: `StandardParabolicFamily.splitComponentRepresentation J b`
(module `AdelicLeadingCuspidalComponents`) is the linear map `f ↦ f(b ·)` of the same raw shift
by `b ∈ A_J`. `GroupAction.leftFunctions` at the inverse of the ambient point of `b` gives the
same map. `isTranslationPolynomialSolution_iff_aeval` (module `AdelicExponentPolynomials`) shows
that the vanishing of an explicit sum of this kind is the vanishing of `Polynomial.aeval` at that
operator; its proof expands `aeval` into the same finite sum. The sum used here is that
function, written out directly.

## Correspondence with the source

- **The equations.** In §8.4, for every `Q ⊆ P` BL fix an integer `m_Q ≥ 0` and an exponent
  list `μ_Q ∈ X_Q^{m_Q}` with `C^cusp_{P,Q} φ ∈ A_Q^cusp(μ_Q)`, i.e. the list is chosen for the
  *cuspidal projection* of the constant term. Then (8.2b) says that for every standard `Q`
  and every collection of tuples `a_w ∈ A_Q^{m_{P_w}}`, `w ∈ W^{⊃Q}(P) \ {e}` (one entry of
  `a_w` for each entry of the list `μ_{P_w}`), the product of difference operators
  `∏_{w ≠ e} D^{Q, w(μ_{P_w} + λ)}_{a_w}` applied to `C_{G,Q} ψ − C_{P,Q} φ_λ` lies in
  `(Ã_Q^cusp)^⊥`. Here `D^{Q,μ}_a f = a · f − a^μ f` for the normalized action
  `(a · f)(g) = δ_Q(a)^{-1/2} f(a g)` of (6.2), and `D^{Q,μ}_{a}` for a tuple is the product
  over its entries. Pairing with the rapidly decreasing elements of `Ã_Q^cusp` makes these
  scalar linear equations on `𝔉^R_L`. Their coefficients are entire in `λ = e s`, which gives
  clause 1; the paired Markdown of `AdelicEisensteinSystemDominationStatement` explains the
  continuity and local uniformity of the affine term. The equations live on every `𝔉^R_L`,
  which is why `L` and `R` are arbitrary here.
- **Clause 2 is (8.3).** In the proof of Proposition 8.4, (8.2b) implies (8.3): for every
  collection of tuples `a_w ∈ A_Q^{m_{P_w}}`, `w ∈ W^{⊃Q}(P)` (now including `w = e` when it
  belongs to `W^{⊃Q}(P)`), the full product `∏_w D^{Q, w(μ_{P_w} + λ)}_{a_w}` sends
  `C_{G,Q} ψ` into `(Ã_Q^cusp)^⊥`. The identity `e` lies in `W^{⊃Q}(P)` exactly when
  `M_Q ⊆ M_P`, i.e. when `Q ⊆ P`.
  - If `Q ⊆ P`, the factor `D^{Q, μ_Q + λ}_{a_e}` for `w = e` does **not** kill the affine term
    `C_{P,Q} φ_λ` itself. It kills the cuspidal projection `C^cusp_{P,Q} φ_λ`, because the
    list `μ_Q` was chosen for that projection. Hence it sends `C_{P,Q} φ_λ` into
    `(Ã_Q^cusp)^⊥`, since pairing with cusp forms only sees the cuspidal projection.
    The annihilator `(Ã_Q^cusp)^⊥` is stable under the other difference operators: a point of
    `A_Q` commutes with the Levi integration variable and only shifts the freely quantified
    ambient point `g`. Applying the factor for `e` to (8.2b) therefore gives (8.3).
    Killing the full term would be false in general. For example, take `P = Q = G = SL₂`,
    `λ = 0` and `φ = 1 − 1^cusp` (the cuspidal projection of §6.2). Then `φ ≠ 0`, its
    cuspidal projection is `0` by idempotence, and one may take `m_G = 0`. The identity factor
    is then the empty product, which leaves `C_{G,G} φ = φ ≠ 0`, although `φ` lies in the
    annihilator.
  - If `Q ⊄ P`, there is no affine term and no identity factor, and (8.3) is (8.2b).

  To obtain clause 2, take every entry of every tuple `a_w` equal to one point `b ∈ A_J`. This
  point lies in `A_Q` for `Q ⊆ J`; the Library's `AdelicNestedSplitComponents` gives the
  compatible lifts. Taking out the nonzero scalar `δ_Q(b)^{-1/2}` from each factor, each
  `D^{Q,μ}_{b}` becomes, up to that scalar, the monic linear factor
  `T_b − δ_Q(b)^{1/2} exp⟨μ, H_Q(b)⟩` in the raw left translation `T_b f = f(b ·)`. The
  modulus enters through these roots, not through the shift. Since the annihilator is a
  subspace, the scalars can be dropped. So the whole product is a polynomial in `T_b`, monic,
  of degree the total length of the exponent lists (independent of `λ`; repetitions are
  allowed and the empty product is `1`), with constant coefficient a product of nonvanishing
  exponentials, and with coefficients entire in `λ`. The statement asks for this for every
  positive `b ∈ A_J`, every `J` and every `Q ≤ J`. For `Q` not below `J` the polynomial is
  unconstrained (it may be `1`).
- **Clause 3 is the first half of the proof of Proposition 8.4.** At regular `λ` the
  Eisenstein series satisfies (8.2b) by Corollary 6.10. The chamber `⟨Re λ, α^∨⟩ ≫ 0` is
  `R₀`-regularity, as in `EisensteinSystemDominationStatement`.
- **Clause 4 is (6.22).** For an automorphic form, (8.2b) is equivalent to (6.21) (proof of
  Proposition 8.4), and by (6.22) `E(φ, λ)` is the unique automorphic form satisfying (6.21)
  at regular `λ`.
- **The standard family.** The difference equations are written relative to a minimal
  parabolic `P₀` and the standard parabolics containing it. The statement lets the prover
  choose `𝓕` (one may take `P` standard for `𝓕` after conjugation) and a maximal compact `K'`.
  Formally the statement requires only that `K'` be maximal compact with
  `P_Q(𝔸) K' = G(𝔸)` for every standard `Q` (`IsIwasawaCompact`). It does not assert that
  `K'` is in good position with respect to `M₀` (BL §2.1, p.190, after MW I.1.4), which in
  particular makes `K'` meet each standard Levi in a maximal compact subgroup. A `K'` in good
  position is one possible witness. `K'`
  enters only through the cuspidal annihilator. Membership in `cuspidalAnnihilator` is the fibrewise test of BL (6.8)
  described in `AdelicCuspidalAnnihilator.md`.

## Use

This is one premise of the planned reduction proving `EisensteinSystemDominationStatement`.
There, clause 2 with `J = Δ₀ \ {α}` and `b = a_α`, multiplied over all `Q ≤ J`, gives the
product step of BL Lemma 8.1 (module `AdelicCuspidalProductVanishing`) along the maximal
parabolic `P_α`, hence the difference equations of `Ξ_main`. Clauses 3 and 4 give the
uniqueness and identification of the solution at regular parameters.
