# A characterizing system for Eisenstein series dominated by `Ξ_main`

Source: J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), 187–234 (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`; PDF in the publication folder,
journal pages). The relevant places are:

- §8.1, (8.1) and Lemma 8.1, pp.221–222: characterization of automorphic forms;
- §8.3, Lemma 8.3, p.223: the uniform Harish-Chandra equations;
- §8.4, pp.223–224: the system `Ξ_fnl(λ)`, equations (8.2a), (8.2b) and (8.3), and Proposition 8.4 with
  its proof;
- §8.6, Corollary, p.226: the Fréchet form of the continuation.

The statement is a proposition only; nothing is proved here.

## The statement `Langlands.Global.EisensteinSystemDominationStatement`

The setting is that of `EisensteinMeromorphicContinuationStatement` and of
`EisensteinAnalyticSystemStatement`:

- `G` connected reductive over a number field `F`, a parabolic `p : P → G` with unipotent radical
  `iU`, a rational Levi `l : M → P` and split component `a : A → M` presented by `r`;
- a maximal compact `K` with `P(𝔸)K = G(𝔸)`, a closed matrix embedding `rho`;
- an automorphic form `φ` on `U(𝔸)M(F) \ G(𝔸)`.

The statement also assumes `[LocallyOfFiniteType G.X.hom]`. This follows from smoothness, and
the Library's constant terms and Haar measures need it.

Conclusion: there is `R₀` such that for every complex linear coordinate system
`e : ℂⁿ ≃ X^*(P) ⊗ ℂ` and every bounded open set `W ⊆ ℂⁿ` there are:

1. a maximal split torus `iT : T → G`, a generic cocharacter `ν` and group data `u`, `t`, `z` of
   the system `Ξ_main` of BL §7.2 (`IsLocalFinitenessGroupData`, from
   `AdelicLocalFinitenessStatement`): unipotent radicals `U_α` of the maximal standard
   parabolics, elements `a_α = iT(t α) ∈ A_{P_α}^G` with `⟨α, H_0(a_α)⟩ > 0`, and
   `iT(z j) ∈ A_G` with `H_G(iT(z j))` a basis of `𝔞_G`;
2. admissible data `X : LocalFinitenessData` of `Ξ_main` on all of `ℂⁿ` (the open set `⊤`);
3. a compact open subgroup `L ≤ G(𝔸_f)` and a real `R₁`.

These satisfy: for every `R ≥ R₁` there is a family of scalar linear equations
`eqn i s v = c i s` (`i ∈ Idx`, `s ∈ W`) on `v ∈ 𝔉^R_L` (the Library's
`UniformGrowthFrechetSpace`) such that

- the system is analytic on `W` (`IsAnalyticSystem`);
- every solution at `s` lies in `X.solutions … R L s`, the solutions of `Ξ_main(s)` in `𝔉^R_L`,
  with `a α = iT(t α)` and central elements `iT(z j)`;
- at every `s` with `e s` `R₀`-regular (`IsRegularParameter`), the system has exactly one
  solution, and its underlying function is the Eisenstein series `E(φ, e s)`
  (`IsIwasawaCompact.eisensteinSeries`);
- every solution is an automorphic form on `G(F) \ G(𝔸)` (`IsAutomorphicFunctionOn` for
  `rationalSubgroup F G`).

## Correspondence with the source

- **The system.** `Ξ_fnl(λ)` of §8.4 consists of the equations (8.2a)
  `δ(h_i(λ)) ψ = c_i(λ) ψ` and the non-homogeneous equations (8.2b), which say that certain
  difference operators applied to `C_{G,Q} ψ − C_{P,Q} φ_λ` lie in the annihilator
  `(Ã_Q^cusp)^⊥`. On `𝔉^R_L` both become families of scalar equations given by continuous
  linear forms:
  - (8.2a) gives the forms `ψ ↦ δ(h_i(λ))ψ(x) − c_i(λ)ψ(x)`, one for each `x ∈ G(𝔸)`;
  - (8.2b) gives the pairings with the rapidly decreasing elements of `Ã_Q^cusp`.

  For each fixed scalar test the convolution integral is bounded by the order-zero weighted
  seminorm times a constant, since the kernel has compact support. Constant term integration
  is over a compact unipotent quotient, and the rapidly decreasing tests in (8.2b) absorb
  every fixed polynomial growth bound on the parabolic quotient. The finitely many translate
  operators in an equation preserve those bounds. The coefficients of these operators are
  entire in `λ = e s`. In the affine term the test has compact support in the `H_Q` variable,
  and for `Q ⊆ P` the `λ`-twist depends on the projection of `H_Q` to `𝔞_P`. The twist thus
  gives a locally uniform integrable bound in `λ`, including after each fixed translate.
  If `Q ⊈ P`, the identity contribution is zero, as in (6.21). These are the scalar tests of
  the holomorphy assertion of Proposition 8.4.
- **Uniqueness.** Proposition 8.4: for `⟨Re λ, α^∨⟩ ≫ 0` the unique solution in the union
  of the growth spaces is `E(φ, λ)`. The chamber depends on the inducing data, not on `W`,
  as in BL's standing assumption of §6.9 (p.207); the Library's equivalent cofinal chamber is
  explained in `AdelicEisensteinConvergenceStatement.md`. To restrict this assertion to
  `𝔉^R_L` one must also put the regular Eisenstein series in that space, as explained below.
- **Automorphy of solutions.** In the proof of Proposition 8.4, (8.2b) implies (8.3) for every
  `λ`. Then Lemma 8.1, with (8.2a) for an `i` with `c_i(λ) ≠ 0`, shows that every solution is an
  automorphic form.
- **Domination by `Ξ_main`.** The last paragraph of the proof of Proposition 8.4 says that, by (8.3)
  and the argument of Lemma 8.1, `Ξ_fnl(λ)` implies a system of the form considered in §7.2.
  The statement makes this implication explicit: every solution of the system is a solution of
  `Ξ_main(s)` for data `X` in the sense of `AdelicLocalFinitenessStatement`. The data are as
  follows.
  - The Harish-Chandra equations (8.2a) come from Lemmas 8.2 and 8.3 and (6.18). A family
    `∑_k b_k(λ) δ(h)^k` acts by the finite list of fixed kernels `h^{*k}` with entire
    coefficients. The families are indexed by base points `λ₀`, with the corresponding
    `c_i(λ₀) ≠ 0`.
  - To obtain the polynomial along `P_α`, specialize the product in the proof of Lemma 8.1
    (the display following the definition of `V`) to `P = P_α`, with the exponent lists of
    (8.3). Include **all** standard `Q ⊆ P_α` and restrict the characters in the list for `Q`
    to `A_{P_α}`. Set every translate in the resulting product to `a_α`. Each linear factor
    for the twisted action has the form `T_{a_α} − exp⟨η_Q(λ), H_0(a_α)⟩`, where
    `η_Q(λ) = w(μ + λ)` with the indicated restrictions understood. In passing to plain
    translation, replace its root by `δ_{P_α}(a_α)^{1/2} exp⟨η_Q(λ), H_0(a_α)⟩`.
  - For `z_j` take the same product at `P = G`, hence over **all** standard `Q`, evaluating
    their characters on `A_G`. The modulus of `G` in this twisted action is trivial. Every
    root is a nonvanishing exponential, so the constant coefficient of the monic product
    never vanishes. Both products use lists, retaining repetitions, with the empty product
    interpreted as `1`.

  The data are defined on all of `ℂⁿ` (`X` lives on `⊤`). No one finite level has to make all
  kernels in this possibly infinite index family bi-invariant: each fixed kernel is a test
  function, and a convolution equation on `𝔉^R_L` is tested pointwise on `G(𝔸)`.
- **Group data.** BL fix `P_0`, the `a_α` and the `z_j` once and for all (§7.2). The statement
  asserts that such data exist (maximal split tori, generic cocharacters, the unipotent radicals
  as closed subgroup schemes, and the elements `a_α`, `z_j`). This existence is part of the
  content to be proved.
- **Changing the Iwasawa compact.** Use the change of height described in
  `AdelicEisensteinConvergenceStatement.md`: conjugate the infinite compact, and express the
  finite height discrepancy using the finite double-coset partition. Before the fixed
  archimedean right translation, the inducing data become a finite family of good-position
  sections with entire scalar coefficients in `λ`. In (8.2b) take the corresponding linear
  combination of the identity terms, and concatenate the exponent lists of all the sections.
  The finite-dimensional spaces in Lemma 8.3 are the sums of the spaces for these sections
  from Lemma 8.2. At a fixed `λ` the scalar multiples are still in those spaces, and the
  leading-component argument for uniqueness uses the same chamber after increasing `R₀` for
  the finite union of exponent lists. Transport the system back by the fixed right
  translation. This commutes with constant terms and left translates and conjugates the
  convolution kernels by the translating element. The finite level is unchanged by an
  archimedean translate and finiteness under the archimedean compact is transported by
  conjugation. Right translation by a fixed element compares the two weighted seminorms of
  a given exponent via the height multiplication bound and the adjoint action on derivatives.
- **Fréchet form.** Choose `L` compact open fixing the inducing data (intersect the finitely
  many stabilizers in the preceding construction). The convergent series then belongs to
  the right-`L`-fixed part of the union of the growth spaces. The proof of Proposition 8.4
  first shows that the series solves `Ξ_fnl` in that union, so it also solves `Ξ_main`
  there. For a common exponent on a bounded `W`, use the growth estimate from §§7.4–7.7,
  before the local finite-type conclusion. Near each point of the compact closure of `W`, the
  polynomial roots are bounded and some `c_i` is nonzero. Section 7.6 puts *every* uniform-growth
  solution into a single weighted `H^λ` (with §7.7 for the center). On that neighborhood each
  such solution satisfies `f = δ(h(s)) f`, with `h(s)` a finite combination of fixed kernels
  normalized by `c_i(s)`. The smoothing estimate of §7.4(2) puts this image into one growth
  exponent, for every derivative. Only this estimate is needed for the exponent, not the
  injective finite-type witness. Use the matrix-height comparison in the paired Markdown of
  `AdelicLocalFinitenessStatement` and a finite subcover to choose `R₁`. Every regular series
  in `W` is then in `𝔉^R_L` for each `R ≥ R₁`. Restrict (8.2a) and (8.2b) to these spaces;
  the solution containment and automorphy are preserved, as is the singleton at regular
  parameters. This is the fixed-level form used to obtain the Corollary of §8.6.

## Use

`AdelicEisensteinAnalyticSystemReduction` proves `EisensteinAnalyticSystemStatement` from this
statement and `UniformGrowthLocalFinitenessStatement` (BL Theorem 7.2).
