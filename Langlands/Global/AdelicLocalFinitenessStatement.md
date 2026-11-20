# Local finiteness of the system `Ξ_main` (Bernstein–Lapid, Theorem 7.2)

Source: J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), 187–234 (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`; arXiv TeX 1911.02342 in the same
folder). We cite journal pages:

- Example in §3.1, p.192: analytic families of smooth compactly supported functions on `G(𝔸)`;
- §3.4, pp.194–195: Fredholm's criterion and its Corollary;
- §7.1, pp.210–211: the spaces of smooth functions of uniform moderate growth;
- §7.2, pp.211–212: the system `Ξ_main(s)` and Theorem 7.2;
- §7.4, pp.215–217: the spaces `H^λ(X)` and their Lemma (comparison with `𝔉^R`, smoothing,
  compactness); §7.5, Proposition, p.219: the strict embeddings `μ_s`;
- §7.6, pp.219–220: proof of Theorem 7.2 (the passage from the Hilbert spaces `H^λ` back to
  `Ξ_main`, including the modification `v(s) = h(s) + u − u * h(s)`);
- §7.7, pp.220–221: the case `A_G ≠ 1`;
- §8.3, Lemma 8.3, p.223: the Harish-Chandra equations used later.

BL's TeX source writes the system as `\Xi_{\at}`, and its macro `\at` expands to `main`; the
published system is `Ξ_main`. For the comparison of growth scales we also use C. Mœglin and
J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995), I.2.2 (iv) and (vii),
printed pp.20–21 (literature id `moeglin-waldspurger-1995-spectral-decomposition`).

This module states Theorem 7.2 for number fields, in a Fréchet form that its proof gives. It is
a statement only; nothing is proved here. Its intended use is the system `Ξ_fnl(λ)` of §8.4:
the proof of BL's Proposition 8.4 reduces local finiteness of `Ξ_fnl` to this theorem.

## Definitions

Namespace `Langlands.Global.AdelicGroupPoints`.

- `IsAdelicTestFunction F G h`: `h : G(𝔸) → ℂ` is a smooth compactly supported test function,
  an element of BL's `C_c^∞(G(𝔸))` (Example in §3.1). It satisfies the Library's
  `IsAdelicSmoothFunction` (continuous, every infinite slice plot-smooth, right invariant under
  an open subgroup of `G(𝔸_f)`), it has compact support, and it is left invariant under an open
  subgroup of `G(𝔸_f)`. Intersecting the two subgroups makes `h` bi-invariant under one open
  subgroup, as in BL's description of `C_c^∞(G(𝔸))`.
- `rightConvolution F G h f x = ∫_{G(𝔸)} h(g) f(x g) dg`. This is BL's operator `δ(h)` (§7.1,
  "right translation … also for the action of `C_c^∞(G(𝔸))`"). The measure is the Haar measure
  `Measure.haar` of `G(𝔸)`. If the integrand is not integrable, the Bochner integral, and hence
  the value, is `0`. Changing the Haar measure by a factor `c > 0` multiplies every `δ(h)` by
  `c`. The theorem quantifies over all test functions, so the class of systems does not depend
  on this normalization.
- `IsTranslationPolynomialSolution a D φ`: `∑_{k ≤ deg D} D_k φ(a^k g) = 0` for every `g`,
  where `D = ∑_k D_k X^k`. This is the equation `D(L_a) φ = 0` for the left translation
  `(L_a φ)(g) = φ(a g)`.

Namespace `Langlands.Global`.

- `LocalFinitenessData F G Δ r n W` bundles the analytic data of `Ξ_main` over an open set
  `W ⊆ ℂⁿ`. Here `Δ` indexes the simple roots and `r` the central equations. The fields are:
  - an index type `Idx`;
  - for `i ∈ Idx`, test functions `h i k` (`k < m i`) with coefficients `b i k : W → ℂ` and
    a scalar `c i : W → ℂ`;
  - for every `α ∈ Δ`, polynomials `D α s` and a degree `degree α`;
  - for every `j < r`, polynomials `centralD j s` and a degree `centralDegree j`.
- `LocalFinitenessData.IsAdmissible` is BL's list of hypotheses in §7.2:
  - every `h i k` is a test function;
  - `b i k`, `c i` and all polynomial coefficients are holomorphic on `W` (the Library's
    `IsHolomorphicOn` for the model `𝓘(ℂ, ℂⁿ)`);
  - for every `s` some `c i s ≠ 0`;
  - every `D α s` is monic of degree `degree α`;
  - every `centralD j s` is monic of degree `centralDegree j` with nonzero constant coefficient.
- `LocalFinitenessData.solutions X u a z rho hN hrho hsmooth hcalc R L s` is the set of
  solutions of `Ξ_main(s)` in
  `𝔉^R_L = UniformGrowthFrechetSpace F G rho hsmooth hcalc hN hrho R L`, the Library's Fréchet
  space of right `L`-invariant smooth functions of uniform moderate growth with exponent `R`.
  With `f` the function of `v ∈ 𝔉^R_L`, the equations are:
  1. `∑_k b i k s · δ(h i k) f = c i s · f` pointwise on `G(𝔸)`, for every `i`;
  2. `D α s (a α) (C_{U_α} f) = 0` (`IsTranslationPolynomialSolution`) for every `α`, where
     `C_{U_α} f = subgroupConstantTerm F (u α) f` is the Library's constant term along
     `u α : U_α → G`: the integral over `U_α(F) \ U_α(𝔸)` for the quotient Haar measure
     normalized to total mass one;
  3. `centralD j s (z j) f = 0` for every `j < r`.
- `IsLocalFinitenessGroupData iT ν u t z` is BL's group-theoretic data in §7.2, for a maximal
  split torus `iT : T → G` and a generic cocharacter `ν`. The pair fixes the minimal parabolic
  `P_0` and the simple relative roots `Δ₀ = simpleRelativeRoots iT ν`. The predicate says:
  - for every `α ∈ Δ₀`, the functor of points of `u α : U_α → G` is
    `standardUnipotent iT ν (Δ₀ \ {α})`, the unipotent radical of the maximal standard
    parabolic `P_α`;
  - `t α` lies in the positive real subgroup `A_T` of `T(𝔸)`
    (`PositiveRealTorus.intrinsicSubgroup F T`: every character takes positive scalar idele
    values), `β(t α) = 1` for every `β ∈ Δ₀ \ {α}`, `α(t α)` is the positive scalar idele of a
    real `x > 1`, and `H_G(iT(t α)) = 0` (`characterLog`);
  - `z j ∈ A_T` for `j < r`, every simple root (hence every relative root) is `1` on `z j`, and
    the logarithms `H_G(iT(z j))` form a basis of `𝔞_G = Hom(X^*(G), ℝ)`
    (`RealCharacterDual F G`).

  On `A_T` a character equals `1` exactly when its logarithm vanishes. So `a_α = iT(t α)` lies
  in `A_{P_α}^G` (positive real points of the split centre of the Levi of `P_α`, killed by
  `H_G`) with `⟨α, H_0(a_α)⟩ > 0`, and `iT(z j)` lies in `A_G`, as BL require. When `A_G = 1`
  the only choice is `r = 0` and the central equations are absent, as in BL.

## The statement `Langlands.Global.UniformGrowthLocalFinitenessStatement`

Let `G` be connected reductive over a number field `F` (`IsConnectedReductive`, affine and
locally of finite type), `iT` a maximal split torus (`IsMaximalSplitTorus`) and `ν` a generic
cocharacter (`IsGenericCocharacter`). Let `u`, `t`, `z` satisfy `IsLocalFinitenessGroupData`,
and let `X` be admissible data over an open `W ⊆ ℂⁿ`.

Then for every compact open subgroup `L` of `G(𝔸_f)` and every `s₀ ∈ W` there are an open
neighbourhood `U` of `s₀` in `W` and a real `R₀` with the following property. For every
`R ≥ R₀`, the sets `X.solutions u (iT ∘ t) (iT ∘ z) … R L s` are of finite type on `U`
(`IsFiniteTypeOn 𝓘(ℂ, ℂⁿ)`, BL §3.3 Definition (2)). That is, there are `m` and a holomorphic
family of injective operators `ℓ s : ℂ^m → 𝔉^R_L` (`s ∈ U`) whose ranges contain all
solutions.

## Correspondence with the source

- **Twisted action.** BL write the constant-term equation as `D_α(s)(T_{a_α})(C_{G,P_α} f) = 0`
  with the twisted action `T_a φ(g) = δ_{P_α}(a)^{-1/2} φ(a g)` of (6.2), p.201. With
  `κ = δ_{P_α}(a_α)^{-1/2} > 0` and `m = deg D_α` we have
  `D_α(s)(T_{a_α}) = κ^m D̃_α(s)(L_{a_α})`, where `D̃_α(s)(X) = κ^{-m} D_α(s)(κ X)`. This
  polynomial is again monic of degree `m`, its coefficients are holomorphic, and the
  correspondence `D_α ↔ D̃_α` is a bijection (BL compare the two actions themselves at the
  end of §7.5, p.219: `τ_α = δ_P(a_α)^{1/2} T_{a_α}`). The statement therefore quantifies over
  the polynomials `D̃_α` acting through plain left translation. The class of systems, and so the
  theorem, is unchanged. The central equations use plain translation by `z_j` in BL already.
- **Harish-Chandra equations.** BL allow arbitrary holomorphic families `h_i(s)` of
  `C_c^∞(G(𝔸))` (Example in §3.1). Here each family is a finite combination
  `h_i(s) = ∑_k b_{ik}(s) h_{ik}` of fixed test functions with holomorphic coefficients, and
  `δ(h_i(s)) f = ∑_k b_{ik}(s) δ(h_{ik}) f`. Such a family is holomorphic in BL's sense, so the
  statement is a special case of BL's theorem. It covers the use in §8.4: Lemma 8.3 produces
  exactly the equations `∑_{k=1}^{d} b_k(λ) δ(h)^k φ = b_0(λ) φ`, and `δ(h)^k = δ(h^{*k})`.
- **Parameter manifold.** BL allow any complex manifold `𝔐`. Here `𝔐` is an open subset of
  `ℂⁿ`, the case used for parameter spaces `𝔞_{P,ℂ}^*` in linear coordinates.
- **Fréchet form.** BL state local finiteness on `𝔉_umg(G(F) \ G(𝔸))`, the union of the
  spaces `𝔉^R_smth`. The Library has no LF topology on that union (see
  `GroupSchemeUniformGrowthFrechet.md`). The statement is therefore made in the Fréchet spaces
  `𝔉^R_L` of the Library, at a prescribed compact open level `L`, for every sufficiently large
  `R` near each point. The argument below is BL's proof in §7.6 run inside the right
  `L`-invariant vectors. It is recorded to justify the statement; nothing of it is formalized
  here. Fix `L` and `s₀ ∈ W`.
  1. *Localization.* Choose `i` with `c_i(s₀) ≠ 0` and a relatively compact open
     neighbourhood `W₁` of `s₀` in `W` on which `c_i` has no zero. On `W₁` put
     `h(s) = ∑_k b_{ik}(s) c_i(s)^{-1} h_{ik}`, so every solution satisfies `δ(h(s)) f = f`, and
     the coefficients of the `D_α(s)` are bounded on `W₁`. These are the two reductions at the
     start of BL's final step in §7.6.
  2. *Growth scales, inputs.* Let `𝔖` be a Siegel domain. For the height of a closed
     embedding, Mœglin–Waldspurger (1995), I.2.2 (iv), gives `‖g‖ ≪ e^{c'‖H_0(g)‖}` on `𝔖` for
     some `c' > 0`, and `‖g‖` is bounded below (step 7). Hence every derivative of the function
     of `v ∈ 𝔉^R_L` is bounded on `𝔖` by a multiple of `e^{R₊‖H_0‖}` with `R₊ = c' max(R, 0)`:
     the function lies in BL's `𝔉^{R₊}_smth` (any positive exponent if `R₊ = 0`), and it is
     right `L`-invariant. (The comparison of the Library's `adelicSourceNorm` with MW's height is
     recorded in `GroupSchemeUniformGrowthFrechet.md` as a step of the same kind.) So every
     solution in `𝔉^R_L` is a right `L`-invariant solution of BL's system `Ξ_main(s)`.
  3. *The weighted Hilbert space.* Choose `λ` with `e^{⟨λ, H_0(a_α)⟩} > |r|` for every root
     `r` of `D_α(s)` and all `s ∈ W₁`. (When `A_G ≠ 1`, choose the family `λ̲` of §7.7 on the
     orthants.) BL show in §7.6, using the Proposition of §7.5 (p.219), that every solution of
     `Ξ_main(s)` in `𝔉_umg` lies in `H^λ(X)` and solves the system `Ξ^λ(s)`: `μ_s f = ν_s f`,
     with `μ_s` a strict embedding and `ν_s` compact (Lemma (3) of §7.4). This holds whatever
     the growth exponent of the solution.
  4. *Level `L`.* Right translation by `G(𝔸)` acts continuously on `H^λ(X)` (§7.4, p.215).
     Hence the right `L`-invariant vectors `H^λ(X)^L = ⋂_{k ∈ L} ker(δ(k) − 1)` form a closed
     subspace. (For `A_G ≠ 1` the orthants of §7.7 are right `L`-invariant, because `H_G` is
     trivial on the compact group `L`.) The restrictions of `μ_s` and `ν_s` to `H^λ(X)^L` are
     still a strict embedding and a compact operator, holomorphic in `s`. The Corollary to
     Fredholm's criterion (§3.4, p.195; the Library's `FredholmCriterionStatement`) gives an
     open neighbourhood `U₁ ⊆ W₁` of `s₀`, a finite-dimensional space `V` and a holomorphic
     family of injective operators `γ_s : V → H^λ(X)^L` with
     `Sol(Ξ^λ(s)) ∩ H^λ(X)^L ⊆ γ_s(V)` for `s ∈ U₁`. By steps 2 and 3, for every `R` and
     `s ∈ U₁` this set contains the solutions in `𝔉^R_L`.
  5. *Smoothing at level `L`.* Let `e_L` be the normalized Haar measure of `L`, so that
     `δ(e_L) = P_L` is the averaging projection onto `H^λ(X)^L`. Put
     `h_L(s) = e_L * h(s) * e_L`. On right `L`-invariant `f` we have
     `δ(h_L(s)) f = P_L δ(h(s)) f`, so every solution in `𝔉^R_L` satisfies `δ(h_L(s)) f = f`,
     and `δ(h_L(s))` takes values in right `L`-invariant functions. Let `u ≥ 0` be smooth of
     total mass `1` and supported near the identity, `u_L = e_L * u * e_L`, and
     `v(s) = h_L(s) + u_L − u_L * h_L(s)` (BL's modification). Then `δ(v(s)) f = f` whenever
     `δ(h_L(s)) f = f`, so the solutions lie in `δ(v(s)) γ_s(V)`. The finite-dimensional space
     `E = (1 − δ(h_L(s₀))) γ_{s₀}(V)` consists of `L`-invariant vectors, and on it
     `δ(u_L) = P_L δ(u)`. As `u` tends to the Dirac mass, `δ(u) → 1` strongly on `H^λ(X)`, so
     `δ(u_L) → P_L = 1` uniformly on the unit ball of `E`. For `u` close enough to the Dirac
     mass, `δ(v(s₀)) γ_{s₀} = γ_{s₀} + (δ(u_L) − 1)(1 − δ(h_L(s₀))) γ_{s₀}` therefore
     satisfies `‖δ(v(s₀)) γ_{s₀} x − γ_{s₀} x‖ < ‖γ_{s₀} x‖` for `x ≠ 0` in a Hilbert norm of
     `H^λ(X)`, so it is injective as a map `V → H^λ(X)`. All averaging acts on vectors
     already fixed by `L`, so `P_L` kills none of them. A version that averages arbitrary
     vectors of `H^λ(X)` can lose injectivity. (For
     `G = 𝔾_m` over `ℚ` and `L = Ẑ^×`, a nontrivial character of `L` gives an idele class
     character that lies in the range of BL's witness but is killed by `P_L`. It is not right
     `L`-invariant, so it is not a solution in `𝔉^R_L`.)
  6. *Growth scales, outputs.* By Lemma (2) of §7.4 (p.216) there is `R''` such that
     `δ(φ) : H^λ(X) → 𝔉^{R''}_smth` is continuous for every smooth compactly supported `φ`.
     Here `v(s) = ∑_k β_k(s) φ_k` is a finite combination of fixed left `L`-invariant test
     functions `φ_k` (namely `e_L * h_{ik} * e_L`, `u_L` and `u_L * e_L * h_{ik} * e_L`) with
     holomorphic coefficients `β_k` on `U₁`. So `δ(v(s)) γ_s = ∑_k β_k(s) δ(φ_k) γ_s` is a
     holomorphic family `V → 𝔉^{R''}_smth` with values in right `L`-invariant functions. To pass
     to the Library's height, MW I.2.2 (iv) gives `e^{c‖H_0(g)‖} ≪ ‖g‖` on `𝔖` for some
     `c > 0`. So a bound `e^{R''‖H_0‖}` on `𝔖` becomes a bound `‖g‖^{R'}` on `𝔖` with
     `R' = R''/c`. MW I.2.2 (vii) gives `‖g‖ ≪ ‖γ g‖` for `g ∈ 𝔖` and `γ ∈ G(F)`. Since the
     functions and their derivatives are left `G(F)`-invariant (the enveloping algebra acts by
     right derivatives) and `G(F) 𝔖 = G(𝔸)`, the bound extends to all of `G(𝔸)`. This gives a
     continuous inclusion of right `L`-invariant `𝔉^{R''}_smth` into `𝔉^{R'}_L`, and
     `ℓ_s = δ(v(s)) γ_s : V → 𝔉^{R'}_L` is a holomorphic family. It is injective at `s₀`: if
     `ℓ_{s₀} x` is the zero function, it is zero in `H^λ(X)`, so `x = 0` by step 5. On the
     finite-dimensional `V`, injectivity persists on a neighbourhood `U ⊆ U₁` of `s₀`: pick
     continuous linear forms whose matrix against `ℓ_{s₀}` is invertible, and its determinant
     stays nonzero near `s₀`.
  7. *All large `R`.* The Library's norm `‖g‖` is bounded below by a positive constant, being
     a fixed positive multiple of `adelicHeight ≥ 1`. So for `R ≥ R₀ := R'` the inclusion
     `𝔉^{R'}_L ⊆ 𝔉^R_L` is continuous and injective. Composing it with `ℓ_s` gives, for every
     `R ≥ R₀`, a holomorphic family of injective operators `V → 𝔉^R_L` on `U`. By steps 4 and
     5, its ranges contain the solutions in `𝔉^R_L`. Neither `U` nor `V` depends on `R`.
- The elements `a_α` and `z_j` are fixed "once and for all" in BL. The statement quantifies
  over all admissible choices, and BL's theorem holds for each choice.

## Scope

Only Theorem 7.2 is stated. The weighted spaces `H^λ`, the Harish-Chandra decomposition and
the Fredholm argument of §§7.3–7.6 are not formalized here. The Library's
`FredholmCriterionStatement` is BL's §3.4 criterion used in §7.6.
