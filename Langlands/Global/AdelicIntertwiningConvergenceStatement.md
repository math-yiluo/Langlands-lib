# Absolute convergence of intertwining integrals

Module `Langlands.Global.AdelicIntertwiningConvergenceStatement` states
`Langlands.Global.IntertwiningAbsoluteConvergenceStatement` as a proposition
definition. It supplies no proof.

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein
  series*, 1995, registered as `moeglin-waldspurger-1995-spectral-decomposition`,
  chapter file `06.1_pp_78_100_Definitions.pdf`, II.1.6, printed pp.87–88,
  Proposition (i): for standard `P = MU`, `P' = M'U'` and `w ∈ G(k)` with
  `wMw⁻¹ = M'`, the integral
  `∫_{(U'(k) ∩ wU(k)w⁻¹) \ U'(𝔸)} φ_π(w⁻¹ u g) du` converges absolutely and
  uniformly for `g` in a compact set if `⟨Re π, α^∨⟩ ≫ 0` for every positive
  simple root `α` of `G` relative to `M`. Part (iv) weakens the condition to
  the roots `α > 0` with `wα < 0`. The proof bounds the integral, uniformly
  for `g` in a compact set, by
  `∫_{U'(k) \ U'(𝔸)} ∑_{γ ∈ P(k) \ G(k)} |φ_π(γ u g)| du` (citing II.1.7 (4)
  and (6)) and applies II.1.5.
- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
  series*, J. Amer. Math. Soc. 37 (2024), registered as
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §2.2, p.191:
  the integral defining `M(w, λ)` converges locally uniformly in `g` and `λ`
  provided `⟨Re λ, α^∨⟩ ≫ 0` for every root `α ∈ Φ_P` with `wα < 0`, citing
  MW II.1.6.

## Statement

The data for `G`, `P`, `M`, `U`, `A`, `p`, `iU`, `l`, `a`, the presentation
`r : ParabolicRootPresentation p l a`, the split-torus proofs `hA`, `hT`,
the compact `K` with `hK : IsIwasawaCompact p K`, `rho`, `hsmooth`, `hcalc`
and `φ` are those of `Langlands.Global.EisensteinAbsoluteConvergenceStatement`
(module `Langlands.Global.AdelicEisensteinConvergenceStatement`), with the
same hypotheses: `G` connected reductive, `iU` a geometric unipotent radical
of `P`, `K` maximal compact, `rho` a closed embedding, and `φ` an
automorphic form on `U(𝔸)M(F) \ G(𝔸)` for the archimedean part of `K`. The
presentation makes `P` a standard parabolic with rational Levi `M` and
split component `A`.

In addition the statement quantifies group schemes `Q`, `M'`, `V`, maps
`q : Q → G`, `iV : V → Q`, `l' : M' → Q` with `iV ≫ q` a closed immersion,
a point `w` of `G` over `Spec F` and a map `c : M' → M`, and assumes:

- `IsParabolicSubgroup q`;
- `LeviSubgroup.IsGeometricUnipotentRadical iV`, so `V` is the unipotent
  radical of `Q`;
- `IsRationalLeviSubgroup l'` and `IsIso (subgroupMultiplication l' iV)`, so
  `Q = M' ⋉ V`;
- `IsWeylConjugation p l q l' w c` (module
  `Langlands.Global.AdelicIntertwiningOperator`): `c` is an isomorphism with
  `l(c(m')) = w⁻¹ l'(m') w`, so `wMw⁻¹ = M'`.

The conclusion: there is a real `R` such that for every compact
`C ⊆ G(𝔸)`, every linear coordinate system `e : ℂⁿ ≃ X^*(P) ⊗ ℂ` and every
compact `Λ ⊆ ℂⁿ` on which every `λ = e(s)`, `s ∈ Λ`, is `R`-regular
(`r.IsRegularParameter hA hT R λ`: `R < B(Re λ|_A, α)` for all
`α ∈ r.unipotentRoots`, as in the Eisenstein convergence statement), there
is a function `b` on
`(V(F) ∩ wU(𝔸)w⁻¹) \ V(𝔸)`, integrable for `intertwiningMeasure` (the
quotient of the Haar measure of `V(𝔸)` normalized by
`vol(V(F) \ V(𝔸)) = 1`), with `‖φ_λ(w⁻¹ v_x g)‖ ≤ b(x)` for every class `x`,
every `g ∈ C` and every `s ∈ Λ`. The left side is
`hK.intertwiningIntegrand iU (iV ≫ q) w φ (e s) g x`, with `v_x` the chosen
representative of `x`. The region is the one of the Eisenstein statement:
`B` is `Langlands.Plancherel.weylInducedCharacterForm hA hT r.data.f r.data.i`,
`Re λ` is `parameterRealPart` and `Re λ|_A` is
`realParameterRestriction (a ≫ l)`.

## Correspondence with the source

- Domination. One integrable majorant on `C × Λ` gives absolute convergence
  of the integral, uniformly for `g ∈ C` and `λ ∈ Λ`, by dominated
  convergence; this is MW's "absolutely and uniformly" and BL's "locally
  uniformly in `g` and `λ`". The majorant form is slightly stronger than
  those words, and it is what MW's proof gives: the quotient map
  `(V(F) ∩ wU(F)w⁻¹) \ V(𝔸) → V(F) \ V(𝔸)` unfolds the integral of
  `sup_{g ∈ C, λ ∈ Λ} |φ_λ(w⁻¹ v g)|` into an integral over the compact
  `V(F) \ V(𝔸)` of a sum over distinct cosets in `P(F) \ G(F)`, and the
  normal convergence of the Eisenstein series on the compact set `Ω C × Λ`,
  for a compact `Ω ⊆ V(𝔸)` mapping onto `V(F) \ V(𝔸)`, bounds that sum.
  This argument is explanatory and not proved here.
- The region. As explained in the Markdown of the Eisenstein statement, the
  condition `B(Re λ|_A, α) > R` for all roots of `A` in `U`, with `R` large,
  is MW (i)'s `⟨Re λ, α^∨⟩ ≫ 0` for the simple roots. It constrains every
  root of `P`, not only those with `wα < 0`. So the statement is a consequence
  of BL's and MW (iv)'s sharper claim, with a smaller region; the sharper
  region is not stated here.
- The parabolic `Q`. MW and BL take `Q` standard. Here `Q` is any parabolic
  with a rational Levi `M'` conjugate to `M` by the rational point `w`. This
  is no stronger: there is `γ ∈ G(F)` with `γQγ⁻¹` standard and
  `γM'γ⁻¹` its standard Levi (all minimal parabolics are `G(F)`-conjugate,
  and rational Levis of a parabolic are conjugate under the rational points
  of its unipotent radical). Conjugation by `γ` maps `V(F)` onto the
  rational points of `γVγ⁻¹`, so it carries the normalized Haar measure of
  `V(𝔸)` to that of `(γVγ⁻¹)(𝔸)` and `V(F) ∩ wU(𝔸)w⁻¹` to the
  corresponding subgroup for `γw`; the substitution
  `v = γ⁻¹ v' γ` turns the integrand for `(Q, w)` at `g` into the one for
  `(γQγ⁻¹, γw)` at `γg`. Since `γC` is compact, the statement for standard
  `Q` gives it for `Q`. This reduction is explanatory and not proved here.
- `π'` and `K` for `Q`. The integrand does not involve `wλ`, `m_Q` or the
  Levi projection `π'`, so the statement needs neither `π'` nor
  `IsIwasawaCompact q K`.
- "Sufficiently regular" is the existential `R`, which may depend on `φ`, and
  compact sets of `λ` are expressed in linear coordinates, as in the
  Eisenstein statement.
- The compact subgroup `K` need not be in good position with respect to a
  minimal Levi, as BL assume; the Markdown of the Eisenstein convergence
  statement explains the reduction to their case.

## Scope

Holomorphy of `λ ↦ M(w, λ)φ`, the facts that `M(w, λ)φ ∈ 𝒜_Q` and that it
depends only on `M'(F) w M(F)`, the cuspidal pairing bound of MW II.1.6
(ii), the precise region `⟨Re λ, α^∨⟩ > ⟨ρ_P, α^∨⟩` of MW (iii) for
unitary cuspidal data, and the meromorphic continuation (BL Theorem 2.3 (3))
are not part of this statement.
