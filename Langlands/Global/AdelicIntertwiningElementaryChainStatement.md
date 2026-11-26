# Standardization and elementary decomposition of intertwining operators

Module `Langlands.Global.AdelicIntertwiningElementaryChainStatement`. It contains one
reducible definition, `StandardParabolicFamily.rootPresentation`, and two statements,
`Langlands.Global.IntertwiningStandardizationStatement` and
`Langlands.Global.IntertwiningElementaryChainStatement`. It proves nothing.

Both statements are structural. They involve the defining intertwining integrals on regions
of regular parameters only, never a meromorphic continuation. With the meromorphic
continuation of intertwining operators (`IntertwiningMeromorphicContinuationStatement`) and
their cocycle relation (`IntertwiningCocycleStatement`), they give the root factorization
`IntertwiningRootFactorizationStatement`. That implication is the theorem
`intertwiningRootFactorization_of_inputs` of the module
`Langlands.Global.AdelicIntertwiningRootFactorizationAssembly`.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), registered as
  `bernstein-lapid-2024-meromorphic-continuation-eisenstein` (publication folder, fingerprint
  `58ab0c92242c29f17cc38fcfde3d73082e15f023a033c1c808282eb783f293b1`; PDF
  `Bernstein-Lapid--On the meromorphic continuation of Eisenstein series--2024.pdf`, SHA-256
  `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`, journal pagination;
  TeX `1911.02342.tex` for line numbers):
  - §2.1, p. 190 (TeX lines 403–406): a maximal compact subgroup `K` "in a good position" with
    respect to `M₀`, so that `G(𝔸) = M(𝔸)U(𝔸)K` for every standard `P`;
  - §2.2, p. 191 (TeX lines 425–437): `[M(w, λ)φ]_{wλ}(g) = ∫ φ_λ(w⁻¹ug) du` over
    `(wU_Pw⁻¹ ∩ U_Q)(𝔸) \ U_Q(𝔸)`, convergent for `⟨Re λ, α^∨⟩ ≫ 0` when `α ∈ Φ_P`, `wα < 0`;
  - §8.6, pp. 225–226 (TeX lines 3517–3523): "If `w` is an elementary symmetry `s_α` for some
    `α ∈ Δ_P`, then as a function of `λ ∈ 𝔛_P`, `M(w, λ)` depends only on `⟨λ, α^∨⟩`. In
    general, by decomposing `w` into elementary symmetries [MW, I.1.8] and using the
    multiplicativity of intertwining operators (cf. [MW, II.1.6]), it follows that the
    singularities of `M(w, λ)` are of the form `⟨λ, β^∨⟩ = c` for some `β ∈ Φ_P` such that
    `wβ < 0` and `c ∈ ℂ`."
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition` (folder SHA-256
  `1ba99fb90916a687503e88c7191dad43b9c4865b68e6b4221a4f2126f2d2f141`):
  - I.1.4, pp. 4–5 (maximal compact subgroups in good position) and I.1.8, Lemma (c), pp. 14–15
    (chapter file `05.1_pp_1_18_Hypotheses_and_general_notation.pdf`, SHA-256
    `f629f59c8774b80b155f60ef935ceccd4c5c5c1e87a1ea793baec0875749e770`): for `w ∈ W(M)` there
    are standard Levis `M₀ = M, M₁, …, M_l = wMw⁻¹`, `l = ℓ(w)`, and roots `α_j` with
    `M_j = s_{α_j} M_{j-1} s_{α_j}⁻¹` and `w = s_{α_l} ⋯ s_{α_1}`;
  - II.1.6, pp. 87–90 (chapter file `06.1_pp_78_100_Definitions.pdf`, SHA-256
    `948dbfd356c2f068c1dc793a52e4c700334eb5236b740f1c775da535b747111c`): the intertwining
    operators, their convergence and their multiplicativity when lengths add.

Provenance: derived. Bernstein–Lapid work with standard parabolics and one compact in good
position, and do not state either assertion as a separate result. Of the compact, both
statements use only that it is a maximal compact subgroup with Iwasawa coverage
`P_J(𝔸)K₀ = G(𝔸)` for every standard parabolic `P_J`. A compact in good position has these
properties; its further properties, about its intersections with the standard Levis, are
neither required nor provided by the statements. The Library's intertwining
statements allow an arbitrary presented parabolic `P`, an arbitrary target parabolic `Q` and an
arbitrary maximal compact subgroup `K` with `P(𝔸)K = Q(𝔸)K = G(𝔸)`. The first statement is the
passage from that setting to Bernstein–Lapid's. The second is the decomposition and the
rank-one dependence quoted from §8.6, restricted to the regular region where the operators are
the defining integrals.

## `StandardParabolicFamily.rootPresentation`

For a standard parabolic family `fam` (module `Langlands.Global.AdelicLeadingCuspidalComponents`)
and a standard index `J`, the root presentation of `fam.p J` with the family's maximal split
torus `fam.i`, generic cocharacter `fam.ν`, set of simple roots `J` and map `fam.f J` of split
tori. Its compatibility is `fam.isCompatible J`. It is an `abbrev`, so its torus inclusion is
recognised as `fam.i` by instance search.

## `IntertwiningStandardizationStatement`

The binders and hypotheses are exactly those of `IntertwiningRootFactorizationStatement`: the
parabolics `P = MU` (presentation `r`) and `Q = M'V`, `(w, c)` presenting an element of
`W(P, Q)`, the retraction `π'`, a maximal compact `K` with `hK`, `hK'`, a closed matrix
embedding `rho` and `φ` automorphic on `U(𝔸)M(F) \ G(𝔸)` for the archimedean part of `K`.

**Assertion.** There are a standard parabolic family `fam` with indices `I`, `I'`, a subgroup
`K₀` with `hK₀ : ∀ J, IsIwasawaCompact (fam.p J) K₀`, a rational point `w₀` with an isomorphism
`c₀ : M_{I'} → M_I`, a retraction `π₀` of `fam.l I'`, a complex linear isomorphism
`iota : X^*(P) ⊗ ℂ ≃ X^*(P_I) ⊗ ℂ`, and, for `j : Fin m`, functions `E j` on `X^*(P) ⊗ ℂ`,
`h j` on `G(𝔸)`, maps `τ j : G(𝔸) → G(𝔸)` and functions `φ₀ j` on `G(𝔸)` such that:

1. `K₀` is a maximal compact subgroup of `G(𝔸)`;
2. `IsWeylConjugation (fam.p I) (fam.l I) (fam.p I') (fam.l I') w₀ c₀` and
   `fam.l I' ≫ π₀ = 𝟙`;
3. every `φ₀ j` is automorphic on `U_I(𝔸)M_I(F) \ G(𝔸)` for the archimedean part of `K₀`
   (same `hsmooth`, `hcalc`, `rho`);
4. every `E j` is complex differentiable in every linear coordinate system;
5. there are instances `Fintype (relativeWeylGroup fam.i)`,
   `∀ J, IsClosedImmersion (fam.p J)` and `∀ J, Mono (fam.f J)`, used to form the standard
   operators, such that, with `r₀ = fam.rootPresentation I`:
   - for every `R` there is `R'` with: `R'`-regular for `r` implies `iota λ` `R`-regular for
     `r₀`;
   - for every root `β₀ ∈ r₀.unipotentRoots` there is `β ∈ r.unipotentRoots` such that
     `r.rootFunctional hA hT β ν = 0` implies `r₀.rootFunctional β₀ (iota ν) = 0`;
   - there is `R` such that for every `R`-regular `λ` and every `g`,
     `M(w, λ)φ (g) = ∑ j, E j λ * h j g * M₀(w₀, iota λ)(φ₀ j)(τ j g)`, where
     `M₀ = (hK₀ I).intertwiningOperator (hK₀ I') (fam.iU I) (fam.l I) (fam.iU I') c₀ π₀ w₀`.

### Why it holds

This explains the truth of the statement; the module contains no proof.

- The presentation `r` determines a standard family in which `P` is the standard parabolic of
  its simple roots, as in the Markdown of `EisensteinStandardizationStatement` (module
  `Langlands.Global.AdelicEisensteinStandardizationStatement`); `iota` is the restriction of
  characters along the identification, and the regular regions correspond.
- The target `Q` is `G(F)`-conjugate to a standard parabolic `P_{I'}`. Conjugating the target
  by a rational point changes the normalized operator by an exponential of a linear form in
  `λ` and translates the argument (see the Markdown of the module
  `Langlands.Global.AdelicIntertwiningConjugateTarget`). Changing the representative of the
  Weyl element by rational points of the Levis does not change the operator.
- A maximal compact subgroup `K₀` in good position (Mœglin–Waldspurger I.1.4) satisfies
  `P_J(𝔸)K₀ = G(𝔸)` for every standard `J`. Its archimedean part is conjugate to that of `K`
  by a point `t` of `G(F_∞)`. Replacing `K` by `tKt⁻¹` multiplies the operator by the
  exponential of a linear form in `λ` (heights of `t` for `P` and for the target) and
  translates the argument by `t`. A change of the finite part writes `φ_λ` as a finite sum of
  exponentials `e^{⟨λ, v⟩}` times twists of automorphic cut-offs. The target heights for the
  two compacts differ by finitely many values, which gives functions `h j` of `g` (indicator
  functions) with entire coefficients (see the Markdown of
  `Langlands.Global.AdelicEisensteinFiniteCompactOperatorComparison` for the finite change of
  compact of the intertwining operators).
- The coefficients `E j` are exponentials of linear forms, hence entire. Root forms of `r₀` and
  `r` have the same kernels on the identified parameter spaces: the roots of the split
  component in the unipotent radical correspond, and the kernel of `λ ↦ B(λ|_A, β)` does not
  depend on the choice of maximal split torus or Weyl-invariant positive form. The form
  `B(·, β̃)` of a root `β̃` vanishes on Weyl invariants and is a positive multiple of a fixed
  form on the irreducible component containing `β̃`.

## `IntertwiningElementaryChainStatement`

**Setting.** A number field `F`, an affine group scheme `G` of finite type, a standard
parabolic family `fam` with the three instances above, a subgroup `K` with
`hK : ∀ J, IsIwasawaCompact (fam.p J) K` that is maximal compact, indices `I`, `I'`, `(w, c)`
with `IsWeylConjugation (fam.p I) (fam.l I) (fam.p I') (fam.l I') w c`, and a retraction `π`
of `fam.l I'`.

**Assertion.** There are `n`, indices `J : Fin n → StandardIndex`, written with
`J' = Fin.cons I J` (so `J' 0 = I`), steps `ws t` and `cs t : M_{J' (t+1)} → M_{J' t}` for
`t : Fin n`, partial composites `W t` and `C t : M_{J' t} → M_I` for `t : Fin (n + 1)`, and
retractions `πs t` of `fam.l (J' t)`, such that:

1. `W 0 = 1`, `C 0 = 𝟙`, `W (t+1) = ws t * W t` and `C (t+1) = cs t ≫ C t`;
2. `fam.l (J' t) ≫ πs t = 𝟙` and the multiplication `M_{J' t} × U_{J' t} → P_{J' t}` is an
   isomorphism, for every `t`;
3. `IsWeylConjugation (fam.p (J' t)) (fam.l (J' t)) (fam.p (J' (t+1))) (fam.l (J' (t+1)))
   (ws t) (cs t)` for every `t : Fin n`;
4. for every step `t` there is `α ∈ (fam.rootPresentation (J' t)).unipotentRoots` such that
   - there is `R` with: if `μ` and `μ + ν` are `R`-regular for `fam.rootPresentation (J' t)`
     and the root form of `α` vanishes at `ν`, then for every function `ψ` and every `g` the
     step operator `(hK (J' t)).intertwiningOperator (hK (J' (t+1))) … (cs t) (πs (t+1)) (ws t)`
     takes the same value at `μ + ν` and at `μ`;
   - there is `β ∈ (fam.rootPresentation I).unipotentRoots` such that the vanishing of the root
     form of `β` at `ν ∈ X^*(P_I) ⊗ ℂ` implies the vanishing of the root form of `α` at
     `weylParameter (fam.l I) (C t) (πs t) ν`;
5. there is `R` such that for every `R`-regular `μ` for `fam.rootPresentation I`, every function
   `ψ` left invariant under `U_I(𝔸)M_I(F)` and every `g`, the operator of `(w, c, π)` from `P_I`
   to `P_{I'}` equals the operator of `(W n, C n, πs n)` from `P_I` to `P_{J' n}`.

### Why it holds

This explains the truth of the statement; the module contains no proof.

- **Decomposition.** The element of `W(M_I, M_{I'})` presented by `w` is a product
  `s_{α_n} ⋯ s_{α_1}` of elementary symmetries through standard Levis (Mœglin–Waldspurger
  I.1.8 (c)); choose rational representatives `ws t`. The partial composites satisfy the
  Weyl conjugation property by composition (`AdelicGroupPoints.IsWeylConjugation.comp`,
  module `Langlands.Global.AdelicWeylSetAssociation`). Since `w` and
  `W n` present the same element they differ by rational points of the Levis, and the
  substitution `v ↦ m' v m'⁻¹` in the integral, the left invariance of `ψ_μ` under `M_I(F)`
  and the left invariance of the target height under rational points give clause 5.
- **Rank-one invariance.** The step `t` lies in the rational points of the Levi `M_L` of
  `L = J' t ∪ {α_t}`, and `P_{J' t}`, `P_{J' (t+1)} ⊆ P_L`. A parameter `ν` restricted from
  `X^*(P_L) ⊗ ℂ` has `m_{P_{J' t}}^ν = m_{P_L}^ν` (with the same `K`), which is left invariant
  under `w⁻¹v` for `v` in the unipotent radical of the target and `w ∈ M_L(F)`. The integrand at
  `μ + ν` is therefore `m_{P_L}(g)^ν` times the integrand at `μ`. The normalizing factor at the
  target contributes `m_{P_L}(g)^{-ν}`, because the Weyl parameter of `ν` is again the
  restriction of the same character of `M_L`. So the two values agree. The image of
  `X^*(P_L) ⊗ ℂ` has codimension one and lies in the kernel of the root form of `α_t`
  restricted to the split component (a character of `M_L` is invariant under `s_{α_t}`, so it
  is orthogonal to `α_t` for the Weyl-invariant form), hence equals that kernel. Bernstein–Lapid
  §8.6 state this dependence "only through `⟨λ, α^∨⟩`".
- **Transport.** All presentations of the family share the maximal split torus `fam.i` and its
  Weyl-invariant form. The Weyl parameter map of `(W t, C t)` is a linear equivalence
  (`exists_weylParameter_linearEquiv`, module `Langlands.Global.AdelicWeylParameterEquivalence`)
  given by a rational point that may be taken in the normalizer of the torus. It carries the
  kernel of the root form of `β_t = ± W_t⁻¹ α_t`, a root of the split component of `P_I`, onto
  the kernel of the root form of `α_t`. Bernstein–Lapid's `⟨w_{t-1}λ, α_t^∨⟩ = ⟨λ, β_t^∨⟩`.

## Scope

- Neither statement asserts anything about continued operators; agreement is required only on
  regions of regular parameters.
- The invariance in clause 4 is stated for all functions `ψ` and the identity in clause 5 for
  left invariant functions; both are exact identities of the defining integrals.
