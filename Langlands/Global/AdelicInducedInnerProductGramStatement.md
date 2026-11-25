# Positivity of the inner product on `A^2_P` in Gram form

Module `Langlands.Global.AdelicInducedInnerProductGramStatement` states
`Langlands.Global.InducedInnerProductGramStatement` as a proposition
definition. It supplies no proof. It is stated for
`IntertwiningImaginaryUnitarityStatement`, where it bounds the coefficients
of `M(w, λ)φ` on the imaginary axis.

## Source

E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, Clay Math. Proc. 13 (2011), registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein` (PDF page =
printed page + 9), §2, p.311: `A^n_P` is the space of `φ ∈ A_P` with
`φ(ag) = δ_P(a)^{1/2} φ(g)` for `a ∈ A_M`, and `A^2_P` is the subspace of
those `φ` with `‖φ‖_P^2 := ∫_{A_M P U(𝔸) \ G(𝔸)} |φ(g)|^2 dg < ∞`; "we can
view `A^2_P` as a dense subspace of `Ind_{P(𝔸)}^{G(𝔸)} L^2_disc(A_M M \
M(𝔸))`". The inner product `(·,·)_P` of `A^2_P` is the one of this norm,
`(φ, ψ)_P = ∫_{A_M P U(𝔸) \ G(𝔸)} φ(g) conj ψ(g) dg`.

## Statement

All objects are in the namespace `Langlands.Global` and its
`AdelicGroupPoints` namespace. Data:

- a number field `F : Type`, a connected reductive `G`
  (`IsConnectedReductive G`), a parabolic `p : P → G`
  (`IsParabolicSubgroup p`, a closed immersion) with geometric unipotent
  radical `iU : U → P` (`IsGeometricUnipotentRadical iU`, `iU ≫ p` a closed
  immersion) and rational Levi `l : M → P` (`IsRationalLeviSubgroup l`) with
  `M ⋉ U ≅ P` (`IsIso (subgroupMultiplication l iU)`); all groups affine,
  `G` and `M` locally of finite type (`P` is locally of finite type as a
  closed subgroup, supplied by `haveI`);
- a subgroup `K` of `G(𝔸)` with `hK : IsIwasawaCompact p K` (`K` compact and
  `P(𝔸)K = G(𝔸)`), a matrix representation `rho` and the smooth-structure
  data `hsmooth`, `hcalc` that enter the definition of automorphic forms;
- a Haar measure `μM` on `M(𝔸)`, a linear isomorphism
  `e : ℝⁿ ≃ X^*(P) ⊗ ℝ` and a continuous compactly supported
  `β : ℝⁿ → ℝ` with `∫ β = 1`; they define
  `(φ, ψ)_P = inducedInnerProduct K hK.isCompact p l μM e β φ ψ`;
- `m : ℕ` and `φ : Fin m → (G(𝔸) → ℂ)` with every `φ i ∈ A^2_P`
  (`IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l`).

Conclusion: for every `x : Fin m → ℂ`, with
`H(x) = ∑ i, ∑ i', x i · conj (x i') · (φ i, φ i')_P`,

1. `0 ≤ H(x)` in the order of `ℂ` (scoped `ComplexOrder`), that is, `H(x)` is
   a nonnegative real number;
2. `H(x) = 0` if and only if `∑ i, x i • φ i = 0` as a function on `G(𝔸)`.

## Correspondence with the source

- Sesquilinearity. For `φ, ψ ∈ A^2_P` the integrand of `(φ, ψ)_P` is
  integrable (Cauchy–Schwarz), so `(·,·)_P` is linear in the first and
  conjugate-linear in the second variable and
  `H(x) = (Φ, Φ)_P` for `Φ = ∑ i, x i • φ i ∈ A^2_P`. The statement is
  therefore the positive definiteness of `(·,·)_P` on the span of the `φ i`:
  `(Φ, Φ)_P ≥ 0`, with equality exactly when `Φ = 0`. It is written for
  finite families so that no sesquilinearity has to be assumed.
- The weight `β`. By the Markdown of `Langlands.Global.AdelicInducedInnerProduct`,
  for `φ, ψ ∈ A^n_P` the function `m ↦ m^{-2ρ_P} φ(mk) conj ψ(mk)` is
  invariant under `A_M`, and integrating over the fibres of
  `M(F) \ M(𝔸) → A_M M(F) \ M(𝔸)` gives
  `inducedInnerProduct … φ ψ = (∫ φ conj ψ over A_M U(𝔸) M(F) \ G(𝔸)) · ∫_{𝔞_P} β(y(H)) dH`,
  and the last factor is a positive constant (the ratio of `dH` to the
  Lebesgue measure `dy`) when `∫ β = 1`. So `(·,·)_P` is a positive multiple
  of Lapid's inner product, and positivity does not depend on `β` (which need
  not be nonnegative). This is explanatory.
- Vanishing. `H(x) = 0` gives `Φ = 0` almost everywhere on
  `A_M U(𝔸) M(F) \ G(𝔸)`; `Φ` is continuous (automorphic forms are smooth),
  left `U(𝔸)`-invariant, and `G(𝔸) = P(𝔸) K`, so `Φ = 0` everywhere. This is
  where the hypothesis `hK` is used. This is explanatory.
- The hypotheses keep the setting of `IntertwiningImaginaryUnitarityStatement`
  on its target side (`P'` there): a parabolic with rational Levi and Levi
  decomposition, which makes `A_M` the split component used by `A^n_P` and
  `y` an isomorphism from `A_M` onto `ℝⁿ`. A maximal compact `K` and a closed
  `rho` are not needed for positivity and are not assumed.

## Scope

The statement asserts positivity in Gram form only. It does not assert
sesquilinearity of `inducedInnerProduct`, its independence of `β`, or its
comparison with Lapid's normalization of measures.
