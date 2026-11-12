# Meromorphic continuation of intertwining operators

Module `Langlands.Global.AdelicIntertwiningContinuationStatement` states
`Langlands.Global.IntertwiningMeromorphicContinuationStatement` as a
proposition definition. It supplies no proof.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, Theorem 2.3 (3)
(§2.3, journal p.191): for any `w ∈ W(P, Q)`, the map `λ ↦ M(w, λ)φ`,
taking values in a finite-dimensional linear subspace of `𝒜_Q`, admits a
meromorphic continuation to `𝔛_P`. Only the number field case is stated
here; BL's rationality in the function field case is not.

## Statement

The data and hypotheses are those of
`Langlands.Global.IntertwiningAbsoluteConvergenceStatement` (module
`Langlands.Global.AdelicIntertwiningConvergenceStatement`): `G` connected
reductive, a standard parabolic `P = MU` with presentation
`r : ParabolicRootPresentation p l a`, a parabolic `q : Q → G` with
unipotent radical `iV : V → Q` and rational Levi `l' : M' → Q`,
`Q = M' ⋉ V`, a pair `(w, c)` with `IsWeylConjugation p l q l' w c`, a
maximal compact `K` with `hK : IsIwasawaCompact p K`, a closed matrix
embedding `rho` and an automorphic form `φ` on `U(𝔸)M(F) \ G(𝔸)`. In
addition:

- `q` is a closed immersion, and `Q` is affine;
- `hK' : IsIwasawaCompact q K`, i.e. `Q(𝔸)K = G(𝔸)`, which defines `m_Q`;
- `π' : Q → M'` satisfies `l' ≫ π' = 𝟙 M'`, so it is the Levi projection
  `Q → Q/V ≅ M'` and `weylParameter l c π'` is BL's `λ ↦ wλ` (see the
  Markdown of `Langlands.Global.AdelicIntertwiningOperator`).

The conclusion: there are `k : ℕ`, functions `ψ i` on `G(𝔸)`
(`i : Fin k`), functions `coeff i` on `X^*(P) ⊗ ℂ` and a set `D` such that

- each `ψ i` is an automorphic form on `V(𝔸)M'(F) \ G(𝔸)`:
  `IsAutomorphicFunctionOn` for `parabolicQuotientSubgroup F q iV l'` and
  the archimedean part `K.comap (ofInfinite F G)` of `K`, i.e. `ψ i ∈ 𝒜_Q`;
- each `coeff i` is meromorphic on `X^*(P) ⊗ ℂ` with domain of holomorphy
  `D`, in every linear coordinate system (`IsMeromorphicInCoordinatesOn`
  of `Langlands.Analysis.Meromorphic.LinearCoordinates`);
- there is `R₀` such that for every `λ` with `r.IsRegularParameter hA hT R₀ λ`
  (`R₀ < B(Re λ|_A, α)` for all `α ∈ r.unipotentRoots`) and every
  `g ∈ G(𝔸)`,
  `hK.intertwiningOperator hK' iU l iV c π' w φ λ g = ∑ i, coeff i λ * ψ i g`.

The left side is `M(w, λ)φ(g) = m_Q(g)^{-wλ} ∫ φ_λ(w⁻¹ v g) dv`. The region
and the form `B` are those of the convergence statements.

## Correspondence with the source

- Finite-dimensional values. A function with values in a
  finite-dimensional space `W ⊆ 𝒜_Q` is meromorphic exactly when its
  coefficients in a basis of `W` are, because `W` carries its unique
  Hausdorff vector topology. The statement uses a spanning family
  `ψ i` of such a `W` and the coefficients `coeff i`; linear independence
  is not required, since meromorphic coefficients for a spanning family give
  meromorphic coefficients for a basis. The values at regular `λ` of the
  continuation are then `∑ i, coeff i λ • ψ i ∈ 𝒜_Q`.
- The continuation is determined by its values on the region `R₀`: two
  meromorphic functions on `ℂⁿ` that agree on a nonempty open set agree on
  the intersection of their domains of holomorphy. The region is the
  Eisenstein region `⟨Re λ, α^∨⟩ ≫ 0` for all simple roots (see the
  Markdown of the Eisenstein convergence statement), on which the
  intertwining integral converges; it is contained in BL's region
  `⟨Re λ, α^∨⟩ ≫ 0` for the roots with `wα < 0`.
- `Q` need not be standard. As explained for the convergence statement,
  there is `γ ∈ G(F)` taking `(Q, M', V)` to a standard parabolic with its
  standard Levi and unipotent radical. Since `Q(𝔸)K = G(𝔸)` and `H_Q` is
  right `K`-invariant, `H_{γQγ⁻¹}(γg)` is the transport of `H_Q(g)` plus the
  constant `H_{γQγ⁻¹}(γ)`, so `M(w, λ)φ(g)` is the entire factor
  `exp⟨(γw)λ, H_{γQγ⁻¹}(γ)⟩` times `M(γw, λ)φ(γg)`, and left translation by
  `γ` maps `𝒜_{γQγ⁻¹}` onto `𝒜_Q`. The standard case of BL therefore gives
  the general one. This reduction is explanatory and not proved here.
- `π'` enters only through `wλ`, which is independent of the retraction.
- The compact subgroup `K` need not be in good position with respect to a
  minimal Levi, as BL assume; the Markdown of the Eisenstein convergence
  statement explains the reduction to their case.

## Scope

Holomorphy on the region of convergence, the functional equation
(BL 2.3 (4)), the cocycle relation (2.3 (5)) and the location of the
singularities along root hyperplanes (2.3 (6)) are not part of this
statement.
