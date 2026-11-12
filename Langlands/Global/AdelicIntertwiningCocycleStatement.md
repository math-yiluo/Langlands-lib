# Cocycle relation of intertwining operators

Module `Langlands.Global.AdelicIntertwiningCocycleStatement` states
`Langlands.Global.IntertwiningCocycleStatement` as a proposition definition.
It supplies no proof.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`:

- Theorem 2.3 (5), journal p.191 (PDF page 5): for any `w ∈ W(P, Q)` and
  `w' ∈ W(Q, Q')`, `M(w'w, λ) = M(w', wλ) ∘ M(w, λ)` for `λ ∈ 𝔛_P`, as an
  identity of the meromorphic continuations of Theorem 2.3 (3).
- §2.1, p.190: `W(P, Q)` is the set of cosets `wM_P(F)` with `w ∈ G(F)` and
  `wM_Pw⁻¹ = M_Q`.
- §8.6, journal p.225 (PDF page 39): the relation is deduced from the
  functional equation (Theorem 2.3 (4)) and the injectivity (8.4) of
  `φ ↦ E(φ, λ)` on finite-dimensional subspaces of `𝒜_P`; no condition on
  the lengths of `w`, `w'` and `w'w` is imposed.

Only the number field case is stated. The Library's name for BL's `Q'` is
`Q''`.

## Statement

The data are those of the intertwining statements (modules
`Langlands.Global.AdelicIntertwiningOperator`,
`Langlands.Global.AdelicIntertwiningConvergenceStatement` and
`Langlands.Global.AdelicIntertwiningContinuationStatement`), applied twice:

- `G` connected reductive over a number field `F`;
- `P = MU` with presentation `r : ParabolicRootPresentation p l a` and `iU`
  a geometric unipotent radical of `P`;
- `Q = M'V` with its own presentation
  `r' : ParabolicRootPresentation q l' a'`, `q` and `iV ≫ q` closed
  immersions, `Q` and `V` affine, `iV` a geometric unipotent radical, and
  `π' : Q → M'` with `l' ≫ π' = 𝟙 M'`;
- `Q'' = M''V''` a parabolic subgroup (`IsParabolicSubgroup q''`, `q''` a
  closed immersion) with geometric unipotent radical `iV''`, rational Levi
  `l''`, `Q'' = M'' ⋉ V''` (`IsIso (subgroupMultiplication l'' iV'')`),
  `iV'' ≫ q''` a closed immersion, `Q''` and `V''` affine, and
  `π'' : Q'' → M''` with `l'' ≫ π'' = 𝟙 M''`;
- `(w, c)` with `IsWeylConjugation p l q l' w c` and `(w', c')` with
  `IsWeylConjugation q l' q'' l'' w' c'`, representing `w ∈ W(P, Q)` and
  `w' ∈ W(Q, Q'')`;
- `K` maximal compact in `G(𝔸)` with `P(𝔸)K = Q(𝔸)K = Q''(𝔸)K = G(𝔸)`
  (`hK`, `hK'`, `hK''`), a closed matrix embedding `rho`, the
  smooth-structure data `hsmooth`, `hcalc`, and `φ ∈ 𝒜_P`
  (`IsAutomorphicFunctionOn` for `parabolicQuotientSubgroup F p iU l` and
  the archimedean part `K.comap (ofInfinite F G)` of `K`).

The composite element of `W(P, Q'')` is the pair `(w' * w, c' ≫ c)`, where
`w' * w` is the product of the rational points `w', w : Spec F → G` (the
monoid structure on morphisms into a group object). It satisfies
`IsWeylConjugation p l q'' l'' (w' * w) (c' ≫ c)`: from
`c ≫ l ≫ p = l' ≫ q ≫ (innerIso w).inv` and
`c' ≫ l' ≫ q = l'' ≫ q'' ≫ (innerIso w').inv` one gets
`c' ≫ c ≫ l ≫ p = l'' ≫ q'' ≫ (innerIso w').inv ≫ (innerIso w).inv`, and
`(innerIso w').inv ≫ (innerIso w).inv = (innerIso (w' * w)).inv` by the
Library lemma `GroupScheme.innerIso_mul_hom`. This fact is not used as a
hypothesis and is not proved here.

The statement is universal in the continuations. It quantifies

1. `k`, `ψ : Fin k → (G(𝔸) → ℂ)`, `coeff : Fin k → (X^*(P) ⊗ ℂ → ℂ)` and
   `D` such that every `ψ i ∈ 𝒜_Q` (`IsAutomorphicFunctionOn` for
   `parabolicQuotientSubgroup F q iV l'`), every `coeff i` is meromorphic
   with domain of holomorphy `D` (`IsMeromorphicInCoordinatesOn`, module
   `Langlands.Analysis.Meromorphic.LinearCoordinates`), and for some `R`,
   `hK.intertwiningOperator hK' iU l iV c π' w φ λ g = ∑ i, coeff i λ * ψ i g`
   for every `g` whenever `r.IsRegularParameter hA hT R λ`;
2. `k'`, `χ : Fin k' → (G(𝔸) → ℂ)`,
   `coeff' : Fin k → Fin k' → (X^*(Q) ⊗ ℂ → ℂ)` and `D'` such that every
   `coeff' i j` is meromorphic with domain `D'`, and for each `i` there is
   `R` with
   `hK'.intertwiningOperator hK'' iV l' iV'' c' π'' w' (ψ i) μ g = ∑ j, coeff' i j μ * χ j g`
   for every `g` whenever `r'.IsRegularParameter hA' hT' R μ`;
3. `k''`, `χ'' : Fin k'' → (G(𝔸) → ℂ)`,
   `coeff'' : Fin k'' → (X^*(P) ⊗ ℂ → ℂ)` and `D''` such that every
   `coeff'' j` is meromorphic with domain `D''`, and for some `R`,
   `hK.intertwiningOperator hK'' iU l iV'' (c' ≫ c) π'' (w' * w) φ λ g = ∑ j, coeff'' j λ * χ'' j g`
   for every `g` whenever `λ` is `R`-regular for `r`.

The conclusion: for every `λ ∈ D ∩ D''` with `wλ ∈ D'` and every
`g ∈ G(𝔸)`,

`∑ j, coeff'' j λ * χ'' j g = ∑ i, coeff i λ * ∑ j, coeff' i j (wλ) * χ j g`,

where `wλ = weylParameter l c π' λ` (`χ ↦ χ ∘ l ∘ c ∘ π'`).

## Correspondence with the source

- The two sides. The left side is the continuation of `M(w'w, λ)φ (g)`.
  On the right, `M(w, λ)φ = ∑ i, coeff i λ · ψ i` (Theorem 2.3 (3), as in
  the Markdown of the intertwining continuation statement) and, since
  `M(w', μ)` is linear on `𝒜_Q`,
  `M(w', wλ)(M(w, λ)φ) = ∑ i, coeff i λ · M(w', wλ)(ψ i)` with
  `M(w', μ)(ψ i) = ∑ j, coeff' i j μ · χ j`.
- One family `χ`. Each `M(w', μ)(ψ i)` takes values in a finite-dimensional
  space; the union of spanning families for `i : Fin k` is a single family
  `χ`, and the coefficients of the members not needed for a given `i` are
  zero. So a common family loses no generality. The functions `χ j` and
  `χ'' j` need not be assumed automorphic; the statement does not require
  it.
- Universal form. As in the functional equation statement, the statement
  applies to all meromorphic data that agree with the convergent integrals
  on regions `Re λ ≫ 0` (resp. `Re μ ≫ 0`). Such data exist by
  Theorem 2.3 (3) (the intertwining continuation statement). For fixed
  `g`, evaluation at `g` turns BL's continuations into scalar meromorphic
  functions, and two meromorphic functions on `ℂⁿ` that agree on a nonempty
  open set agree on the intersection of their domains of holomorphy (the
  argument with local quotients `h/g` given in the Markdown of the
  functional equation statement). Hence for any admissible data both sides
  of the conclusion are the corresponding sides of BL's identity on a dense
  open subset of `D ∩ D'' ∩ w⁻¹D'`, and by continuity on all of it. This is
  explanatory and not proved here.
- Regions. The point `wλ` need not lie in a region of convergence of
  `M(w', ·)` when `λ` is regular for `P` (for example when `w` reverses the
  positive roots). This is why the right side is formed from the
  continuations, as in BL. The relation is an identity of meromorphic
  functions; no additivity of lengths `ℓ(w'w) = ℓ(w') + ℓ(w)` is assumed.
- `wλ`. `weylParameter l c π'` is BL's linear isomorphism
  `w : 𝔛_P → 𝔛_Q` (Markdown of the intertwining operator module), so
  `w⁻¹D'` is open and dense. The parameter `(w'w)λ` does not occur in the
  statement: the normalization `m_{Q''}^{-(w'w)λ}` is inside
  `hK.intertwiningOperator hK'' … (w' * w)`, built with
  `weylParameter l (c' ≫ c) π''`, and the normalization `m_{Q''}^{-w'(wλ)}`
  inside `hK'.intertwiningOperator hK'' … w'` evaluated at `wλ`. The two
  agree because `weylParameter l (c' ≫ c) π''` is the composite of
  `weylParameter l c π'` followed by `weylParameter l' c' π''`: as
  morphisms, `π'' ≫ c' ≫ l' ≫ π' ≫ c ≫ l = π'' ≫ (c' ≫ c) ≫ l` by
  `l' ≫ π' = 𝟙 M'` (not proved here).
- Parabolics. `P` and `Q` carry presentations because the regularity
  conditions on `λ` and `μ` are stated with them. `Q''` is any parabolic
  with a rational Levi factor; BL take `Q'` standard. A rational
  conjugation reduces the general case to theirs, as in the Markdown of the
  intertwining continuation statement. The presentations `r` and `r'` need
  not use the same maximal split torus or minimal parabolic.
- Where both sides are not holomorphic nothing is claimed; BL's identity of
  meromorphic functions is equivalent to equality on a dense open set.
- The compact subgroup. BL (§2.1) fix `K` in good position with respect to a
  minimal Levi `M₀`; here `K` is any maximal compact subgroup with
  `P(𝔸)K = Q(𝔸)K = Q''(𝔸)K = G(𝔸)`. The reduction to their case is the one
  described in the Markdown of the Eisenstein convergence statement. In the
  cocycle relation the factor `m_Q^{-wλ}` of `M(w, λ)φ` cancels against the
  factor `m_Q^{wλ}` of the twist inside `M(w', wλ)`.

## Scope

The existence of the continuations (BL 2.3 (3)) is stated separately in
`Langlands.Global.IntertwiningMeromorphicContinuationStatement`, the
functional equation (2.3 (4)) in
`Langlands.Global.EisensteinFunctionalEquationStatement`. The location of
singularities along root hyperplanes (2.3 (6)) is not stated here.
