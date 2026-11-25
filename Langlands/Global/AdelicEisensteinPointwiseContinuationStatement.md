# Pointwise meromorphic continuation of Eisenstein series

Module `Langlands.Global.AdelicEisensteinPointwiseContinuationStatement` states
`Langlands.Global.EisensteinPointwiseContinuationStatement` as a proposition
definition. It supplies no proof. It is stated for the cocycle relation of
intertwining operators (`IntertwiningCocycleStatement`). It is one of the four premises of
the reduction in `Langlands.Global.AdelicIntertwiningCocycleReduction`.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`:

- Theorem 2.3 (1), journal p.191 (PDF page 5): in the number field case the
  Eisenstein series `E(φ, λ)`, originally defined and holomorphic for
  `⟨Re λ, α^∨⟩ ≫ 0` for all `α ∈ Δ_P`, extends to a meromorphic function
  `λ ↦ E(φ, λ) ∈ 𝔉_umg(X)` on `𝔛_P`.
- §3.1, journal p.192: a function with values in a locally convex space is
  meromorphic if near every point some nonzero scalar holomorphic function
  times it is holomorphic.

Only the number field case is stated.

## Setting

The hypotheses are those of `EisensteinAbsoluteConvergenceStatement`
(module `Langlands.Global.AdelicEisensteinConvergenceStatement`) and of the
Library's `EisensteinMeromorphicContinuationStatement` (module
`Langlands.Global.AdelicEisensteinContinuationStatement`):

- `G` connected reductive over a number field `F`;
- a parabolic `p : P → G` with geometric unipotent radical `iU`, rational
  Levi `l` and split component `a`, presented by
  `r : ParabolicRootPresentation p l a`;
- `K` a maximal compact subgroup of `G(𝔸)` with `P(𝔸)K = G(𝔸)` (`hK`), a
  closed matrix embedding `rho` of `G` into `GL_N`, and the smooth-structure
  data `hsmooth`, `hcalc`.

Positivity of `N` is not assumed: it is a premise of the Fréchet spaces in
the Library's continuation statement, and this statement does not use those
spaces.

## Statement

For every finite index type `Idx` and every family `φ : Idx → (G(𝔸) → ℂ)`
of automorphic forms on `U(𝔸)M(F) \ G(𝔸)` (`IsAutomorphicFunctionOn` for
`parabolicQuotientSubgroup F p iU l` and the archimedean part
`K.comap (ofInfinite F G)` of `K`), there are

- functions `E : Idx → X^*(P) ⊗ ℂ → (G(𝔸) → ℂ)` and
- one set `D ⊆ X^*(P) ⊗ ℂ`

such that

1. for every `i` and every `g ∈ G(𝔸)`, the scalar function `λ ↦ E i λ g`
   is meromorphic with domain of holomorphy `D`
   (`IsMeromorphicInCoordinatesOn`, module
   `Langlands.Analysis.Meromorphic.LinearCoordinates`: in every linear
   coordinate system `e : ℂⁿ ≃ X^*(P) ⊗ ℂ`, `e⁻¹D` is open and dense, the
   function is holomorphic on it, and it has local holomorphic quotient
   presentations near every point of `ℂⁿ`); and
2. there is `R` such that `E i λ = hK.eisensteinSeries (φ i) λ` (as
   functions on `G(𝔸)`) for every `i` and every `λ` with
   `r.IsRegularParameter hA hT R λ`.

The region `r.IsRegularParameter hA hT R λ` is the region
"`⟨Re λ, α^∨⟩ ≫ 0` for `α ∈ Δ_P`" of the source, as explained in the
Markdown of the Eisenstein convergence statement.

## Correspondence with the source

Fix the family `φ`. By Theorem 2.3 (1), each `λ ↦ E(φ i, λ)` is a
meromorphic function on `𝔛_P = X^*(P) ⊗ ℂ` with values in `𝔉_umg(X)`, equal
to the convergent series for `Re λ` sufficiently regular. Let `E i` be this
continuation at its regular points, extended in any way elsewhere. The set of
points near which `E(φ i, ·)` is holomorphic is open and dense: near each
point it contains the complement of the zero set of a nonzero holomorphic
scalar denominator. Let `D` be the intersection over `i` of these sets, open
and dense as a finite intersection (for empty `Idx`, `D` is the whole space).

- Pointwise meromorphy. By the Corollary at the end of §8.6 (journal p.226,
  PDF page 40), on every bounded open set the continuation is meromorphic
  with values in one Fréchet space `𝔉^R_smth(X)`, on which evaluation at `g`
  is a continuous linear form. So `λ ↦ E(φ i, λ)(g)` is a scalar meromorphic
  function. It is holomorphic on `D`, and near every point the scalar
  denominator of the vector-valued function is a denominator for it. This is
  property 1 in every linear chart.
- Agreement with the series. Each `E(φ i, ·)` agrees with the series on a
  region `r.IsRegularParameter hA hT R_i`; a larger threshold gives a smaller
  region, so `R = max_i R_i` serves for all `i` (any `R` for empty `Idx`).
  This is property 2.

The statement is weaker than Theorem 2.3 (1) in two ways: it keeps only the
values at single points `g`, and it does not assert that the continuation is
automorphic at regular points. It is stronger than one application of the
Library's continuation statement in one way: it asks for one global domain of
holomorphy `D` common to all `g` and all members of the family, as the source
provides. It is not derived here from the Library's continuation statement.

## Use

The reduction of the cocycle relation (BL §8.6) applies the functional
equation `Langlands.Global.EisensteinFunctionalEquationStatement`, which is
universal in the continuations. This statement supplies the continuations
it needs, for the single form `φ`, for the forms spanning `M(w, λ)φ` and for
all forms spanning the values of the intertwining operators into `Q''`.

## Scope

The automorphy of the continuation and the Fréchet-space formulation are
stated in `Langlands.Global.EisensteinMeromorphicContinuationStatement`. The
generic injectivity (8.4) is stated in
`Langlands.Global.EisensteinGenericInjectivityStatement` and proved as
`Langlands.Global.eisensteinGenericInjectivity` in the module
`Langlands.Global.AdelicEisensteinGenericInjectivityProof`.
