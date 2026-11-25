# Generic injectivity of Eisenstein series

Module `Langlands.Global.AdelicEisensteinGenericInjectivityStatement` states
`Langlands.Global.EisensteinGenericInjectivityStatement` as a proposition
definition. It supplies no proof: the statement is proved as
`Langlands.Global.eisensteinGenericInjectivity` in the module
`Langlands.Global.AdelicEisensteinGenericInjectivityProof`.
It is stated for the cocycle relation of
intertwining operators (`IntertwiningCocycleStatement`). It is one of the four premises of
the reduction in `Langlands.Global.AdelicIntertwiningCocycleReduction`.

## Source

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`:

- Remark at the end of §8.5, formula (8.4), journal p.225 (PDF page 39):
  for `Q = P` and `w = e`, the argument of §8.5 shows that on any
  finite-dimensional linear subspace of `𝒜_P`, the operator
  `φ ↦ E(φ, λ)` is injective for generic `λ ∈ 𝔛_P`.
- §8.5, journal p.225 (PDF page 39): the operator `D̃(λ)` of the argument
  is invertible wherever the resultant `R(λ)` does not vanish, where `R` is
  an analytic function on `𝔛_P` that is not identically 0, and
  `R(λ) D̃(λ)⁻¹` extends to a holomorphic function on `𝔛_P`; "generic" thus
  means outside the zero set of such a function.
- Theorem 2.3 (1), journal p.191 (PDF page 5): the meromorphic continuation
  of `E(φ, λ)`, in which (8.4) is meant.

Only the number field case is stated.

## Setting

The setting is that of
`Langlands.Global.EisensteinPointwiseContinuationStatement` (module
`Langlands.Global.AdelicEisensteinPointwiseContinuationStatement`): `G`
connected reductive over a number field `F`; a parabolic `p : P → G` with
geometric unipotent radical `iU`, rational Levi `l`, split component `a` and
presentation `r : ParabolicRootPresentation p l a`; `K` maximal compact in
`G(𝔸)` with `P(𝔸)K = G(𝔸)` (`hK`); a closed matrix embedding `rho`; the
smooth-structure data `hsmooth`, `hcalc`; and a finite family
`φ : Idx → (G(𝔸) → ℂ)` of automorphic forms on `U(𝔸)M(F) \ G(𝔸)`
(`IsAutomorphicFunctionOn` for `parabolicQuotientSubgroup F p iU l` and the
archimedean part of `K`).

## Statement

The statement is universal in the continuations. Let
`E : Idx → X^*(P) ⊗ ℂ → (G(𝔸) → ℂ)` and `D ⊆ X^*(P) ⊗ ℂ` be such that

1. for every `i` and `g`, `λ ↦ E i λ g` is meromorphic with domain of
   holomorphy `D` (`IsMeromorphicInCoordinatesOn`, module
   `Langlands.Analysis.Meromorphic.LinearCoordinates`); and
2. for every `i` there is `R` with `E i λ = hK.eisensteinSeries (φ i) λ`
   whenever `r.IsRegularParameter hA hT R λ`.

Then for every linear coordinate system `e : ℂⁿ ≃ X^*(P) ⊗ ℂ` there is an
open dense set `O ⊆ ℂⁿ` such that for every `s ∈ O` with `e s ∈ D` and every
`c : Idx → ℂ`:

if `∑ i, c i * E i (e s) g = 0` for every `g ∈ G(𝔸)`, then
`∑ i, c i * φ i g = 0` for every `g ∈ G(𝔸)`.

## Correspondence with the source

- The subspace. BL's finite-dimensional subspace is the span `V` of the
  `φ i`. The conclusion says that the linear map
  `c ↦ ∑ i, c i · E i (e s)` vanishes only on the relations `c` among the
  `φ i`; equivalently, `∑ i, c i φ i ↦ ∑ i, c i E i (e s)` is a well-defined
  injective map on `V`. This is (8.4) for the point `λ = e s`, once
  `∑ i, c i E i λ = E(∑ i, c i φ i, λ)` is known (next item).
- Universal form. The `E i` are any pointwise continuations, as in the
  Library's functional equation statement. For the true continuations of
  Theorem 2.3 (1), linearity `∑ i, c i E(φ i, λ) = E(∑ i, c i φ i, λ)` holds
  on the region of convergence and hence, by uniqueness of meromorphic
  continuation, wherever all terms are holomorphic. Any admissible `E i`
  agrees, for each `g`, with the true continuation on the intersection of
  the two domains of holomorphy: both are meromorphic on `ℂⁿ` and agree on
  the nonempty open regular region (the local quotient argument in the
  Markdown of the functional equation statement).
- The generic set. Take for `O` the intersection of `e⁻¹` of the set of
  regular points of the true continuations of the `E(φ i, ·)` (open and
  dense) with the complement of the zero set of the holomorphic function
  behind "generic" in (8.4), pulled back by `e` (open and dense). For
  `s ∈ O` with `e s ∈ D`, the given `E i (e s)` is the true value
  `E(φ i, e s)`, and (8.4) gives the implication. The set `O` may depend on
  `e`; this is harmless, because each chart is a linear isomorphism.
- Where `e s ∉ D` nothing is claimed.

The statement asks for an open dense set rather than "outside a proper
analytic subset". This is weaker than the source's notion of generic and is
the form used by the reduction of the cocycle relation, which only needs a
nonempty open set of parameters on which injectivity holds.

## Scope

The existence of continuations is stated separately in
`Langlands.Global.EisensteinPointwiseContinuationStatement` and
`Langlands.Global.EisensteinMeromorphicContinuationStatement`.
