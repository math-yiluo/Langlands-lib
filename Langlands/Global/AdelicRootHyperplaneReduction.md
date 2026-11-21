# Reduction of root-hyperplane singularities to one continuation

Module `Langlands.Global.AdelicRootHyperplaneReduction` defines the
proposition `Langlands.Global.RootHyperplaneReductionStatement` and proves it
(`Langlands.Global.rootHyperplaneReduction`):

`PositiveChamberNonemptyStatement.{u} → RootHyperplaneContinuationStatement.{u} → RootHyperplaneSingularitiesStatement.{u}`.

The target `RootHyperplaneSingularitiesStatement` (module
`Langlands.Global.AdelicRootHyperplaneStatement`) is Bernstein–Lapid,
Theorem 2.3 (6), number field case, in the local form of the Corollary in
§8.6. It asserts the root-hyperplane product form for every admissible
continuation of `M(w, λ)φ` and of `E(φ, λ)`. The premises are:

- `PositiveChamberNonemptyStatement` (module
  `Langlands.Global.AdelicPositiveChamberStatement`): if `G` is connected
  reductive, some `λ` is `0`-regular, i.e. the positive chamber is nonempty;
- `RootHyperplaneContinuationStatement` (module
  `Langlands.Global.AdelicRootHyperplaneContinuationStatement`): some
  continuation of `M(w, λ)φ`, and some continuation of `E(φ, λ)`, has the
  product form.

## Provenance

This is an internal intermediate result of the task proving
`RootHyperplaneSingularitiesStatement`. The Markdown of that statement
explains, without proof, that any admissible continuation data agree with
BL's continuation on the intersection of the domains (identity theorem), and
hence that the product form for BL's continuation gives it for the given
data. This module proves that step. The premises separate the content of BL
Theorem 2.3 (1), (3) and (6) (existence of a continuation with singularities
along root hyperplanes) from this analytic transfer. The positive chamber
premise is what makes the regular region nonempty. No assertion beyond BL is
introduced.

## Proof

### Transfer of cleared forms

All in the namespace `Langlands.Global`, for scalar functions on a complex
normed space `E`.

- `isMeromorphicOn_sum_mul_or_eq_zero`: `s ↦ ∑ i, f i s * c i`, for
  `f : Fin k → E → ℂ` meromorphic with one domain `U`, is meromorphic with
  domain `U`, or it is zero. When `k = 0` the coefficients give no information
  about `U`, so that case is separate. Otherwise `U` is open and dense by the
  meromorphy of `f i₀`, and `isMeromorphicOn_sum` with
  `IsMeromorphicOn.mul_const` applies (module
  `Langlands.Analysis.Meromorphic.IdentityTheorem`).
- `exists_eq_mul_of_eqOn_isOpen`: let each of `f₁`, `f₂` be meromorphic
  (domains `U₁`, `U₂`) or zero, and let them agree on a nonempty open `V`. If
  `h` is complex differentiable on an open `W` and `h = p · f₂` on `W ∩ U₂`
  with `p` continuous, then some function complex differentiable on `W`
  equals `p · f₁` on `W ∩ U₁`.
  - If `f₁ = 0`, take `0`.
  - If `f₂ = 0` and `f₁` is meromorphic, the identity theorem
    `IsMeromorphicOn.eq_of_eqOn_isOpen` against the zero function with domain
    `ℂⁿ` gives `f₁ = 0` on `U₁`; take `0`.
  - If both are meromorphic, `h` itself works, by
    `IsMeromorphicOn.eq_mul_of_eqOn_isOpen`.

### The regular region

For a presentation `r` with split `A` and `T`:

- `ParabolicRootPresentation.IsRegularParameter.mono`: `R'`-regular implies
  `R`-regular for `R ≤ R'`.
- `ParabolicRootPresentation.finite_unipotentRoots` (with
  `[LocallyOfFiniteType G.X.hom]`): `r.unipotentRoots` is finite. It is
  contained in the image of the positive relative roots under restriction
  along `r.data.f`, which are finite by
  `IsSplitTorus.finite_positiveRelativeRoots`.
- `exists_isOpen_isRegularParameter`: if some `λ₀` is `0`-regular, then for
  every `R` and every linear coordinate system `e : ℂⁿ ≃ X^*(P) ⊗ ℂ` there is
  a nonempty open `O ⊆ ℂⁿ` with `e s` `R`-regular for all `s ∈ O`. For each
  root `α` the map
  `L_α : s ↦ r.realRootFunctional hA hT α (Re (e s))` is real linear on the
  finite-dimensional real space `ℂⁿ`, hence continuous, and `R`-regularity of
  `e s` is `R < L_α s` for all `α ∈ r.unipotentRoots` (the definitions agree
  by `rfl`). Take `O = ⋂_{α} {s | R < L_α s}` over the finite set of roots.
  It is open. It contains `t · e⁻¹(λ₀)` for large real `t`, because
  `L_α(t · e⁻¹(λ₀)) = t · L_α(e⁻¹(λ₀))` and `L_α(e⁻¹(λ₀)) > 0` by
  `0`-regularity of `λ₀`.

### The two halves

`intertwiningRootHyperplane_of_continuation`: given the data of
`IntertwiningRootHyperplaneStatement`, with continuation data `k, ψ, coeff, D`
agreeing with `M(w, λ)φ` for `R`-regular `λ`, and coordinates `e`, `s₀`:

1. The premise gives other data `k', ψ', coeff', D'`, agreeing with
   `M(w, λ)φ` for `R'`-regular `λ`, and for `e`, `s₀` a finite set `S` of roots,
   an exponent `m` and an open `W ∋ s₀`. These `S`, `m`, `W` are used for the
   conclusion.
2. The positive chamber premise (with `IsConnectedReductive G`) gives a
   `0`-regular `λ₀`, and `exists_isOpen_isRegularParameter` a nonempty open `O`
   of `max R R'`-regular parameters in the coordinates `e`. On `O` both
   `s ↦ ∑ i, coeff i (e s) * ψ i g` and `s ↦ ∑ i, coeff' i (e s) * ψ' i g`
   equal `M(w, e s)φ(g)`.
3. For each `g`, the premise gives `h` complex differentiable on `W` with
   `h s = p(s) · ∑ i, coeff' i (e s) * ψ' i g` for `s ∈ W`, `e s ∈ D'`, where
   `p(s) = (∏ β ∈ S, rootFunctional β (e s - e s₀))^m`. The polynomial `p` is
   continuous, since each `s ↦ rootFunctional β (e s)` is complex linear on
   `ℂⁿ`. The meromorphy of the two sums in the coordinates `e` comes from
   `isMeromorphicOn_sum_mul_or_eq_zero` with `(hmero i).2 n e`. Then
   `exists_eq_mul_of_eqOn_isOpen` gives the required function for `D`.

`eisensteinRootHyperplane_of_continuation` is the same with
`s ↦ EP (e s) g` and `s ↦ EP' (e s) g`, which are meromorphic in the
coordinates `e` by hypothesis and agree with `E(φ, e s)(g)` on `O`. Here
`[LocallyOfFiniteType G.X.hom]`, which the Eisenstein statements do not carry,
comes from the smoothness field of `IsConnectedReductive G`.

`rootHyperplaneReduction` combines the two halves.

The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
