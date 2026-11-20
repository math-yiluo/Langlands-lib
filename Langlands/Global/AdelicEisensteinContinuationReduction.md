# Meromorphic continuation of Eisenstein series from an analytic system

Module `Langlands.Global.AdelicEisensteinContinuationReduction` proves the
conditional theorem

```
eisensteinMeromorphicContinuation_of_analyticSystem :
  MeromorphicContinuationHolomorphicStatement.{0, 0, u, u, 0} →
  EisensteinAnalyticSystemStatement.{u} →
  EisensteinMeromorphicContinuationStatement.{u}
```

The first premise is the holomorphic part of the principle of meromorphic
continuation (Bernstein–Lapid Theorem 3.3, module
`Langlands.Analysis.Meromorphic.ContinuationPrincipleStatement`). The second
is the analytic system that characterizes Eisenstein series (BL Proposition
of §8.4 with Lemma 8.1 and the Corollary of §8.6, module
`Langlands.Global.AdelicEisensteinAnalyticSystemStatement`). The conclusion is
the meromorphic continuation of Eisenstein series, BL Theorem 2.3 (1) in the
Fréchet form of Corollary 8.6 (module
`Langlands.Global.AdelicEisensteinContinuationStatement`). Both premises are
explicit hypotheses. Nothing is asserted unconditionally.

The universe levels of the principle are those of this application. The
parameter space `ℂⁿ` and the open set of parameters are in `Type`. The
Fréchet space `𝔉^R_L` and the index type of the equations are in `Type u`. The
equations take values in `ℂ`.

## Provenance

Derived. This is the step "Theorem 3.3 applied to the system of §8.4" that
Bernstein–Lapid use to deduce Theorem 2.3 (1) and Corollary 8.6 (registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §8.4 and the end
of §8.6, journal pp.223–226). The source treats one global system on all of
`𝔛_P`. Here the system is given only on bounded open sets of coordinates, so
the module adds a gluing argument. The continuations obtained on different
sets and in different coordinates are compared by the identity theorem
(`IsMeromorphicOn.eq_of_linearCoordinates`, module
`Langlands.Analysis.Meromorphic.ContinuationUniqueness`).

## Abstract gluing (namespace `Langlands.Analysis.Meromorphic`)

Data:

- a complex vector space `X` (the parameters) and a set `Y` (the points of
  `G(𝔸)`);
- a family `Sp j` of complex topological vector spaces, indexed by `j : J`,
  with maps `toFun j : Sp j → (Y → ℂ)` to functions;
- a function `Ψ : X → (Y → ℂ)` to be continued (the Eisenstein series), a
  set `Reg ⊆ X` where `Ψ` is known (the regular parameters), and an anchor
  `A ⊆ Reg`.

Definitions:

- `IsContinuationValue Sp toFun Ψ Reg A lam g` holds when there are:
  - linear coordinates `e : ℂⁿ ≃ X`;
  - a convex open set `B ⊆ ℂⁿ` with `e⁻¹(A) ⊆ B`;
  - an index `j`, and a function `v : B → Sp j` meromorphic with domain of
    holomorphy `U` (`IsMeromorphicOn`), whose underlying function at every
    `s ∈ U` with `e s ∈ Reg` is `Ψ (e s)`;
  - a point `s ∈ U` with `e s = lam` at which the underlying function of
    `v s` is `g`.
- `gluedContinuation Sp toFun Ψ Reg A lam` is chosen by `Classical.choice`.
  It is such a `g` if one exists, and `Ψ lam` otherwise.

Results:

- `IsContinuationValue.unique`: two values `g₁`, `g₂` at the same `lam` are
  equal. The hypotheses are: `A ⊆ Reg`, `A` nonempty, `e⁻¹(A)` open in every
  coordinate system, and for each `j` and `y ∈ Y` a continuous linear form
  `ev j y` on `Sp j` evaluating the underlying function at `y`. At each `y`,
  apply `IsMeromorphicOn.eq_of_linearCoordinates` to the forms `ev j₁ y`,
  `ev j₂ y` and the function `lam ↦ Ψ lam y`. On `A` both continuations equal
  `Ψ`, because `A ⊆ Reg`.
- `gluedContinuation_eq`: under the same hypotheses, the glued continuation at
  `lam` equals any continuation value at `lam`.
- `gluedContinuation_of_mem`: at `lam ∈ Reg` the glued continuation is
  `Ψ lam`. Every continuation value there equals `Ψ lam` by its own agreement
  clause.

## Applying the principle on a convex set

- `connectedSpace_of_convex`: a nonempty convex open subset of `ℂⁿ` is a
  connected space.
- `isMeromorphicOn_zero`: on a connected open subset of `ℂⁿ`, the zero
  function is meromorphic, holomorphic everywhere. Its denominator is the
  constant `1`.
- `exists_meromorphic_unique_solution`: take a convex open `B ⊆ ℂⁿ` and an
  analytic system on `B`, locally of finite type, with values in a Hausdorff
  locally convex space. Suppose it has a unique solution at every point of a
  nonempty open `O ⊆ B`. Then it has a function `v` of unique solutions on
  the unique-solution locus `M_unq`, meromorphic with domain of holomorphy
  `M_unq`. This is `MeromorphicContinuationHolomorphicStatement` with
  `M = B`: `B` is connected, and `O` lies in the interior of `M_unq`.

## Lemmas about the setting (namespace `Langlands.Global`)

- `finite_quotient_top_restrictScalars`: an algebra modulo its unit ideal is a
  finite module.
- `zero_isAutomorphicFunctionOn`: the zero function satisfies
  `IsAutomorphicFunctionOn` for every `Γ`, `Kinf` and `rho`. The conditions
  hold as follows:
  - left invariance and right invariance under the level `L = ⊤` are trivial;
  - the function is continuous, and its slices are the zero plot-smooth
    function;
  - the span of its `Kinf`-translates is `⊥`;
  - the unit ideal of the center has finite codimension and acts by zero;
  - the growth bound holds with `C = 1` and `r = 0`.
- `isOpen_setOf_isRegularParameter`: for `G` connected reductive and linear
  coordinates `e`, the set of `t` with `e t` `R₀`-regular is open.
  - The unipotent roots are finite: they are restrictions of positive relative
    roots, and these are finite by `IsSplitTorus.finite_positiveRelativeRoots`,
    since `G` is smooth.
  - Each condition `R₀ < B(Re (e t)|_A, α)` is a strict inequality for a
    real-linear function of `t`. This function is continuous because `ℂⁿ` is
    finite-dimensional.

## The reduction

`eisensteinMeromorphicContinuation_of_analyticSystem`. Take the data of
`EisensteinMeromorphicContinuationStatement`. The analytic-system statement
gives `R₀` and the systems. The target's `R₀` is this `R₀`. There are three
cases.

1. **No linear coordinate system of `X^*(P) ⊗ ℂ` exists.** Then the second
   clause of the target is vacuous. Take `E' = E(φ, ·)`.
2. **Some coordinates `e₀` exist, and no parameter is `R₀`-regular.** Take
   `E' = 0`. The first clause is vacuous. For the second clause, take:
   - `W` the unit ball around `s₀`;
   - `R = 0` and `L = G(𝔸_f)`;
   - `f = 0`, holomorphic on all of `W` (`isMeromorphicOn_zero`).

   The values are automorphic by `zero_isAutomorphicFunctionOn`.
3. **Some `e₀ t₀` is `R₀`-regular.** The regular set is open in the
   coordinates `e₀` (`isOpen_setOf_isRegularParameter`), so it contains a ball
   `ball t₀ ε`. The anchor is `A = e₀(ball t₀ ε)`, written
   `e₀.symm ⁻¹' ball t₀ ε`. In any coordinates `e`, `e⁻¹(A)` is open and
   bounded, as the preimage of a ball under a linear isomorphism of
   finite-dimensional spaces. `E'` is `gluedContinuation`, built from:
   - the spaces `Sp (R, L) = 𝔉^R_L` (`UniformGrowthFrechetSpace`);
   - the evaluation forms `UniformGrowthFrechetSpace.evalCLM` of module
     `Langlands.Automorphic.GroupSchemeUniformGrowthFrechetInstances`;
   - `Ψ = E(φ, ·)`, `Reg` the set of `R₀`-regular parameters, and the anchor
     `A`.

   The first clause of the target is `gluedContinuation_of_mem`.

   For the second clause, let `e` and `s₀` be given. Choose `ρ` with
   `{s₀} ∪ e⁻¹(A)` inside the ball `W = ball 0 ρ`, which is bounded and
   convex. The analytic-system statement on `W` gives `R`, an open `L` and an
   analytic system. At every point of `e⁻¹(A)` the system has a unique
   solution, because these points are regular. So
   `exists_meromorphic_unique_solution` gives `v`, meromorphic with domain of
   holomorphy `D = M_unq`. At a regular `s ∈ D`, `v s` is the unique solution,
   and its underlying function is `E(φ, e s)`. So `v` is a continuation value
   at every `e s` with `s ∈ D`, and by `gluedContinuation_eq` its underlying
   function there is `E'(e s)`. The value `E'(e s)` is automorphic by the last
   clause of the analytic-system statement, because `v s` is a solution. The
   target's `f` and `D` are `v` and `D`.
