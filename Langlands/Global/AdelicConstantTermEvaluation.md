# Continuous evaluation of the adelic constant term

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), 187–234, use the normalized unipotent constant term and its pointwise growth
bound in §7.1 and the maximal-parabolic equations in §7.2. This module implements the
continuous linear evaluation needed for such scalar equations, with the Library's matrix
weight and compact rational subgroup quotient. The estimate and packaging are derived;
this is not the constant-term formula for Eisenstein series.

## The forms

`uniformGrowthToContinuousRational` is the linear forgetful map from `𝔉^R_L` to the space
of continuous rational-invariant functions. Let `U` be a subgroup functor whose adelic
points are closed and whose rational quotient `Q = U(F) \ U(𝔸)` is compact, with notation
`U(F)` for the actual principal image. The module uses the existing normalized quotient
Haar probability `dQ`. For `g ∈ G(𝔸)`, `normalizedConstantTermEvalCLM` is the continuous
complex-linear form

\[
 v\longmapsto \int_Q v(ug)\,dQ([u]).
\]

The integrand is `constantTermIntegrand`, the descended continuous function on `Q`.
`compactConstantTermLinearMap` supplies linearity and convergence for this finite Borel
measure on the compact quotient, so the integral is not relying on the zero value of a
nonintegrable Bochner integral.

For a closed immersion `j : H ⟶ G` of the affine groups, with compact rational quotient
of its image, `subgroupConstantTermEvalCLM` specializes the form to `SubgroupFunctor.range j`.
The lemma `subgroupConstantTermEvalCLM_apply` identifies its value with the existing
`AdelicGroupPoints.subgroupConstantTerm F j` on the underlying function. The descended
integrand evaluated on a quotient class equals its value at `Quotient.out` of that class,
since projecting the representative gives back the class. This compares the two exact
integrals for the same probability measure.

## Estimate and continuity

Use `S` for the exact source norm (`adelicSourceNorm`), `H` for its normalized
submultiplicative multiple (`adelicHeight`), and `D₁` for the weighted derivative along the
unit. Both norms are positive. The proof establishes the estimate

\[
 |C_U v(g)|\ \leq\ C\,\|D_1 v\|_\infty\,S(g)^R,
\]

with one `C` for all `g` and `v` (`exists_norm_normalizedConstantTerm_le` and
`exists_norm_subgroupConstantTerm_le`). The exponent is the same as the input exponent,
including when it is negative.

1. A compact subset of `U(𝔸)` meets every class of the compact `Q`. To construct one,
   choose compact neighborhoods upstairs, project their interiors by the open quotient
   map, take a finite subcover downstairs, and take the union of the selected compact
   neighborhoods. No continuous section of the quotient map is required.
2. Submultiplicativity of `H` and its fixed positive scalar ratio to `S` imply
   `S(ug) ≤ H(u) S(g)`. Using `u⁻¹` and inversion invariance of `H` in addition gives
   `S(g) ≤ H(u) S(ug)`. For `R ≥ 0` take the `R`-th power in the first bound, and for
   `R ≤ 0` use the second bound with the order reversed under the power. In either
   case `S(ug)^R ≤ H(u)^|R| S(g)^R`.
3. On the compact set of representatives, `H(u)^|R|` is bounded by some `C` by height
   continuity. The order-zero weighted supremum bound gives
   `|v(ug)| ≤ ‖D₁ v‖ S(ug)^R`. Combining the two bounds on a representative in that
   compact set bounds each value of the descended integrand. Integrating over the
   probability measure proves the displayed inequality.
4. For fixed `g`, the bound tends to zero when `v` tends to zero, by continuity of
   `weightedDerivativeCLM` for `1`. Thus the linear form is continuous at zero and
   hence everywhere.

This proves the order-zero estimate and continuous evaluations only. It does not build
cuspidal test pairings, prove bounds on derivatives of the constant term, or prove the
recurrence or uniqueness of any solution to the analytic system.
