# Dependence of the formal degree on the Haar measure (Renard IV.1.4, Remark 1): statement

Module `Langlands.Representation.CompactCoefficient.CompactFormalDegreeHaarScalingStatement`.
Namespace `Langlands.Renard.CompactRepresentation`. Universe parameters `u` (the group) and
`v` (representation carriers).
The module contains one **statement**, the `Prop`-valued definition
`CompactFormalDegreeHaarScalingStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The published
[CompactFormalDegreeStatements](CompactFormalDegreeStatements.md) says: "Remark 1, the
dependence of `d(τ)` on the Haar measure, is not stated separately". This unit states it.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read IV.1.4, printed p.92 / PDF p.98:

> On pose `d(τ) = κ(τ)⁻¹`. On appelle ce scalaire le degré formel de `τ`.
>
> Remarques. 1. Le scalaire `d(τ)` dépend du choix de la mesure de Haar.

`κ(τ)` is the scalar of the IV.1.4 Proposition (ii): `τ(ˇφ_{w,λ}) = κ(τ) α(w ⊗ λ)`, that is
`τ(ˇφ_{w,λ}) x = κ(τ) λ(x) w`, where `ˇφ_{w,λ}(g) = λ(τ(g⁻¹) w)` and `τ(f)` integrates
against the chosen Haar measure. The remark gives no formula. The precise dependence stated
here, `κ_{cμ}(τ) = c κ_μ(τ)` and so `d_{cμ}(τ) = d_μ(τ)/c`, is the content behind it. The
published Markdown of `CompactFormalDegreeStatements` explains the same scaling in prose.

## Published objects used

- `SmoothRep.{0, u, v} ℂ G` and `SmoothDual τ.representation`: smooth representations and
  the smooth functionals (Renard's `W̃`).
- `Hecke.HeckeAlgebra μ`: the Hecke algebra indexed by the measure `μ`. Its carrier is the
  space `SchwartzBruhat G` of locally constant compactly supported functions for every `μ`,
  so the same function `f` lies in `HeckeAlgebra μ` and in `HeckeAlgebra (c • μ)`.
- `Hecke.heckeAction μ ρ hρ`: the integrated action `f ↦ ∫ f(g) ρ(g) dμ(g)`.
- `Measure.IsHaarMeasure.nnreal_smul` (Mathlib): `c • μ` is a Haar measure for `c ≠ 0`.

## The statement

Let `G` be a Hausdorff, locally compact, totally disconnected topological group with a
measurable structure making it Borel, and let `μ` be a Haar measure on `G`. Let `τ` be a
smooth complex representation, `c` a nonzero nonnegative real (`c : ℝ≥0`, `[NeZero c]`) and
`κ` a complex number. The following are equivalent:

1. for all `w ∈ τ`, smooth `λ`, `f ∈ H(G)` with `f(g) = λ(τ(g⁻¹) w)` for all `g`, and all
   `x ∈ τ`: `τ_μ(f) x = (κ λ(x)) w`;
2. the same identity with the action `τ_{cμ}` for `c • μ` and the scalar `c κ`.

## Formalization choices

- **`κ` is a variable.** The published `CompactCoefficientFormalDegreeStatement` asserts that
  a nonzero `κ` with identity 1 exists. There is no named definition of `κ(τ)` or `d(τ)`.
  The statement therefore says that `κ` satisfies the defining identity for `μ` exactly when
  `c κ` satisfies it for `c • μ`. For an irreducible `τ` with compactly supported
  coefficients the scalar is unique (choose `w ≠ 0` and `λ` with `λ(w) = 1`), so this says
  `κ_{cμ}(τ) = c κ_μ(τ)` and `d_{cμ}(τ) = c⁻¹ d_μ(τ)`. Since `κ ≠ 0`, `d(τ)` changes whenever
  `c ≠ 1`, which is Renard's "dépend du choix".
- **Hypotheses.** The equivalence holds for every smooth `τ`, because `τ_{cμ}(f) = c τ_μ(f)`.
  The statement therefore omits irreducibility, compactness of coefficients, σ-compactness,
  regularity and right invariance of `μ`. They are needed for the existence of `κ`, not for
  its scaling. The statement is at least as strong as the source remark.
- **Scalars.** `c` is a nonnegative real, as in Mathlib's scaling of measures. It enters the
  complex identity as `((c : ℝ) : ℂ)`.

## Why the statement is true

For `f` in the Hecke algebra and `x ∈ τ`, `τ_{cμ}(f) x = ∫ f(g) τ(g) x d(cμ)(g) = c τ_μ(f) x`.
So identity 1 gives identity 2 after multiplication by `c`. Conversely, identity 2 gives
identity 1 after division by `c ≠ 0`.

## Remaining obligations

The proof is a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CompactCoefficient.CompactFormalDegreeStatements` | `SmoothRep`, `SmoothDual`, `Hecke.HeckeAlgebra`, `Hecke.heckeAction` (through its imports), and the formal-degree statement this remark refers to |
