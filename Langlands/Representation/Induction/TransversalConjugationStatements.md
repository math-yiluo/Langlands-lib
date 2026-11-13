# Fixed vectors over a double-coset transversal and conjugation (Renard III.2.2, III.2.4): statements

Module `Langlands.Representation.Induction.TransversalConjugationStatements`. Namespace
`Langlands.Induction`. Universe parameters `uR` (coefficients), `uG` (the group) and `uV`
(the representation space).
The module contains two **statements**, the `Prop`-valued definitions
`InducedFixedVectorTransversalStatement` and `CompactConjugateInducedStatement`. It proves
nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The published map
[iii2-hecke-induction](../../../notes/renard/iii2-hecke-induction.md) (Task 5296) records two
gaps that these statements fill:

- the III.2.2 Lemma for an arbitrary system of representatives. The published
  `fixedEvaluationEquiv` ([FixedVectorModel](FixedVectorModel.md)) needs a *finite*
  transversal. The published `compactFixedEvaluationEquiv`
  ([CompactFixedVectorModel](CompactFixedVectorModel.md)) treats compact induction with
  Mathlib's chosen representatives `q.out`. No published result treats smooth induction
  when `P \ G / K` is infinite;
- the compact-induction half of the III.2.4 Lemma. The published
  `conjugateSmoothInducedEquiv` ([ConjugateParabolic](ConjugateParabolic.md)) treats smooth
  induction only.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read III.2.2, printed pp.71–72 / PDF pp.77–78, and III.2.4, printed p.73 /
PDF p.79:

> Lemme. Soit `K` un sous-groupe ouvert compact de `G`, et soit `Ω` un système de
> représentants des doubles classes `H\G/K`. Pour tout `g ∈ Ω`, posons `K_g = H ∩ gKg⁻¹`.
> La restriction des fonctions de `Ind_H^G E` (resp. `ind_H^G E`) à `Ω` définit un
> isomorphisme de `(Ind_H^G E)^K` (resp. `(ind_H^G E)^K`) avec l'espace `F(Ω, E)`
> (resp. `F_c(Ω, E)`) des fonctions `f : Ω → E` telles que `f(g) ∈ E^{K_g}` pour tout
> `g ∈ Ω` (resp. avec l'espace de ces fonctions ayant un support fini).

> Lemme. Supposons que `g ∈ G` normalise `H`. Alors, avec les notations de l'exemple III.2.1,
> `Ind_H^G(ρ^g, E)` est équivalente à `Ind_H^G(ρ, E)`. De même `ind_H^G(ρ^g, E)` est
> équivalente à `ind_H^G(ρ, E)`.
>
> Démonstration. […] si `f ∈ Ind_H^G(ρ, E)` (ou `ind_H^G(ρ, E)`), `A · f(g′) = f(g⁻¹g′)`.

Example III.2.1 defines `ρ^g(ghg⁻¹) = ρ(h)`.

## Published objects used

- `smoothInduced P σ` and `compactInduced P σ` on `SmoothFunctions P σ` and
  `CompactFunctions P σ`: Renard's `Ind` and `ind` (covariant functions with an open right
  stabilizer, and with compact support modulo `P`), and `eval P σ f x = f(x)`
  ([Definitions](Definitions.md)). A compactly induced function `f` has underlying smooth
  induced function `f.val`.
- `fixedVectors ρ K`, the `K`-fixed submodule.
- `conjOpenSubgroup P K ω`, the open subgroup `{p ∈ P | ω⁻¹ p ω ∈ K} = P ∩ ω K ω⁻¹` of `P`:
  Renard's `K_ω`.
- `DoubleCoset.mk P K x`, the double coset `P x K` (Mathlib).
- `Representation.Equiv`, an equivalence of representations.

## The statements

**`InducedFixedVectorTransversalStatement`** (III.2.2 Lemma). Let `P` be a subgroup of a
topological group `G`, `σ` a representation of `P` on an `R`-module `V`, `K` a compact open
subgroup of `G`, and `Ω ⊂ G` a system of representatives of `P \ G / K`: every `x ∈ G` is
`p ω k` with `ω ∈ Ω`, `p ∈ P`, `k ∈ K`, and distinct elements of `Ω` lie in distinct double
cosets. Then:

1. there is a linear isomorphism `e : (Ind_P^G V)^K ≃ ∏_{ω ∈ Ω} V^{P ∩ ωKω⁻¹}` with
   `e(f)(ω) = f(ω)`;
2. there is a linear isomorphism `e : (ind_P^G V)^K ≃ ⊕_{ω ∈ Ω} V^{P ∩ ωKω⁻¹}` (finitely
   supported functions, Lean's `Π₀`) with `e(f)(ω) = f(ω)`.

**`CompactConjugateInducedStatement`** (III.2.4 Lemma, `ind`). Let `c ∈ G` and let
`e : P ≃* Q` be conjugation by `c`, that is `e(p) = c p c⁻¹`. Let `τ` be a representation of
`Q` on the same space with `τ(e(p)) = σ(p)`. Then there is an equivalence of representations
`A : ind_P^G σ ≃ ind_Q^G τ` with `(A f)(x) = f(c⁻¹ x)`.

## Formalization choices

- **Generality.** Neither statement needs `P` closed, `G` locally compact or `σ` smooth.
  The coefficients are an arbitrary commutative ring. The source's setting (closed `H` in a
  t.d. group, smooth complex `ρ`) is a special case.
- **The transversal.** `Ω` is a subset of `G`, as in the source. "Système de représentants"
  is the covering condition together with injectivity of `ω ↦ P ω K` on `Ω`, as in the
  published `fixedEvaluationEquiv`.
- **Restriction to `Ω`.** The isomorphisms are asserted to exist with the restriction formula
  `e(f)(ω) = f(ω)`. That formula determines `e`, so the statement says that restriction to
  `Ω` is an isomorphism, as in the source.
- **Conjugation.** The published smooth counterpart `conjugateSmoothInducedEquiv` takes an
  inner conjugation `e : P ≃* Q` and the matching condition `τ ∘ e = σ`. The compact
  statement uses the same data. Renard's case is `P = Q = H` normalized by `c`, with
  `τ = ρ^c`, since `τ(c h c⁻¹) = ρ(h)` is the definition of `ρ^c`. The formula
  `(A f)(x) = f(c⁻¹ x)` is Renard's `A · f(g′) = f(g⁻¹g′)` with `g = c`.

## Why the statements are true

1. **III.2.2 Lemma.** A `K`-fixed `f ∈ Ind` satisfies `f(p ω k) = σ(p) f(ω)` (III.2.2.1), so
   `f` is determined by its values on `Ω`. If `p ∈ P ∩ ωKω⁻¹`, say `p = ω k ω⁻¹`, then
   `σ(p) f(ω) = f(ω k) = f(ω)`, so `f(ω)` lies in `V^{K_ω}`. Conversely, given values
   `v_ω ∈ V^{K_ω}`, put `f(p ω k) = σ(p) v_ω`. If `p ω k = p₁ ω k₁`, then
   `p₁⁻¹ p = ω k₁ k⁻¹ ω⁻¹ ∈ K_ω`, so the value is well defined. The function is covariant
   and right `K`-invariant, so it lies in `Ind`. For `ind`, the support of a `K`-fixed
   compactly supported function meets only finitely many double cosets, because its compact
   image in `P \ G` is covered by the open images of the `ω K`. Conversely, a function
   supported on one double coset `P ω K` has support in `P · ωK` with `ωK` compact. The
   published `compactFixedEvaluationEquiv` is the case `Ω = {q.out}`. For a general `Ω`,
   compose with the change of representatives `ω = p_ω · q.out · k_ω` and the isomorphism
   `σ(p_ω) : V^{K_{q.out}} ≃ V^{K_ω}`. The smooth case follows the argument above.
2. **III.2.4 Lemma.** For `f ∈ ind_P^G σ` put `(A f)(x) = f(c⁻¹ x)`. Then
   `(A f)(e(p) x) = f(p c⁻¹ x) = σ(p) f(c⁻¹ x) = τ(e(p)) (A f)(x)`, so `A f` is
   `τ`-covariant. It is right invariant under the same open subgroup as `f`. Its support is
   `c · supp f`, and `x ↦ c x` maps `P`-cosets to `Q`-cosets, since `c P = Q c`. So
   `A f` has compact support modulo `Q`. `A` commutes with right translation, and its
   inverse is `h ↦ (x ↦ h(c x))`. The published `conjugateSmoothInducedEquiv` is the same
   map on all of `Ind`; it remains to check that it preserves compact support.

## Remaining obligations

The proofs are a separate obligation.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Induction.CompactFixedVectorModel` | `compactInduced`, `CompactFunctions`, `smoothInduced`, `eval`, `fixedVectors`, `conjOpenSubgroup`, `DoubleCoset.mk`, `Representation.Equiv` (through its imports) |

The smooth counterpart `conjugateSmoothInducedEquiv` (module
`Langlands.Representation.Induction.ConjugateParabolic`) is cited for comparison only and is
not imported.
