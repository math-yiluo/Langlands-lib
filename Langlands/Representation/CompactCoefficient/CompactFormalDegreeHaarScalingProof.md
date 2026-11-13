# Dependence of the formal degree on the Haar measure (Renard IV.1.4, Remark 1): proof

Module `Langlands.Representation.CompactCoefficient.CompactFormalDegreeHaarScalingProof`.
Namespace `Langlands.Renard.CompactRepresentation`. Universe parameters `u` (the group) and
`v` (representation carriers).

The theorem `compactFormalDegreeHaarScaling` proves the published statement
`CompactFormalDegreeHaarScalingStatement.{u, v}` of
[CompactFormalDegreeHaarScalingStatement](CompactFormalDegreeHaarScalingStatement.md). It adds
no hypothesis. The module also proves two helper lemmas about rescaling the measure in the
integrated action. The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, registered as
`renard-2026-representations-groupes-reductifs-padiques`, IV.1.4, Remark 1 (printed p.92 /
PDF p.98): "Le scalaire `d(τ)` dépend du choix de la mesure de Haar." Renard gives no proof.
The proof below is the one-line computation `τ_{cμ}(f) = c τ_μ(f)`, recorded in the
statement's Markdown under "Why the statement is true".

## Helper lemmas

### `integratedAction_nnreal_smul_measure`

Let `G` be a topological group whose Borel sets are measurable (`OpensMeasurableSpace`), `μ`
a measure that is finite on compact sets, and `c : ℝ≥0` with `c • μ` also finite on compact
sets. Let `ρ` be a smooth complex representation on a complex vector space `V`. Then for every
`f ∈ SchwartzBruhat G` and `x ∈ V`,

`Hecke.integratedAction (c • μ) ρ hρ f x = ((c : ℝ) : ℂ) • Hecke.integratedAction μ ρ hρ f x`.

Proof. `V` has no topology, so the two vectors are compared through linear functionals:
`Module.forall_dual_apply_eq_zero_iff` reduces the equality to `L(lhs) = L(rhs)` for every
algebraic linear functional `L : V →ₗ[ℂ] ℂ`. The published
`Hecke.integratedAction_dual` turns each side into an ordinary Bochner integral:
`L(integratedAction ν ρ hρ f x) = ∫ f(g) L(ρ(g) x) dν(g)` for `ν = c • μ` and `ν = μ`.
Mathlib's `integral_smul_nnreal_measure` gives
`∫ … d(c • μ) = (c : ℝ) • ∫ … dμ`, and `Complex.real_smul` rewrites the real scalar
multiplication as multiplication by `((c : ℝ) : ℂ)`, which is `L` applied to the right-hand
side.

### `heckeAction_nnreal_smul_measure`

With `G` Borel and `μ`, `c • μ` both finite on compact sets and left invariant, for every
`f : Hecke.HeckeAlgebra (c • μ)` and `x ∈ V`,

`Hecke.heckeAction (c • μ) ρ hρ f x = ((c : ℝ) : ℂ) • Hecke.heckeAction μ ρ hρ f x`,

where on the right the same `f` is read as an element of `Hecke.HeckeAlgebra μ`. This is
possible because `Hecke.HeckeAlgebra ν` is the type synonym `SchwartzBruhat G` for every
measure `ν`. Proof: `Hecke.heckeAction_apply` unfolds both Hecke actions to
`Hecke.integratedAction` of `HeckeAlgebra.toTestFunction f`, the identity equivalence, and
the previous lemma applies.

## Main theorem `compactFormalDegreeHaarScaling`

Fix `G`, the Haar measure `μ`, the smooth representation `τ`, `c : ℝ≥0` with `[NeZero c]` and
`κ : ℂ`. The instance `(c • μ).IsHaarMeasure` provided inside the statement supplies the
finiteness on compacts and left invariance of `c • μ` that `heckeAction_nnreal_smul_measure`
needs. First, `((c : ℝ) : ℂ) ≠ 0` follows from `NeZero.ne c` by casting.

- **From `μ` to `c • μ`.** Assume the identity for `μ` and `κ`. Given `w`, `ℓ`,
  `f : HeckeAlgebra (c • μ)` with `f(g) = ℓ(τ(g⁻¹) w)` for all `g`, and `x`, rewrite the
  `c • μ` action as `c • τ_μ(f) x` by `heckeAction_nnreal_smul_measure`, apply the hypothesis
  to the same `f` read in `HeckeAlgebra μ` (the pointwise condition on `f` is unchanged),
  and get `c • ((κ ℓ(x)) • w) = (c κ ℓ(x)) • w` by `smul_smul` and `mul_assoc`.
- **From `c • μ` to `μ`.** Assume the identity for `c • μ` and `c κ`. Given `w`, `ℓ`,
  `f : HeckeAlgebra μ` with the pointwise condition, and `x`, apply the hypothesis to the same
  `f` read in `HeckeAlgebra (c • μ)`. After rewriting with `heckeAction_nnreal_smul_measure`,
  `mul_assoc` and `smul_smul`, it reads `c • τ_μ(f) x = c • ((κ ℓ(x)) • w)`. Since
  `c ≠ 0`, scalar multiplication by `c` is injective on the complex vector space `τ`
  (`smul_right_injective`), which gives the identity for `μ` and `κ`.

## Scope

The proof uses neither irreducibility, nor compactness of coefficients, nor Hausdorffness,
local compactness or total disconnectedness of `G`: the statement holds because the integrated
action is linear in the measure. Those hypotheses of the statement are simply not used.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.CompactCoefficient.CompactFormalDegreeHaarScalingStatement` | The target statement, and through its imports `Hecke.integratedAction`, `Hecke.integratedAction_dual`, `Hecke.heckeAction`, `Hecke.heckeAction_apply`, `Hecke.HeckeAlgebra`, `SchwartzBruhat`, `IsSmooth` and Mathlib's `integral_smul_nnreal_measure` |
