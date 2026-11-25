# Descent of filtration jumps through semilinear coordinates

## Purpose and provenance

This module is pure group theory and is internal to the proof of
`Langlands.Geometry.Building.UnramifiedZeroJumpDescentStatement`. It specializes
the published module `Langlands.GroupScheme.TraceCocycleDescent` (norm and trace arguments for
a Galois group acting through a finite quotient) to the situation of a root group with a
filtration. The two parts are:

- `U ⊇ U₂`, the root group and the subgroup of the doubled root;
- a function `ψ` (a root function) that defines the filtration.

The argument is the standard Galois-descent technique: a norm over a finite Galois level, plus
additive Hilbert 90 via a trace-one element. It is not a numbered statement of a source. It is
used in `Langlands.Geometry.Building.UnramifiedZeroJumpGaloisDescent` for
`K = F^ur`, `Δ = Aut(K/F)`, `Γ = Gal(E/F)` for a finite subextension `E`, and `R = 𝒪_E`.

Everything is in namespace `Langlands.GroupScheme.FilteredTraceDescent`.

## Setting

Groups `Δ`, `Γ`, `H` with `[Fintype Γ] [DecidableEq Γ]`, a commutative ring `L` with
`[MulSemiringAction Δ L]`, and a linear order `Λ`. As in `TraceCocycleDescent`:

- `act : Δ →* MulAut H` is the action on `H`;
- `res : Δ →* Γ` is the finite level, with a set-theoretic section `s : Γ → Δ`,
  `hs : ∀ γ, res (s γ) = γ`;
- "fixed by the kernel of `res`" means `∀ k, res k = 1 → act k x = x`.

`L^n` is `Fin n → L`. It carries the coordinatewise action of `Δ` and the scalar action of `L`.

## Auxiliary constructions

| Declaration | Content |
|---|---|
| `restrictAct act U hU` | The action `Δ →* MulAut U` on a `Δ`-stable subgroup `U ≤ H`. `coe_restrictAct` is its value. |
| `map_one_eq_zero`, `map_inv_eq_neg` | A map `q : H → V` to an additive group that is additive on a subgroup `U` sends `1` to `0` and `x⁻¹` to `-q x` for `x ∈ U`. |
| `imageAddSubgroup U B hB q hq` | For `B ≤ U` and `q` additive on `U`, the image `q '' B` as an additive subgroup of `V`; `mem_imageAddSubgroup` unfolds membership. |
| `stabilizer ι X` | For `ι : R →+* L` and an additive subgroup `X` of an `L`-module `V`, the subring `{r ∈ R ∣ ∀ x ∈ X, ι r • x ∈ X}`; `mem_stabilizer` unfolds membership. |
| `mem_stabilizer_of_smul` | Let `Δ` act semilinearly on `V` (`σ • (c • v) = (σ • c) • (σ • v)`) and let `X` be `Δ`-stable. If `ι r' = σ • ι r` and `r ∈ stabilizer ι X`, then `r' ∈ stabilizer ι X`. Proof: `ι r' • x = σ • (ι r • (σ⁻¹ • x))`. |
| `pi_smul_smul n` | The action of `Δ` on `L^n` is semilinear. |

## Main theorem with explicit dual data: `exists_fixed_not_mem_mul`

Hypotheses:

- `U U₂ : Subgroup H`, with `U` stable under `act` (`hU`);
- `q : H → L^n` is additive on `U` (`hq_mul`), and for `x ∈ U`, `q x = 0 ↔ x ∈ U₂` (`hq_ker`);
- `e : H → L^m` is additive on `U₂` (`he_mul`), with `e x = 0 → x = 1` on `U₂` (`he_inj`);
- `q (act σ x) = σ • q x` on `U` (`hq_act`) and `e (act σ x) = σ • e x` on `U₂` (`he_act`);
- `ψ : H → Λ` is ultrametric on `U`: `min (ψ g) (ψ h) ≤ ψ (g * h⁻¹)` (`hψ_min`). It is
  `Δ`-invariant on `U` (`hψ_act`), and `r < ψ 1` (`hψ1`);
- a dual family `a c : Fin N → L` with `∑ j, a j * s γ • c j = if γ = 1 then 1 else 0` for all
  `γ` (`hac`);
- each `a j` maps `q {x ∈ U ∣ r < ψ x}` into itself (`ha`), and each `c j` maps the `q`-image of
  the kernel-fixed elements of `{x ∈ U ∣ r ≤ ψ x}` into itself (`hc`);
- `θ : L` is fixed by the kernel of `res` (`hθfix`), has trace `∑ γ, s γ • θ = 1` (`hθ`), and
  every conjugate `σ • θ` maps `e {x ∈ U₂ ∣ r ≤ ψ x}` into itself (`hθA`);
- `u ∈ U` with `r ≤ ψ u`, fixed by the kernel of `res`, and
  `u ∉ {g ∣ g ∈ U ∧ r < ψ g} * U₂` (`huU`, `hur`, `hufix`, `hu`).

Conclusion: some `h ∈ U` with `r ≤ ψ h`, fixed by every `act σ`, satisfies
`h ∉ {g ∣ g ∈ U ∧ r < ψ g} * U₂`.

Proof. The ultrametric inequality gives `ψ g ≤ ψ 1`, `ψ g⁻¹ = ψ g` and
`min (ψ g) (ψ h) ≤ ψ (g * h)` on `U`. So `A = {x ∈ U ∣ r ≤ ψ x}` and
`A₊ = {x ∈ U ∣ r < ψ x}` are `Δ`-stable subgroups of `U` (here `r < ψ 1` is used). The map `q`
becomes a homomorphism `U →* Multiplicative (L^n)` whose kernel is `U₂`. The theorem is then
`TraceCocycleDescent.exists_fixed_not_mem_of_dual` applied to `P = U` with the restricted
action `restrictAct act U hU`. The hypothesis there is "`q u ∉ q(A₊)`". It follows from
`u ∉ A₊ U₂`: if `q y = q u` with `y ∈ A₊`, then `y⁻¹ u ∈ U₂` because `q (y⁻¹ u) = 0`. Its
conclusion "`q h ∉ q(A₊)`" gives back `h ∉ A₊ U₂`: if `h = y w` with `y ∈ A₊` and `w ∈ U₂`,
then `w ∈ U` and `q h = q y`.

## Main theorem with stable subrings: `exists_fixed_not_mem_mul_of_subring`

Here the dual family and the trace-one element come from a ring. Hypotheses beyond those on
`U`, `U₂`, `q`, `e`, `ψ`, `r`, `u` above:

- commutative rings `R`, `R₀` with `[Algebra R₀ R]`, an action `ρ : Γ →* (R ≃ₐ[R₀] R)` and
  `ι : R →+* L` with `ι (ρ (res σ) x) = σ • ι x` (`hι`);
- `hdual`: every `Γ`-stable subring `P` of `R` that contains `x ^ 2` for every unit `x` of `R`
  contains `a j`, `c j` (`j : Fin N`) with `∑ j, a j * ρ γ (c j) = if γ = 1 then 1 else 0`;
- `htrace`: every such `P` contains some `θ` with `∑ γ, ρ γ θ = 1`;
- `hsq_q`: for each unit `x` of `R` there is `τ ∈ H` fixed by the kernel of `res`, such that
  for `g ∈ U`: `τ g τ⁻¹ ∈ U`, `ψ (τ g τ⁻¹) = ψ g` and `q (τ g τ⁻¹) = ι (x ^ 2) • q g`;
- `hsq_e`: for each unit `x` of `R` there is `τ ∈ H` fixed by the kernel of `res`, such that
  for `g ∈ U₂` (and `g ∈ U`): `τ g τ⁻¹ ∈ U`, `τ g τ⁻¹ ∈ U₂`, `ψ (τ g τ⁻¹) = ψ g` and
  `e (τ g τ⁻¹) = ι (x ^ 2) • e g`.

The conclusion is the same as for `exists_fixed_not_mem_mul`.

Proof. Consider the three `Δ`-stable additive subgroups

- `X₊ = q {x ∈ U ∣ r < ψ x}`;
- `X_f = q {x ∈ U ∣ r ≤ ψ x, x fixed by the kernel of res}`;
- `X₂ = e {x ∈ U₂ ∣ r ≤ ψ x}`.

`X_f` is `Δ`-stable because the kernel of `res` is normal. Let
`P_q = stabilizer ι X₊ ⊓ stabilizer ι X_f` and `P_e = stabilizer ι X₂`. They are `Γ`-stable by
`mem_stabilizer_of_smul`, since `ι (ρ γ x) = s γ • ι x`. They contain all squares of units by
`hsq_q` and `hsq_e`, since conjugation by `τ` preserves the three sets. `hdual P_q` gives the
dual family and `htrace P_e` gives `θ`. Their images under `ι` satisfy the hypotheses of
`exists_fixed_not_mem_mul`: `ρ γ` is transported to `s γ` by `hι`, and `ι θ` is fixed by the
kernel of `res` because `ρ 1 = 1`. Moreover `σ • ι θ = ι (ρ (res σ) θ)` with
`ρ (res σ) θ ∈ P_e`. Two separate subrings are used because the dual family must preserve
`q`-images, while `θ` must preserve the `e`-image.
