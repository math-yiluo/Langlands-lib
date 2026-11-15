# Trace and cocycle descent for semilinear group actions

Authors: Worker 47.

This module is pure group theory. It provides the abstract Galois-descent steps for the
backward direction of the unramified zero-jump descent (Task 6754). A Galois group
`Δ = Aut(K/F)` acts on a group `P` of points. The action on elements fixed by an open subgroup
factors through a finite quotient `Γ = Gal(E/F)`. The module shows two things:

1. With an element of trace one, cocycles with values in a "linear" subgroup are coboundaries.
   This is additive Hilbert 90.
2. With a dual family `a_j, c_j`, an element of a stable subgroup that is not in a smaller
   subgroup modulo the kernel of a quotient map can be replaced by a `Δ`-fixed element with the
   same property. This is a norm argument.

Everything is in namespace `Langlands.GroupScheme.TraceCocycleDescent`.

## Setting

Common variables: groups `Δ`, `Γ`, `P`, a commutative ring `L` with `[MulSemiringAction Δ L]`.
The finite level is a homomorphism `res : Δ →* Γ` with `[Fintype Γ]`, together with a function
`s : Γ → Δ` satisfying `hs : ∀ γ, res (s γ) = γ`. So `s` is a set-theoretic section; `res` is
then surjective. The action on `P` is `act : Δ →* MulAut P`. "Fixed by the kernel of `res`"
means `∀ k, res k = 1 → k • x = x`, or `act k x = x` on `P`.

Linear coordinates are modelled by `L`-modules `V`, `W` with `[DistribMulAction Δ _]` and
semilinearity `σ • (c • w) = (σ • c) • (σ • w)` (hypotheses `hV`, `hW`).

## Kernel-fixed elements

| Declaration | Content |
|---|---|
| `smul_eq_section_smul` | For a `Δ`-set `X` and `x` fixed by the kernel of `res`: `τ • x = s (res τ) • x`. |
| `smul_sum_section` | For a `Δ`-module `M` (`AddCommMonoid`, `DistribMulAction`) and `m` fixed by the kernel of `res`: `σ • ∑ γ, s γ • m = ∑ γ, s γ • m`. The trace over the section is `Δ`-fixed. |

The second lemma holds because `σ · s(γ) · m = s(res σ · γ) · m` and left multiplication by
`res σ` permutes `Γ`.

## Coboundaries from a trace-one element

`eq_of_coord_eq B e he_mul he_inj`: if `e : P → W` is additive on a subgroup `B`
(`e (x * y) = e x + e y` for `x y ∈ B`) and has trivial kernel on `B`, then `e` is injective
on `B`.

`exists_coboundary_of_trace_eq_one`. Hypotheses:

- `B : Subgroup P` is `Δ`-stable (`hB`);
- `e : P → W` is additive and injective on `B` (`he_mul`, `he_inj`) and semilinear on `B`:
  `e (act σ x) = σ • e x` (`he_act`);
- `θ : L` is fixed by the kernel of `res` (`hθfix`) and has trace `∑ γ, s γ • θ = 1` (`hθ`);
- every conjugate of `θ` preserves `e(B)`: for `x ∈ B` there is `y ∈ B` with
  `e y = (σ • θ) • e x` (`hθB`);
- `z : Δ → P` takes values in `B` (`hzB`), is a cocycle `z (σ * τ) = z σ * act σ (z τ)`
  (`hcoc`), and is trivial on the kernel of `res` (`hker`).

Conclusion: `∃ b ∈ B, ∀ σ, z σ = b * (act σ b)⁻¹`.

Proof. The cocycle and the conjugates of `θ` depend only on `res τ`: `z τ = z (s (res τ))`,
and `τ • θ = s (res τ) • θ`. Since `e(B)` is closed under finite sums, there is `b ∈ B` with
`e b = ∑_γ (s γ • θ) • e (z (s γ))`. The cocycle identity gives
`σ • e (z τ) = e (z (σ τ)) - e (z σ)`. Reindexing the sum by `γ ↦ res σ · γ` gives
`σ • e b = e b - (∑_γ s γ • θ) • e (z σ) = e b - e (z σ)`. Hence
`e (b · (act σ b)⁻¹) = e (z σ)`, and injectivity of `e` on `B` concludes.

`exists_fixed_mul_of_trace_eq_one`. Same hypotheses on `B`, `e`, `θ`. Let `w₀ : P` be fixed by
the kernel of `res`, with `w₀⁻¹ * act σ w₀ ∈ B` for all `σ`. Then
`∃ b ∈ B, ∀ σ, act σ (w₀ * b) = w₀ * b`.
Proof: `z σ = w₀⁻¹ · σ(w₀)` is a `B`-valued cocycle, trivial on the kernel of `res`. Write
`z σ = b · σ(b)⁻¹` by the previous theorem. Then `σ(w₀ b) = w₀ z(σ) σ(b) = w₀ b`.

## The norm over the section

`sectionNorm act s y : P` (definition) is the product of the elements `act (s γ) y` for
`γ : Γ`, taken in the order of the list `(Finset.univ : Finset Γ).toList`. When `P` is not
commutative, the order matters only for the value of the norm, not for the properties below.

| Declaration | Content |
|---|---|
| `sectionNorm_mem` | If `A` is `Δ`-stable and `y ∈ A`, then `sectionNorm act s y ∈ A`. |
| `toAdd_sectionNorm` | For `q : P →* Multiplicative V` with `V` an additive commutative group: `(q (sectionNorm act s y)).toAdd = ∑ γ, (q (act (s γ) y)).toAdd`. |
| `sectionNorm_fixed` | If `y` is fixed by the kernel of `res`, so is `sectionNorm act s y`. For `k` in the kernel, `k · s(γ) = s(γ) · (s(γ)⁻¹ k s(γ))` and the second factor is in the kernel. So each factor of the product is unchanged. |

## Norm descent with a dual family

`exists_fixed_not_mem_of_dual` (with `[DecidableEq Γ]`). Data and hypotheses:

- `q : P →* Multiplicative V` is semilinear: `(q (act σ x)).toAdd = σ • (q x).toAdd` (`hq`);
- `e : P → W` gives coordinates on the kernel of `q`. It is additive on `q x = q y = 1`
  (`he_mul`), has trivial kernel there (`he_inj`), and is semilinear there (`he_act`);
- `A Ap : Subgroup P` with `A` being `Δ`-stable (`hA`);
- `n : ℕ`, `a c : Fin n → L` with `∑ j, a j * s γ • c j = if γ = 1 then 1 else 0` for every
  `γ : Γ` (`hac`);
- each `a j` preserves `q(Ap)`. For `x ∈ Ap` there is `y ∈ Ap` with
  `(q y).toAdd = a j • (q x).toAdd` (`ha`);
- each `c j` preserves the images of the kernel-fixed elements of `A`. For `x ∈ A` fixed by
  the kernel of `res` there is a kernel-fixed `y ∈ A` with
  `(q y).toAdd = c j • (q x).toAdd` (`hc`);
- `θ` as above (`hθfix`, `hθ`), whose conjugates preserve `e(A ∩ ker q)`. For `x ∈ A` with
  `q x = 1` there is `y ∈ A` with `q y = 1` and `e y = (σ • θ) • e x` (`hθA`);
- `u ∈ A` is fixed by the kernel of `res`, and `q y ≠ q u` for every `y ∈ Ap`.

Conclusion: `∃ h ∈ A, (∀ σ, act σ h = h) ∧ ∀ y ∈ Ap, q y ≠ q h`.

Proof. Let `x = q(u)`; it is fixed by the kernel of `res`. Semilinearity and `hac` give
`x = ∑_j a_j • Tr(c_j • x)`, with `Tr(v) = ∑_γ s γ • v`. Since `q(Ap)` is closed under sums
and under each `a_j`, some `Tr(c_j • x)` is not in `q(Ap)`. Take a kernel-fixed `y ∈ A` with
`q y = c_j • x`. Its norm `N = sectionNorm act s y` lies in `A` (`sectionNorm_mem`).
It satisfies `q N = Tr(c_j • x)` (`toAdd_sectionNorm` and `hq`), and it is fixed by the kernel
of `res` (`sectionNorm_fixed`). By
`smul_sum_section`, `q N` is `Δ`-fixed, so `N⁻¹ σ(N) ∈ B = A ⊓ ker q`. Then
`exists_fixed_mul_of_trace_eq_one` gives `b ∈ B` with `h = N b` fixed by `Δ`. Since
`q b = 1`, `q h = q N ∉ q(Ap)`.

## Provenance

Internal. These are the standard arguments of Galois descent: additive Hilbert 90
`b = ∑ γ(θ) z_γ` for vector-group coefficients, and the norm/trace argument with a normal-basis
dual family. They are written for an abstract profinite-style group `Δ` whose action factors
through a finite quotient on the relevant elements, as for `Aut(F^ur/F)` acting on points
defined over a finite subextension.
