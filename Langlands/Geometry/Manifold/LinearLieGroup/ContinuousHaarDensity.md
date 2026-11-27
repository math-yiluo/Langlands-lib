# Continuous kernels in coordinates of the second kind

`Langlands.Geometry.Manifold.LinearLieGroup.ContinuousHaarDensity`, namespace
`Langlands.LinearLieGroup.IsExpLieAlgebra`. Let `𝔸` be a finite-dimensional real Banach algebra,
`G` a subgroup of `𝔸ˣ` and `𝔤` a subspace of `𝔸` with `h : IsExpLieAlgebra G 𝔤`, let `b` be a basis
of `𝔤` indexed by `Fin d`, `P = h.prodExp b` the coordinates of the second kind
`P(t) = exp(t₀ b₀) ⋯ exp(t_{d-1} b_{d-1})`, and `μ` a left Haar measure on `G` (with a Borel
measurable structure).

## Statements

- `exists_continuous_density_prodExp`: there is `ε > 0` such that for every continuous
  `K : ℝᵈ → ℂ` with `tsupport K ⊆ B̄(0, ε)` (closed ball for the sup norm) there is a continuous
  compactly supported `κ : G → ℂ` with `∫ κ(y) φ(y) dμ(y) = ∫ K(t) φ(P t) dt` for every continuous
  `φ : G → ℂ`.
- `exists_continuous_density_prodExp_smul`: the same `ε`, and for each such `K` a continuous
  compactly supported `κ` with `∫ κ(y) • f(y) dμ(y) = ∫ K(t) • f(P t) dt` for every complex Banach
  space `V` (in a fixed universe) and every continuous `f : G → V`.

## Proofs

`exists_haar_density_prodExp` (module `HaarDensity`) gives `r > 0`, a smooth `ρ` positive on the
open ball `B(0, r)`, an open `W ⊆ G` and `c : G → ℝᵈ` with `P(B(0, r)) ⊆ W`, `c ∘ P = id` on the
ball, `P ∘ c = id` on `W`, `Y ↦ c(g exp Y)` smooth at `0` for `g ∈ W`, and
`∫ ψ dμ = ∫_{B(0, r)} ψ(P z) ρ(z) dz` for continuous compactly supported `ψ` with
`tsupport ψ ⊆ P(B(0, r))`. Take `ε = r/2` and `κ = 1_W · (K ∘ c) / (ρ ∘ c)`.

- `κ` vanishes outside the compact set `C = P(B̄(0, r/2))`: on `W \ C`, `c(y) ∉ B̄(0, r/2)`, so
  `K(c y) = 0`. Hence `κ` has compact support.
- `κ` is continuous: `c` is continuous on `W` (`contMDiffAt_iff_expG` with smoothness order `0`),
  so near a point of `C ⊆ W` the function `κ` is `(K ∘ c)/(ρ ∘ c)` with `ρ(c(P z₀)) = ρ(z₀) > 0`;
  off `C`, `κ` vanishes on the open complement of `C`.
- For `φ` continuous, `ψ = κ φ` is continuous with compact support in `P(B(0, r))`, so
  `∫ κ φ dμ = ∫_{B(0, r)} κ(P z) φ(P z) ρ(z) dz`, and `κ(P z) ρ(z) = K(z)` on the ball; `K` vanishes
  off `B̄(0, r/2)`, so the integral over the ball is `∫ K(t) φ(P t) dt`.
- The vector-valued form follows by applying continuous linear functionals `ℓ` (which commute with
  Bochner integrals, `ContinuousLinearMap.integral_comp_comm`) to the scalar form with
  `φ = ℓ ∘ f`; they separate points of `V` by the Hahn–Banach theorem
  (`SeparatingDual.eq_iff_forall_dual_eq`). Both integrands are continuous with compact support,
  hence integrable.

This is the construction of `exists_smooth_density_prodExp` in `HaarDensity` (where `K` is smooth
and `κ` comes out smooth for the exponential charts), for kernels that are only continuous.

## Literature

The density of Haar measure in coordinates of the second kind is used in J. Dixmier and
P. Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment différentiables*, Bull. Sci.
Math. (2) 102 (1978), §3, proof of Theorem 3.1, step (3), p. 7 of the English translation
*Factorizations of infinitely differentiable functions and smooth vectors* (paginated 1–24): the
image of a measure `f(t) dt` on a small cube under `(t₁, …, t_m) ↦ (exp t₁x₁) ⋯ (exp t_m x_m)` is a
function times the left Haar measure. The statement here takes `f` continuous instead of smooth.
