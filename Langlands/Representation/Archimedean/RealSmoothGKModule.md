# The real (𝔤, K)-module of genuine compact-finite smooth vectors

Worker 1028, Task 7767. This internal construction is the Harish-Chandra module of a Banach representation of actual `GL_n(ℝ)`, as in Wallach, *Real Reductive Groups I*, Lemma 3.3.5 (PDF p.101, registered `wallach-1988-real-reductive-groups-i`) and Getz–Hahn Proposition 4.4.7 (PDF p.131). It uses the actual compact action of [SmoothKFiniteAdmissibility](SmoothKFiniteAdmissibility.md), the derivative restriction of [SmoothFiniteActionUnits](SmoothFiniteActionUnits.md), and the bracket law of [SmoothLieActionUnits](SmoothLieActionUnits.md).

- `Langlands.Archimedean.hasDerivAt_apply_of_mem_finiteDimensional`: let `D` be a Hausdorff topological complex vector space and `P` a finite-dimensional subspace. A curve in `P` that has a derivative in `P` (as a curve in `D`) is differentiated by every complex-linear functional `g` on `D`, continuous or not. Restricted to `P`, `g` is continuous, and slopes converge in the subspace topology.

In `Langlands.Archimedean.RealSmoothGK`, `R` is a representation of `GL_n(ℝ)` on a complex normed space, and `V = smoothKFinite ℝ n R`.

- `realDerivative` restricts the genuine derivative `dR(X)` to `V`, real linear in `X`; `coe_realDerivative` identifies its value. `realDerivative_commutator` gives `dR(XY − YX) = [dR(X), dR(Y)]` on `V` for jointly continuous `R`.
- `complexDerivative` is the complex-linear extension `z ⊗ X ↦ z • dR(X)` to `ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ`, and `lieAction` is the same map as a complex Lie algebra homomorphism, with the commutator bracket on matrices. `lieAction_one_tmul` states `π(1 ⊗ X) = dR(X)` on `V`.
- `isSmoothGKIntertwiner`: the inclusion of `V` intertwines `smoothKFiniteRepresentation` with the actual orthogonal action and `lieAction` with the genuine derivatives (`IsSmoothGKIntertwiner`).
- `isRealGKModule`: for jointly continuous `R`, `IsRealGKModule n (smoothKFiniteRepresentation ℝ n R) (lieAction n R hR)`. The four clauses:
  1. Each vector of `V` is finite for the restricted action, by injectivity of the inclusion.
  2. For any complex-linear functional `ℓ`, `k ↦ ℓ(ρ(k)v)` is continuous. Extend `ℓ` to the smooth carrier; on the finite-dimensional image of the orbit span it is continuous, and the orbit is continuous by `continuous_representation_units`.
  3. Take a curve `γ` in the orthogonal group with `γ(0) = 1` and entrywise derivative `X`. Its matrix curve has derivative `X` (`hasDerivAt_matrix_of_entries`). The published `hasDerivAt_unitsChartOrbit` gives the derivative `dR(X)v` in the genuine topology. The extension of `ℓ` restricted to the span of the orbit and `dR(X)v` is then differentiated by the lemma above.
  4. `ρ(k)π(1 ⊗ X) = π(1 ⊗ kXkᵀ)ρ(k)`, by the published covariance `operator_representation_units` and `kᵀk = 1`.

Irreducibility is proved separately in [RealSmoothKFiniteIrreducible](RealSmoothKFiniteIrreducible.md).
