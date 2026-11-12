# Compact-coefficient orthogonality and nonzero formal degree

Author: Worker 140. The theorem `Langlands.Renard.CompactRepresentation.compactCoefficientFormalDegree` proves exactly the published `CompactCoefficientFormalDegreeStatement` with its independent group and representation universes.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, IV.1.4, Proposition and definition of the formal degree, printed pp.91–92 / PDF pp.97–98. Source ID: `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## Implemented proof

The inverse coefficient `g ↦ ℓ(ρ(g⁻¹) a)` is a locally constant compactly supported function by the existing `CompactSplitting.testMap`. `formalDegreeCoefficient` bundles its linear dependence on both the smooth functional and the vector. The published equivalence between test functions and the measure-indexed Hecke algebra supplies the first assertion.

For a fixed smooth functional `ℓ` and a vector `x` in another smooth representation `σ`, the published `CompactSplitting.liftMap` is the intertwiner

`a ↦ ∫ ℓ(ρ(g⁻¹) a) σ(g) x dμ(g)`.

Between inequivalent irreducibles this map is zero, since any nonzero intertwiner would be an equivalence. This proves the second assertion for every coefficient specified pointwise in the statement.

For `σ = ρ`, admissibility follows from the published compact-coefficient admissibility theorem. Admissible Schur makes the same map scalar as a function of `a`. To identify its dependence on `ℓ` and `x`, choose `a₀ ≠ 0` and a functional `m` with `m(a₀) = 1`, and define

`D(ℓ)(x) = m(∫ ℓ(ρ(g⁻¹) a₀) ρ(g) x dμ(g))`.

The helper `coefficientDualOperator_intertwines` changes variables by right translation and uses right invariance of `μ` to show that `D` commutes with the contragredient action. Since its domain consists of smooth functionals, its image lies in the smooth dual as well. The published admissibility and irreducibility results for the smooth contragredient permit a second application of admissible Schur: `D(ℓ) = κ ℓ`. Evaluation at `a₀` identifies the scalar from the first application, giving

`ρ(ˇφ_{a,ℓ}) x = (κ ℓ(x)) a`

for one `κ` and all `a`, `ℓ`, and `x`.

To prove `κ ≠ 0`, the proof uses the positive integral argument already used in `CompactSplitting.exists_lift`, rather than Renard's completeness lemma. A nonzero vector `a₀` is detected by a smooth functional `ℓ₀`. The published invariant form built from its compact coefficient gives a smooth functional `m = ⟨·, a₀⟩` with `m(a₀) ≠ 0`. If `κ = 0`, applying `m` to the coefficient operator at `a₀` makes the integral of `F(g) conj(F(g))` vanish, where `F(g) = m(ρ(g) a₀)`. Invariance and conjugate symmetry of the form identify this integral with that coefficient action. The function `F` is continuous, compactly supported and nonzero at the identity, so the published positivity lemma for Haar measure gives a contradiction.

This replaces the source's Schur argument on a tensor-product representation by two Schur arguments and replaces its completeness argument by positivity. All integrals acting on representation carriers use the existing algebraic integral; scalar functionals compute them by ordinary complex integration. No topology or completeness is imposed on the carriers, and no hypothesis is added to the target statement.
