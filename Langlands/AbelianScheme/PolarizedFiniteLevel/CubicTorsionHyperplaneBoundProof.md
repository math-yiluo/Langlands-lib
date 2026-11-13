# Proof of the torsion-hyperplane bound for a supplied canonical cubic embedding

Lean module: `Langlands.AbelianScheme.PolarizedFiniteLevel.CubicTorsionHyperplaneBoundProof`,
namespace `Langlands.AbelianScheme.PolarizedFiniteLevel`.

Author: Worker 3523.

`cubicTorsionHyperplaneBound` proves the published target
`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicTorsionHyperplaneBoundStatement`
at every universe `u`. It adds no premise to that statement.

The setting is a datum `a` over an algebraically closed field `K`, with `0 < g`, `0 < d`,
`0 < n` and `(n : K) ≠ 0`. Let `i` be a closed immersion of the abelian variety of `a` into
`ℙᵐ_K` over `Spec K`, with `i^* 𝒪(1) ≅ a.cubicBundle`. Suppose that no nonzero linear form
vanishes on the whole image of `i`. Then for every nonzero linear form `f`, at most
`6^g · d · g! · n^(2g-2)` sections in the `n`-torsion `Level a.abelian.toGrp _ n` have their
point on the hyperplane `f = 0`.

The geometric argument is that of Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*,
3rd edition, proof of Proposition 7.7 (printed pp.138–139). The Lean proof follows the
published Library route described below; this file only supplies the last step.

## Proof

The proof is one term:

```
cubicTorsionHyperplaneBoundReduction fieldSymmetricMultiplicationPullback
  algClosedFieldAmpleEulerInverseScaling algClosedFieldEulerInverseSymmetry
  cubicFibreCohomology
```

`cubicTorsionHyperplaneBoundReduction` (Library module `CubicTorsionHyperplaneBoundAssembly`)
proves `CubicTorsionHyperplaneBoundReductionStatement`. That proposition says that the target
follows from four published statements. Here each premise is supplied by its published
Library proof, used at the same universe `u`:

| Premise | Published statement | Published proof (module) |
| --- | --- | --- |
| `hB` | `Langlands.GroupScheme.FieldSymmetricMultiplicationPullbackStatement` | `Langlands.GroupScheme.fieldSymmetricMultiplicationPullback` (`Langlands.AbelianScheme.FieldSymmetricMultiplicationPullbackProof`) |
| `hS` | `Langlands.AbelianScheme.AlgClosedFieldAmpleEulerInverseScalingStatement` | `Langlands.AbelianScheme.algClosedFieldAmpleEulerInverseScaling` (`Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleEulerInverseScalingProof`) |
| `hI` | `Langlands.AbelianScheme.AlgClosedFieldEulerInverseSymmetryStatement` | `Langlands.AbelianScheme.algClosedFieldEulerInverseSymmetry` (`Langlands.AlgebraicGeometry.Picard.AlgClosedFieldEulerInverseSymmetryProof`) |
| `hC` | `Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreCohomologyStatement` | `Langlands.AbelianScheme.PolarizedFiniteLevel.cubicFibreCohomology` (`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreCohomologyProof`) |

What the premises say:

- `hB`: on an abelian variety over a field, if a line bundle `L` satisfies `[-1]^* L ≅ L`,
  then `[k]^* L ≅ L^(k·k)` for every `k > 0`.
- `hS`: let `H` be ample on a `g`-dimensional abelian variety over an algebraically closed
  field, `N` an inverse of `H`, `k ≥ 1`, and `Nk` an inverse of `H^k`. Then
  `χ(H^k) · χ(Nk) = k^(2g) · χ(H) · χ(N)`.
- `hI`: on such an abelian variety, if `N ⊗ M ≅ 𝒪`, then `χ(M) = (-1)^g · χ(N)`.
- `hC`: for a datum `a` over an algebraically closed field with `0 < d`,
  `Hⁱ(A, a.cubicBundle) = 0` for `i > 0` and `dim_K H⁰(A, a.cubicBundle) = 6^g · d`.

## How the reduction uses them

The reduction is proved in `CubicTorsionHyperplaneBoundAssembly`; its Markdown gives the
details. In outline, with `M = a.cubicBundle`:

1. `hS` and `hI`, applied to `M` and to `M^k`, give `χ(M^k)^2 = k^(2g) · χ(M)^2` for `k > 0`.
2. `hC` gives `χ(M) = 6^g · d`.
3. The Library theorem `lineBundleEulerPolynomial_coeff_eq_of_eulerCharacteristic_sq` then
   shows that the degree-`g` coefficient of the Euler polynomial
   `lineBundleEulerPolynomial a.abelian.X.hom M g` is `6^g · d`.
4. The Library theorem `cubicTorsionHyperplaneBound_of_symmetricPullback`
   (module `TorsionHyperplaneBezoutReduction`) takes `hB` and this coefficient and gives the
   target. It uses the published linear-system Bézout bound `linearSystemBaseLocusBezout`.

The axioms used are `propext`, `Classical.choice` and `Quot.sound`.
