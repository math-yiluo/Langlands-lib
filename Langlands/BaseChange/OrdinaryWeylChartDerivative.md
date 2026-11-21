# The strict derivative in ordinary Weyl coordinates

Work over a complete nontrivially normed field with the matrix operator
norm. Let `γ` be regular semisimple and write `d = Ad(γ) − 1`.
The matrix algebra splits into the kernel and image of `d`. Write `P`
for the continuous projection onto the kernel and `Q = 1 − P` for
its complement. The normalized ordinary chart is

`x ↦ (1 + Qx) (1 + Px) γ · Ring.inverse(1 + Qx) · γ⁻¹`.

`OrdinaryWeylChartDerivativeStatement` identifies its strict derivative at
zero as `P − d` and proves that the determinant is a unit equal to
`weylDiscriminant γ`. The identity twist of the general orbit-chart rule
gives `Q + P − Ad(γ) Q`. Since `d P = 0`, we have `d Q = d`, so the
derivative reduces to `P − d`. The determinant is the signed range-block
calculation of `OrdinaryWeylDifferentialStatement`.

This is the local differential calculation for ordinary Weyl integration
in Henniart–Lemaire, II.2.10, printed pp. 70–72.
