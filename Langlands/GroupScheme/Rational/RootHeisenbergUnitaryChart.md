# Upgrade of unitary charts (statement)

Module `Langlands.GroupScheme.Rational.RootHeisenbergUnitaryChart`, declaration
`Langlands.GroupScheme.RelativeRoot.UnitaryChartUpgradeStatement`.

## Statement

Let `K` be an infinite field, `S` a commutative group scheme over `Spec K` that is a split
torus, `i : S ⟶ G` into an affine smooth group scheme `G` locally of finite type, `a ≠ 0`
a character such that no `n • a` with `n ≥ 3` is a relative root, `U = U_a` and
`U₂ = U_{2a}` affine group schemes representing the root subgroups through `j` and `j₂`,
`C` a double-root commutator pairing with affine quotient `V`, `N` a Heisenberg normal
form of `C`, and `e`, `e'` weight vector coordinates on `V` (weight `a`, dimension `d`) and
on `U₂` (weight `2a`, dimension `m`). Let `E / K` be a finite separable extension and
`L / E` a separable quadratic extension with conjugation `σ`.

Suppose `A : L →ₗ[K] K^d` is bijective, `B : L →ₗ[K] K^m` restricts to a bijection from the
trace-zero elements `{z : z + σ z = 0}` onto `K^m` (`∀ w, ∃! z, z + σ z = 0 ∧ B z = w`),
`H : L →ₗ[K] L →ₗ[K] K^m` is `K`-bilinear, and `φ` is a group homomorphism from the rational
unitary parameters `{(u, v) ∈ L² | v + σ v = u σ u}` (`SU3Root.rationalParameters E L`) to
`U(K)` with chart form

`φ (u, v) = chartPoint (A u) (B v + H u u) = incl(B v + H(u, u)) * sec(A u)`.

Then there is a homomorphism of group schemes
`ψ : R_{E/K} U_{L/E} ⟶ U` (`AffineWeil.groupScheme K E (SU3Root.unitaryParameterGroup E L)`)
whose map on rational points, read through `AffineWeil.sectionsEquiv` and
`SU3Root.unitaryRationalPointsEquiv`, is `φ`, and such that `ψ ≫ j` represents the root
subgroup `U_a`.

## Provenance

Internal intermediate statement, introduced by Worker 7 for the proof of
`Langlands.Geometry.Building.MultipliableRootGroupCoordinatesExistenceStatement` (Task 7077).
It isolates the step "a rational chart-form homomorphism is the rational-point map of a
scheme homomorphism" from the rational algebra: over an infinite field, a chart-form
rational homomorphism is given by polynomial formulas in the coordinates, and those formulas
define the scheme homomorphism. The Lean statement
is the verbatim interface agreed with Worker 7; `HeisenbergNormalForm.chartPoint` is defined
in `Langlands.GroupScheme.Rational.RootHeisenbergChartPoints`.
