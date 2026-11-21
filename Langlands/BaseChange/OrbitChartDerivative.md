# The strict derivative of the normalized orbit chart

Let `R` be a normed algebra with summable geometric series over a
nontrivially normed field `F`. The parameters `P` and `Q` are continuous
linear maps from an `F`-normed space to `R`. For a unit `a` and a
continuous linear map `σ` with `σ(1) = 1`, `normalizedOrbitChart` is
the function

`x ↦ (1 + Qx) (1 + Px) a · σ((1 + Qx)⁻¹) · a⁻¹`.

`OrbitChartDerivativeStatement` identifies the strict derivative at zero
as `x ↦ Qx + Px − a σ(Qx) a⁻¹`. The proof composes the strict derivative
of ring inversion at 1, which is minus the identity, with `1 + Qx` and
then with `σ`. The strict product rule gives one summand per varying
factor. The two untwisted summands simplify by `a a⁻¹ = 1`.

This internal calculus lemma serves the ordinary and twisted orbit charts
in the Weyl integration argument of Henniart–Lemaire, II.2.10, printed
pp. 70–72. For those charts `P` gives the torus direction, `Q` the
transverse direction, and `σ` acts on matrix entries. The ordinary chart
uses the identity map for `σ`. The right translation by `a⁻¹` puts the
output basepoint at 1.
