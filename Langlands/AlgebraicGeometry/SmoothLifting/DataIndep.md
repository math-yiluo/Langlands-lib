# Global affine combinations do not depend on the lifting data

Namespace `Langlands.AlgebraicGeometry.SmoothLifting`. Consider two lifting
data `(f, I, x₀, s)` and `(f, I₂, x₀₂, s₂)` over the same ring `C`, both
with square-zero ideals.

- `IsGlobalLift.mem_chart`: a global lift maps the basic open of a chart
  element into the chart's affine open.
- `Chart.transfer` turns a chart of the first data into a chart of the
  second, with the same opens and element, provided some morphism is a
  global lift for both data.
- `Chart.rep_transfer` and `Chart.comb_transfer` say that chart
  representatives and chart combinations are unchanged. The combination
  identity uses `affComb_congr'`, which rewrites `affComb` along equalities
  of its ring maps, so no definitional unfolding is needed.
- `gcomb_data_indep`: if the base lift and all lifts in a family are
  global lifts for both data, their global affine combinations computed
  with either data coincide.

This is an internal lemma for the lifting of homomorphisms from groups of
multiplicative type through nilpotent thickenings. It is used to
compare kernel lifts along maps of test algebras when the target ideal is
larger than the extended ideal.
