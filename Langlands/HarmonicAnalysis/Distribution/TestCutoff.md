# Smooth cutoff multiplication between real test function spaces

Let \(\Omega\) be an open subset of a real normed space. A smooth
real scalar function with topological support contained in \(\Omega\)
defines a continuous linear map from the real tests on the whole
space to the real tests on \(\Omega\), by pointwise multiplication.

For a fixed compact input support \(K\), the product has support in
the intersection of \(K\) with the closed cutoff support. This
intersection is a compact subset of \(\Omega\). Its derivative
coordinates agree with those of Mathlib's bounded multiplication
map in the fixed-\(K\) space, so the smaller support does not affect
continuity. The universal property of the test function topology gives
the claimed map. This is an internal localization construction.
