# Local domination of Lie group chart volume by Haar measure

`exists_chartVolume_le_smul_haar` compares the Euclidean identity chart of a finite-dimensional real Lie group with a left Haar measure `μ`. Write `e = extChartAt 𝓘(ℝ, E) 1`, `L = toEuclidean`, `x₀ = L (e 1)` and `ψ = e.symm ∘ L.symm`. It gives a closed ball about `x₀` in the coordinate domain on which the pushforward of restricted Lebesgue measure by `ψ` is at most `c • μ` for a finite scalar `c`.

The coordinate map for right translation by `(ψ z)⁻¹` is smooth on the open set where both inputs and the translated point are in the chart. At `z = x₀` it is the identity on a neighbourhood of `x₀`. Its Jacobian in the first variable is therefore bounded below by `1/2` on a small product of balls. Choose a larger closed ball `T` in the coordinate domain that contains the images of all these local translations. Choose the open group neighbourhood `W` given by the smaller open coordinate ball. It has positive Haar mass by openness and finite mass by containment in the compact image of `T`.

For a measurable group set `A`, let `C` be its inverse image in the small closed ball. For each `a ∈ W`, the coordinate change for right translation by `a⁻¹` maps `C` injectively into the points `y ∈ T` with `ψ y * a ∈ A`. Change of variables bounds the Lebesgue volume of `C` by twice the volume of this last set. Integrating over `W` and using Tonelli interchanges the `a` and `y` integrals. The integral in `a` is bounded by `μ A` by left Haar invariance. Thus the comparison constant can be taken as `2 * volume T / μ W`.

The result is an internal application of smooth group multiplication, the real Jacobian change-of-variables formula and Haar invariance.
