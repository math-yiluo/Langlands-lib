# Split centralizers and quotient measures

This module formalizes the centralizer and quotient calculation in Arthur–Clozel
(1989), I.5, equations (5.1)–(5.2), using the first coordinates of the twisted
conjugate as the triangular variables. It supplies the quotient measure
normalization used in the split case of Henniart–Lemaire (2011), II.2.15.

For a twisted representative `δ`, let `N₀` be the ordered product of its split
coordinates. If `b⁻¹ * N₀ * b = γ`, `splitAmbientChart` sends `x` to the pair
consisting of `b⁻¹ * x₀` and the first `l` coordinates of the twisted conjugate
of `δ` by `x`. The final coordinate is the inverse of their ordered product
times the ordinary conjugate of `γ` by `b⁻¹ * x₀`. This follows by applying
coordinate zero to the twisted norm identity. Left translation by `b⁻¹`
preserves the first Haar factor, so the ambient chart preserves the measures.

The centralizer isomorphism reads `b⁻¹ * c₀ * b`. Its inverse uses the inverse
ambient chart with the first `l` coordinates of `δ` and the prescribed first
factor. Left multiplication by `c` acts on the first factor by the centralizer
isomorphism and fixes the remaining factors. The resulting quotient chart is
continuous and open by the open quotient projections, and the equivariance
identifies its fibers. Applying coordinate zero to the association equality of
ambient measures and cancelling the centralizer inclusion proves measure
preservation of the centralizer isomorphism.

To compare the quotient measures, Lean lifts a real continuous compactly
supported quotient test to an ambient test by the positive lifting theorem.
Under the chart its average is the ordinary centralizer average of an ambient
slice. Each slice has compact support because the fixed-coordinate inclusion
is a closed embedding. Fubini, the two compatible Weil formulas and ambient
measure preservation show equality of the integrals of every such quotient
test. Regularity then gives equality of measures.
