# A product-set volume bound

Let `G` and `H` be second-countable Hausdorff topological groups equipped
with their Borel measurable spaces and s-finite right-invariant measures
`mG` and `mH`. For a continuous group homomorphism `i` from `H` to `G` and
compact sets `D` in `G` and `E`, `V` in `H`,
`CompactProductMeasureBoundStatement` gives the inequality

\[
m_H(V)\,m_G(D\,i(E)) \leq m_G(D\,i(V^{-1}))\,m_H(V E).
\]

The measure values and products are in the extended nonnegative reals.

Integrate the indicator of `D * i(V⁻¹)` at `x * (i h)⁻¹` times the indicator
of `V * E` at `h`. For `x = d * i e` in `D * i(E)`, the product of the
indicators is one on the right translate `V * {e}`. Its measure is `mH V`.
Integrating first in `x` instead gives `mG (D * i(V⁻¹))` times the indicator
of `V * E`, by right invariance of `mG`. Tonelli's theorem gives the inequality.

This measure estimate can be applied when `i` includes an opposite unipotent
group and `E` is a conjugate of a fixed compact subset. It bounds the ambient
volume by a volume in the unipotent group, where one can apply the modulus of
the conjugation.
