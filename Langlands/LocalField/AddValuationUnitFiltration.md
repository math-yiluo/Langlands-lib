# Real-depth unit congruence subgroups

This internal supporting construction starts with a field `K` and an additive
valuation `ω : AddValuation K (WithTop ℝ)`. For nonnegative real depth `r`,
`addValuationUnitFiltration ω r` consists of units `x` satisfying
`ω(x) = 0` and `r ≤ ω(x - 1)`.

The product identity `(xy - 1) = (x - 1)y + (y - 1)`, the valuation inequality
for addition, and the inverse identity
`x⁻¹ - 1 = -(x - 1)x⁻¹` prove that this is a subgroup. At positive depth the
valuation-zero condition follows from the strict valuation inequality between
`1` and `x - 1`. At zero the congruence inequality follows from the
valuation-zero condition. The subgroups decrease with depth. If a unit belongs
to every depth, the valuation of `x - 1` dominates every real number, hence is
infinite, so `x = 1`. A valuation-preserving ring map preserves each subgroup.

This is a derived algebraic ingredient for the positive-depth character
congruence filtration of a torus. It does not construct a torus filtration,
identify a torus subgroup at zero, or prove any centralizer or root-group
compatibility. It uses only Mathlib's additive valuation laws.
