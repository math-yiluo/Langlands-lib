import Langlands.Correspondence.Laumon.EndRingStageMaps

/-!
# The end ring is the henselization of `k[x]` at `x = 0`

This module proves `EndTraitHenselizationStatement`: for every field `k`, the ring `endRing k` of
power series separable algebraic over `k(t)` is a henselian local ring and a discrete valuation
ring, the uniformizer `t` is irreducible in it, and every ring map `φ : k[x] → B` to a henselian
local ring with `φ⁻¹(𝔪_B) = (x)` extends along `x ↦ t` to a unique local ring map
`endRing k → B`.
-/

universe u

namespace Langlands.Henniart.Laumon

/-- **The end ring is the henselization of `k[x]` at `x = 0`** (Laumon 1987, (2.1.1); Stacks
Project, Section 10.155). -/
theorem endTraitHenselization : EndTraitHenselizationStatement.{u} := by
  intro k _
  exact ⟨henselianLocalRing_endRing k, isDiscreteValuationRing_endRing k,
    irreducible_endUniformizer k .zero, fun B _ _ φ hφ => existsUnique_endRing_hom k hφ⟩

end Langlands.Henniart.Laumon
