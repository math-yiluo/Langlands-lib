import Langlands.GaloisCohomology.Global.PoitouTate.Reduction
import Langlands.GaloisCohomology.Global.RealPlaces.VanishingProof

/-!
# Duality of the Tate–Shafarevich groups of `G_S`

This file proves `PoitouTateShaStatement`, with no hypothesis: for a finite smooth `G_S`-module `M`
killed by `N`, with the places above `N` in `S`, `Ш¹(G_S, M)` and `Ш²(G_S, M')` are finite and the
pairing `Ш¹(G_S, M) × Ш²(G_S, M') → ℚ/ℤ` is perfect. As `PoitouTateDualityStatement` in
`DualityProof.lean`: `PoitouTate.isShaDuality_of_hypotheses` applied to
`PoitouTate.tatePoitouTateHypotheses` for `N ≠ 1`, the zero module for `N = 1`.
-/

namespace Langlands.GaloisCohomology

universe u

/-- **Duality of the Tate–Shafarevich groups of `G_S`**, for every finite smooth `G_S`-module
killed by `N`, with the places above `N` in `S`. -/
theorem poitouTateShaStatement : PoitouTateShaStatement.{u} := by
  intro K _ _ Ω _ _ _ S _ ι N _ hS M _ _ hM
  by_cases hN : N = 1
  · subst hN
    have : Subsingleton M := ⟨fun a b => by rw [← one_nsmul a, ← one_nsmul b, hM a, hM b]⟩
    exact PoitouTate.isShaDuality_of_subsingleton ι M
  · exact PoitouTate.isShaDuality_of_hypotheses ι N M
      (PoitouTate.tatePoitouTateHypotheses ι S N hS hN) hM

end Langlands.GaloisCohomology
