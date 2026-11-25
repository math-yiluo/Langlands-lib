import Langlands.GaloisCohomology.Global.PoitouTate.Reduction
import Langlands.GaloisCohomology.Global.RealPlaces.VanishingProof

/-!
# The nine-term exact sequence of Poitou–Tate for `G_S`

This file proves `PoitouTateNineTermStatement`, with no hypothesis: for a finite smooth
`G_S`-module `M` killed by `N`, with the places above `N` in `S`, the sequence
`0 → H⁰(G_S, M) → P̂⁰(M) → H²(G_S, M')^∨ → H¹(G_S, M) → P¹(M) → H¹(G_S, M')^∨ → H²(G_S, M) → P²(M)
→ H⁰(G_S, M')^∨ → 0` is exact, with Tate's `Ĥ⁰` at the real places. As `PoitouTateDualityStatement`
in `DualityProof.lean`: `PoitouTate.isNineTermExact_of_hypotheses` applied to
`PoitouTate.tatePoitouTateHypotheses` for `N ≠ 1`, the zero module for `N = 1`.
-/

namespace Langlands.GaloisCohomology

universe u

/-- **The nine-term exact sequence of Poitou–Tate for `G_S`**, for every finite smooth
`G_S`-module killed by `N`, with the places above `N` in `S` and Tate's `Ĥ⁰` at the real places. -/
theorem poitouTateNineTermStatement : PoitouTateNineTermStatement.{u} := by
  intro K _ _ Ω _ _ _ S _ ι N _ hS M _ _ hM
  by_cases hN : N = 1
  · subst hN
    have : Subsingleton M := ⟨fun a b => by rw [← one_nsmul a, ← one_nsmul b, hM a, hM b]⟩
    exact PoitouTate.isNineTermExact_of_subsingleton ι M
  · exact PoitouTate.isNineTermExact_of_hypotheses ι N M
      (PoitouTate.tatePoitouTateHypotheses ι S N hS hN) hM

end Langlands.GaloisCohomology
