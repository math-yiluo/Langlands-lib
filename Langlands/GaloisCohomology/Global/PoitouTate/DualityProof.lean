import Langlands.GaloisCohomology.Global.PoitouTate.Reduction
import Langlands.GaloisCohomology.Global.RealPlaces.VanishingProof

/-!
# Poitou–Tate duality for `G_S`

This file proves `PoitouTateDualityStatement`, with no hypothesis: for a finite smooth `G_S`-module
`M` killed by `N`, with the places above `N` in `S` and `M' = Hom(M, μ_N)`, the duality maps
`Hʳ(G_S, M) → Ĥ_cˢ(G_S, M')^∨` (`s ≥ 1`) and `Ĥ_cʳ(G_S, M) → Hˢ(G_S, M')^∨` (`r ≥ 1`) are bijective
for `r + s = 3`. For `N ≠ 1` it is `PoitouTate.isDuality_of_hypotheses` applied to the abstract
hypotheses `PoitouTate.tatePoitouTateHypotheses` of
`Langlands.GaloisCohomology.Global.PoitouTate.Reduction` (which rest on the duality without real
places `PoitouTate.finitePlacesDualityStatement`, the vanishing of `Ĥ_c⁴`
`tateCompactSupportVanishingStatement` and local Tate duality
`PoitouTate.localTateDualityStatement`); for `N = 1` the module is zero.
-/

namespace Langlands.GaloisCohomology

universe u

/-- **Poitou–Tate duality for `G_S`.** For a finite smooth `G_S`-module `M` killed by `N`, with the
places above `N` in `S`: `Hʳ(G_S, M) ≅ Ĥ_cˢ(G_S, M')^∨` for `s ≥ 1` and
`Ĥ_cʳ(G_S, M) ≅ Hˢ(G_S, M')^∨` for `r ≥ 1`, where `r + s = 3`. -/
theorem poitouTateDualityStatement : PoitouTateDualityStatement.{u} := by
  intro K _ _ Ω _ _ _ S _ ι N _ hS M _ _ hM
  by_cases hN : N = 1
  · subst hN
    have : Subsingleton M := ⟨fun a b => by rw [← one_nsmul a, ← one_nsmul b, hM a, hM b]⟩
    exact PoitouTate.isDuality_of_subsingleton ι M
  · exact PoitouTate.isDuality_of_hypotheses ι N M
      (PoitouTate.tatePoitouTateHypotheses ι S N hS hN) hM

end Langlands.GaloisCohomology
