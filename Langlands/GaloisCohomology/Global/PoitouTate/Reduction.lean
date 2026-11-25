import Langlands.GaloisCohomology.Global.PoitouTate.EvenDuality
import Langlands.GaloisCohomology.Global.PoitouTate.LocalDuality
import Langlands.GaloisCohomology.Global.PoitouTate.DualityStatement
import Langlands.GaloisCohomology.Global.PoitouTate.NineTermStatement
import Langlands.GaloisCohomology.Global.PoitouTate.ShaStatement
import Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.Proof
import Langlands.GaloisCohomology.Global.RealPlaces.VanishingProof

/-!
# Poitou–Tate for `G_S`: the duality with the real places and the abstract hypotheses

This file proves, for every `N`, Poitou–Tate duality for `G_S` with the real places,
`bijective_dualityMap` (the duality map `Hʳ(G_S, M) → Ĥ_cˢ(G_S, M')^∨` is bijective, `r + s = 3`,
`s ≥ 1`), and the abstract hypotheses of the Tate-modified nine-term sequence
(`TatePoitouTateHypotheses`) for `G_S`, `tatePoitouTateHypotheses` (`N ≠ 1`), from

* local Tate duality at the finite places (`localTateDualityStatement`),
* the duality without real places, `finitePlacesDualityStatement` of
  `Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.Proof` (for `N` odd it gives the duality
  directly, `bijective_dualityMap_of_odd`; for `N` even it is used for the totally complex fields
  `L ⊆ K_S`, `bijective_dualityMap_of_even`),
* the vanishing of the Tate-modified cohomology with compact support in degrees `≥ 4`,
  `tateCompactSupportVanishingStatement` of
  `Langlands.GaloisCohomology.Global.RealPlaces.VanishingProof`, of which `N` even needs
  `Ĥ_c⁴(G_S, M) = 0`.

The three statements of Poitou–Tate duality follow from `tatePoitouTateHypotheses`
(`poitouTateDualityStatement`, `poitouTateNineTermStatement`, `poitouTateShaStatement` of
`DualityProof.lean`, `NineTermProof.lean`, `ShaProof.lean` in this directory).
-/

namespace Langlands.GaloisCohomology.PoitouTate

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section Hypotheses

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (N : ℕ) [NeZero N]

/-- **Poitou–Tate duality for `G_S` with the real places**, for every `N`: for a finite smooth
`G_S`-module `M` killed by `N`, with the places above `N` in `S`, the duality map
`Hʳ(G_S, M) → Ĥ_cˢ(G_S, M')^∨` is bijective (`r + s = 3`, `s ≥ 1`). -/
theorem bijective_dualityMap
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, N • m = 0) {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
    Function.Bijective (dualityMap ι N M h) := by
  rcases Nat.even_or_odd N with he | ho
  · exact bijective_dualityMap_of_even ι S N finitePlacesDualityStatement he hS
      (fun M _ _ hM => tateCompactSupportVanishingStatement K Ω S ι M N (NeZero.ne N) hM hS 4
        le_rfl) M hM h hs
  · refine (finitePlacesDualityStatement K Ω S ι N hS (Or.inl ho)).elim fun T hT => ?_
    exact bijective_dualityMap_of_odd ι S N ho hS T hT.1 M (hT.2 M hM) h hs

/-- **The hypotheses of the abstract nine-term sequence for `G_S`** (`N ≠ 1`), with the places
above `N` in `S`. -/
theorem tatePoitouTateHypotheses
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) (hN : N ≠ 1) :
    letI : Fintype S := Fintype.ofFinite S
    TatePoitouTateHypotheses (localFamily ι S) (realFamily ι S) (dualizingModule K Ω S N)
      (trace ι S N) (fun v => invariantAt ι S N v) (fun w => realInvariantAt ι S N w.1) :=
  tatePoitouTateHypotheses_of ι S N hS hN
    fun M _ _ hM _ _ h hs => bijective_dualityMap ι S N hS M hM h hs

end Hypotheses

end

end Langlands.GaloisCohomology.PoitouTate
