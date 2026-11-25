import Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.Pairing
import Langlands.GaloisCohomology.Global.PoitouTate.FinitePlacesProof
import Langlands.GaloisCohomology.Global.PoitouTate.OddDuality

/-!
# Poitou–Tate duality for `G_S` from the base case

With `rootsOfUnityPairingStatement` (the perfectness of the pairing
`H_c²(G_S, μ_n) × H¹(G_S, ℤ/n) → ℤ/n`, in
`Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.Pairing`), this file gives the
hypothesis-free forms of the end theorems of the base case and of the duality at the finite places.

## Main statements

* `rootsOfUnityDualityStatement : RootsOfUnityDualityStatement` (duality for `μ_n` over the fields
  containing the `n`-th roots of unity);
* `finitePlacesDualityStatement : FinitePlacesDualityStatement` (duality with compact support at
  the finite places, `N` odd or `K` totally complex);
* `bijective_dualityMap_odd`: Poitou–Tate duality `Hʳ(G_S, M) ≅ Ĥ_cˢ(G_S, M')^∨` (`r + s = 3`,
  `s ≥ 1`) for `N` odd.

The duality for every `N` and the three statements of Poitou–Tate duality are
`bijective_dualityMap` and `tatePoitouTateHypotheses` of
`Langlands.GaloisCohomology.Global.PoitouTate.Reduction` and `poitouTateDualityStatement`,
`poitouTateNineTermStatement`, `poitouTateShaStatement` of `DualityProof`, `NineTermProof`, `ShaProof`
in this directory.

## Proofs

`rootsOfUnityDualityStatement_of_pairing` and `finitePlacesDualityStatement_of_rootsOfUnity` apply
to `rootsOfUnityPairingStatement`; for `N` odd, `bijective_dualityMap_of_odd` applies to the trace
and the duality at the finite places.

## References

See the page beside this file.
-/

namespace Langlands.GaloisCohomology.PoitouTate

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

/-- **The base case of Poitou–Tate duality**: duality for `μ_n` over the fields containing the
`n`-th roots of unity. -/
theorem rootsOfUnityDualityStatement : RootsOfUnityDualityStatement.{u} :=
  rootsOfUnityDualityStatement_of_pairing rootsOfUnityPairingStatement

/-- **Duality with compact support at the finite places**, for `N` odd or `K` totally complex. -/
theorem finitePlacesDualityStatement : FinitePlacesDualityStatement.{u} :=
  finitePlacesDualityStatement_of_rootsOfUnity rootsOfUnityDualityStatement

section Duality

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (N : ℕ) [NeZero N]

/-- **Poitou–Tate duality for odd `N`.** For `N` odd with the places above `N` in `S` and a finite
smooth `G_S`-module `M` killed by `N`, the duality map `Hʳ(G_S, M) → Ĥ_cˢ(G_S, M')^∨` is bijective
(`r + s = 3`, `s ≥ 1`). -/
theorem bijective_dualityMap_odd (hN : Odd N)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, N • m = 0) {r s : ℕ} (h : r + s = 3) (hs : 1 ≤ s) :
    Function.Bijective (dualityMap ι N M h) := by
  obtain ⟨T, hT, hdual⟩ := finitePlacesDualityStatement K Ω S ι N hS (Or.inl hN)
  exact bijective_dualityMap_of_odd ι S N hN hS T hT M (hdual M hM) h hs

end Duality

end

end Langlands.GaloisCohomology.PoitouTate
