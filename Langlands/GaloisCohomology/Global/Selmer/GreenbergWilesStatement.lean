import Langlands.GaloisCohomology.Global.Selmer.SelmerGroup

/-!
# The formula of Greenberg and Wiles: statement

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`
containing the places above `N ≥ 1`, `G_S = Gal(K_S/K)`, `M` a finite smooth `G_S`-module killed by
`N` with dual `M' = Hom(M, μ_N)` (`PoitouTate.dual`), and `L` a family of local conditions for `M`
(`LocalConditions`: subgroups `L_v ⊆ H¹(K_v, M)` for `v ∈ S` and `L_w ⊆ H¹(K_w, M)` for the real
places `w`) with dual family `L^⊥` (`LocalConditions.dual`, the orthogonal complements under the
local pairings of the Poitou–Tate sequence). The formula of Greenberg and Wiles is

`#Sel_L(M) / #Sel_{L^⊥}(M') = #H⁰(G_S, M) / #H⁰(G_S, M') · ∏_{v ∈ S} #L_v / #H⁰(K_v, M)
  · ∏_{w real} #L_w / #H⁰(K_w, M) / (#M)^{r₂}`,

`r₂` the number of complex places of `K` (`InfinitePlace.nrComplexPlaces`), in which the Selmer groups
are those of `LocalConditions.selmerGroup`. `GreenbergWilesStatement` asserts it for all `K`, `Ω`,
`S`, `ι`, `N`, `M` and every family of local conditions `L`. It is proved in
`Langlands.GaloisCohomology.Global.Selmer.GreenbergWilesProof`.

The complex places contribute the factor `1/#M` each: there `H⁰(K_w, M) = M` and `H¹(K_w, M) = 0`
(Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, (8.7.9), where the product runs over all
places of `S` including the archimedean ones).
-/

namespace Langlands.GaloisCohomology

open Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

/-- **The formula of Greenberg and Wiles** for the Galois group `G_S` of the maximal extension of a
number field unramified outside a finite set `S` of finite places containing the places above `N`,
for every finite smooth module `M` killed by `N` and every family `L` of local conditions at the
places of `S` and the real places:
`#Sel_L(M) / #Sel_{L^⊥}(M') = #H⁰(G_S, M) / #H⁰(G_S, M') · ∏_{v ∈ S} #L_v / #H⁰(K_v, M)
· ∏_{w real} #L_w / #H⁰(K_w, M) / (#M)^{r₂}`. -/
def GreenbergWilesStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N],
    (∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    ∀ (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M],
      (∀ m : M, N • m = 0) → ∀ L : LocalConditions ι M,
        haveI : Fintype S := Fintype.ofFinite S
        (Nat.card L.selmerGroup : ℚ) / Nat.card (L.dual N).selmerGroup =
          (Nat.card (cohomology M 0) : ℚ) / Nat.card (cohomology (PoitouTate.dual N M) 0) *
            (∏ v : S, (Nat.card (L.finite v) : ℚ) / Nat.card (cohomology (localModule ι M v) 0)) *
            (∏ w : {w : InfinitePlace K // w.IsReal},
              (Nat.card (L.real w) : ℚ) / Nat.card (cohomology (realLocalModule ι M w.1) 0)) /
            (Nat.card M : ℚ) ^ InfinitePlace.nrComplexPlaces K

end Langlands.GaloisCohomology
