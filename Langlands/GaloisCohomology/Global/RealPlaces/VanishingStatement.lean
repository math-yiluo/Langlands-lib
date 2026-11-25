import Langlands.GaloisCohomology.Global.PoitouTate.Sequence

/-!
# The vanishing of `Ĥ_cʳ(G_S, M)` in degrees `≥ 4`: statement

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`,
`G_S = Gal(K_S/K)`, `ι : PlaceEmbeddings K Ω`, and `Ĥ_cʳ(G_S, M) = compactCohomology ι M r` the
cohomology with compact support with respect to the places of `S`, modified at the real places by Tate's
cohomology (`Langlands.GaloisCohomology.PoitouTate.compactCohomology`).

`TateCompactSupportVanishingStatement`: for a finite smooth `G_S`-module `M` killed by an `n ≠ 0` such
that every finite place above `n` lies in `S`, `Ĥ_cʳ(G_S, M) = 0` for every `r ≥ 4`. It is proved in
`Langlands.GaloisCohomology.Global.RealPlaces.VanishingProof`.
-/

namespace Langlands.GaloisCohomology

open Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

/-- **Vanishing of the Tate-modified cohomology with compact support of `G_S` in degrees `≥ 4`.** For
every number field `K`, separable closure `Ω`, finite set `S` of finite places, place embeddings `ι`,
finite smooth `G_S`-module `M` killed by `n ≠ 0` such that every finite place above `n` lies in `S`, and
every `r ≥ 4`, `Ĥ_cʳ(G_S, M) = 0`. -/
def TateCompactSupportVanishingStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (ι : PlaceEmbeddings K Ω)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (n : ℕ), n ≠ 0 → (∀ m : M, n • m = 0) →
    (∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    ∀ r : ℕ, 4 ≤ r → Subsingleton (PoitouTate.compactCohomology ι M r)

end Langlands.GaloisCohomology
