import Langlands.GaloisCohomology.Global.PoitouTate.Sequence

/-!
# Poitou–Tate duality for `G_S`: statement

Let `K` be a number field, `Ω` a separable closure of `K`, `S` a finite set of finite places of `K`
containing the places above `N ≥ 1`, `G_S = Gal(K_S/K)`, and `M` a finite smooth `G_S`-module killed
by `N`, with dual `M' = Hom(M, μ_N)`. Let `Ĥ_c^•(G_S, ·)` be the cohomology with compact support with
respect to the places of `S` and the real places, in which degree `0` at the real places is Tate's
`Ĥ⁰` (`PoitouTate.compactCohomology`). Poitou–Tate duality says that the cup product with the
evaluation `M ⊗ M' → μ_N` followed by the trace `Ĥ_c³(G_S, μ_N) → ℤ/N` gives perfect pairings

* `Hʳ(G_S, M) × Ĥ_cˢ(G_S, M') → ℤ/N` for `r + s = 3`, `s ≥ 1` (`PoitouTate.dualityMap`), and
* `Ĥ_cʳ(G_S, M) × Hˢ(G_S, M') → ℚ/ℤ` for `r + s = 3`, `r ≥ 1` (`PoitouTate.compactDualityMap`).

`PoitouTate.IsDuality ι N M` is the conjunction of the two bijectivities and
`PoitouTateDualityStatement` asserts it for all `K`, `Ω`, `S`, `ι`, `N` and `M`, with no condition on
the parity of `N` or on the real places. It is proved in
`Langlands.GaloisCohomology.Global.PoitouTate.DualityProof`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

namespace PoitouTate

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]

/-- Poitou–Tate duality for `M`: the duality maps `Hʳ(G_S, M) → Hom(Ĥ_cˢ(G_S, M'), ℤ/N)` (`s ≥ 1`)
and `Ĥ_cʳ(G_S, M) → Hˢ(G_S, M')^∨` (`r ≥ 1`), `r + s = 3`, are bijective. -/
structure IsDuality : Prop where
  /-- `Hʳ(G_S, M) ≅ Hom(Ĥ_cˢ(G_S, M'), ℤ/N)` for `r + s = 3`, `s ≥ 1`. -/
  bijective_dualityMap : ∀ {r s : ℕ} (h : r + s = 3), 1 ≤ s →
    Function.Bijective (dualityMap ι N M h)
  /-- `Ĥ_cʳ(G_S, M) ≅ Hˢ(G_S, M')^∨` for `r + s = 3`, `r ≥ 1`. -/
  bijective_compactDualityMap : ∀ {r s : ℕ} (h : r + s = 3), 1 ≤ r →
    Function.Bijective (compactDualityMap ι N M h)

end PoitouTate

/-- **Poitou–Tate duality** for the Galois group `G_S` of the maximal extension of a number field
unramified outside a finite set `S` of finite places containing the places above `N`, for every
finite smooth module killed by `N`, with the real places through Tate's `Ĥ⁰`. -/
def PoitouTateDualityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N],
    (∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    ∀ (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M],
      (∀ m : M, N • m = 0) → PoitouTate.IsDuality ι N M

end Langlands.GaloisCohomology
