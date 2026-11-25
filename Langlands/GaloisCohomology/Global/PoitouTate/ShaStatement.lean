import Langlands.GaloisCohomology.Global.PoitouTate.Sequence

/-!
# The duality of Tate–Shafarevich groups for `G_S`: statement

For a number field `K`, a separable closure `Ω`, a finite set `S` of finite places containing the
places above `N ≥ 1`, `G_S = Gal(K_S/K)` and a finite smooth `G_S`-module `M` killed by `N` with dual
`M' = Hom(M, μ_N)`, the groups `Ш¹_S(M)` and `Ш²_S(M')` of classes vanishing at the places of `S` and
at the real places (`sha`) are finite, and the pairing `Ш¹_S(M) × Ш²_S(M') → ℚ/ℤ`
(`PoitouTate.shaPairing`) is perfect. `PoitouTate.IsShaDuality ι N M` collects these four facts and
`PoitouTateShaStatement` asserts them for all `K`, `Ω`, `S`, `ι`, `N` and `M`. It is proved in
`Langlands.GaloisCohomology.Global.PoitouTate.ShaProof`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

namespace PoitouTate

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]

/-- The duality of the Tate–Shafarevich groups: `Ш¹_S(M)` and `Ш²_S(M')` are finite and in perfect
duality under `shaPairing`. -/
structure IsShaDuality : Prop where
  /-- `Ш¹_S(M)` is finite. -/
  finite_sha_one : Finite (sha ι M 1)
  /-- `Ш²_S(M')` is finite. -/
  finite_sha_two : Finite (sha ι (dual N M) 2)
  /-- `Ш¹_S(M) → Ш²_S(M')^∨` is bijective. -/
  bijective_shaPairing : Function.Bijective (shaPairing ι N M)
  /-- `Ш²_S(M') → Ш¹_S(M)^∨` is bijective. -/
  bijective_shaPairing_flip : Function.Bijective (shaPairing ι N M).flip

end PoitouTate

/-- **The duality of Tate–Shafarevich groups** for the Galois group `G_S` of the maximal extension of
a number field unramified outside a finite set `S` of finite places containing the places above
`N`, for every finite smooth module killed by `N`. -/
def PoitouTateShaStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N],
    (∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    ∀ (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M],
      (∀ m : M, N • m = 0) → PoitouTate.IsShaDuality ι N M

end Langlands.GaloisCohomology
