import Langlands.GaloisCohomology.Global.PoitouTate.Sequence

/-!
# The nine-term sequence of Poitou–Tate for `G_S`: statement

For a number field `K`, a separable closure `Ω`, a finite set `S` of finite places containing the
places above `N ≥ 1`, `G_S = Gal(K_S/K)` and a finite smooth `G_S`-module `M` killed by `N` with dual
`M' = Hom(M, μ_N)`, the sequence

`0 → H⁰(G_S, M) → P̂⁰(M) → H²(G_S, M')^∨ → H¹(G_S, M) → P¹(M) → H¹(G_S, M')^∨ → H²(G_S, M) → P²(M)
  → H⁰(G_S, M')^∨ → 0`

is exact, where `Pⁿ(M) = ∏_{v ∈ S} Hⁿ(K_v, M) × ∏_{w real} Hⁿ(K_w, M)`, `P̂⁰(M)` has Tate's `Ĥ⁰` at
the real places, `X^∨ = Hom(X, ℚ/ℤ)`, and the maps are `PoitouTate.locHat`, `PoitouTate.locDualHat`,
`PoitouTate.connecting`, `PoitouTate.loc`, `PoitouTate.locDual` of
`Langlands.GaloisCohomology.Global.PoitouTate.Sequence`. `PoitouTate.IsNineTermExact ι N M` names the
nine exactness properties and `PoitouTateNineTermStatement` asserts them for all `K`, `Ω`, `S`, `ι`,
`N` and `M`. It is proved in `Langlands.GaloisCohomology.Global.PoitouTate.NineTermProof`.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

namespace PoitouTate

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]

/-- Exactness of the nine-term sequence
`0 → H⁰(G_S, M) → P̂⁰(M) → H²(G_S, M')^∨ → H¹(G_S, M) → P¹(M) → H¹(G_S, M')^∨ → H²(G_S, M) → P²(M)
→ H⁰(G_S, M')^∨ → 0`. -/
structure IsNineTermExact : Prop where
  /-- `H⁰(G_S, M) → P̂⁰(M)` is injective. -/
  injective_locHat : Function.Injective (locHat ι M)
  /-- Exactness at `P̂⁰(M)`. -/
  exact_locHat_locDualHat : Function.Exact (locHat ι M) (locDualHat ι N M)
  /-- Exactness at `H²(G_S, M')^∨`. -/
  exact_locDualHat_connecting :
    Function.Exact (locDualHat ι N M) (connecting ι N M (show 1 + 2 = 3 from rfl))
  /-- Exactness at `H¹(G_S, M)`. -/
  exact_connecting_loc_one :
    Function.Exact (connecting ι N M (show 1 + 2 = 3 from rfl)) (loc ι M 1)
  /-- Exactness at `P¹(M)`. -/
  exact_loc_locDual_one : Function.Exact (loc ι M 1) (locDual ι N M (show 1 + 1 = 2 from rfl))
  /-- Exactness at `H¹(G_S, M')^∨`. -/
  exact_locDual_connecting_one :
    Function.Exact (locDual ι N M (show 1 + 1 = 2 from rfl))
      (connecting ι N M (show 2 + 1 = 3 from rfl))
  /-- Exactness at `H²(G_S, M)`. -/
  exact_connecting_loc_two :
    Function.Exact (connecting ι N M (show 2 + 1 = 3 from rfl)) (loc ι M 2)
  /-- Exactness at `P²(M)`. -/
  exact_loc_locDual_two : Function.Exact (loc ι M 2) (locDual ι N M (show 2 + 0 = 2 from rfl))
  /-- `P²(M) → H⁰(G_S, M')^∨` is surjective. -/
  surjective_locDual_two : Function.Surjective (locDual ι N M (show 2 + 0 = 2 from rfl))

end PoitouTate

/-- **The nine-term exact sequence of Poitou–Tate** for the Galois group `G_S` of the maximal
extension of a number field unramified outside a finite set `S` of finite places containing the
places above `N`, for every finite smooth module killed by `N`, with Tate's `Ĥ⁰` at the real
places. -/
def PoitouTateNineTermStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N],
    (∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    ∀ (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M],
      (∀ m : M, N • m = 0) → PoitouTate.IsNineTermExact ι N M

end Langlands.GaloisCohomology
