import Langlands.GaloisCohomology.Global.PoitouTate.Assembly
import Langlands.GaloisCohomology.CompactSupport.DualityMap

/-!
# Duality with compact support at the finite places

When `N` is odd or `K` has no real place, the real places play no role in Poitou–Tate duality for
modules killed by `N`, and the duality can be stated with the cohomology with compact support
`H_c^•(G_S, ·)` taken with respect to the places of `S` only (`compactSupportCohomologyRes` of the
family `localFamily ι S`).

`FinitePlacesDualityStatement` says: for every such `K`, `S`, `N`, there is a trace
`T : H_c³(G_S, μ_N) → ℤ/N` that restricts on `∏_{v ∈ S} H²(K_v, μ_N)` to the sum of the local
invariants, and for which the duality map `Hʳ(G_S, M) → Hom(H_cˢ(G_S, M'), ℤ/N)` (cup product with the
evaluation followed by `T`) is bijective for every finite module `M` killed by `N` and every
`r + s = 3`. It is the form in which the base case of the duality and the reduction to prime powers
enter the proof of `PoitouTateDualityStatement`.
-/

namespace Langlands.GaloisCohomology.PoitouTate

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

noncomputable section

section Statement

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (N : ℕ) [NeZero N]

/-- A trace `T : H_c³(G_S, μ_N) → ℤ/N` (compact support at the places of `S`) is compatible with the
local invariants when it restricts on `∏_{v ∈ S} H²(K_v, μ_N)` to their sum. -/
def IsFiniteTrace
    (T : compactSupportCohomologyRes (localFamily ι S) (dualizingModule K Ω S N) 3 →+ ZMod N) :
    Prop :=
  letI : Fintype S := Fintype.ofFinite S
  ∀ ξ : ∀ v : S, cohomology (localModule ι (dualizingModule K Ω S N) v.1) 2,
    zmodToQZ N (T ((ptLocalToCompact (localFamily ι S) (dualizingModule K Ω S N) 2).hom ξ)) =
      ∑ v : S, invariantAt ι S N v.1 (ξ v)

/-- Forgetting the real places, `Ĥ_cⁿ(G_S, A) → H_cⁿ(G_S, A)`. -/
noncomputable abbrev forgetReal (A : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S))
    [IsSmoothRep A] (n : ℕ) :
    compactCohomology ι A n ⟶ compactSupportCohomologyRes (localFamily ι S) A n :=
  tateForget _ _ A _ (fun _ => 𝟙 _) _ (fun _ => 𝟙 _) n

end Statement

/-- **Poitou–Tate duality without the real places.** For every number field `K`, separable closure
`Ω`, finite set `S` of finite places containing the places above `N`, with `N` odd or `K` totally
complex, there is a trace `T : H_c³(G_S, μ_N) → ℤ/N` compatible with the local invariants at `S` such
that `Hʳ(G_S, M) → Hom(H_cˢ(G_S, M'), ℤ/N)` is bijective for every finite module `M` killed by `N` and
every `r + s = 3`; here `H_c` is the cohomology with compact support at the places of `S`. -/
def FinitePlacesDualityStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N],
    (∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    (Odd N ∨ IsTotallyComplex K) →
    ∃ T : compactSupportCohomologyRes (localFamily ι S) (dualizingModule K Ω S N) 3 →+ ZMod N,
      IsFiniteTrace ι S N T ∧
      ∀ (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]
        [Finite M], (∀ m : M, N • m = 0) → ∀ {r s : ℕ} (h : r + s = 3),
          Function.Bijective
            (GaloisCohomology.compactDualityMap (localFamily ι S) (dualizingModule K Ω S N) h T M)

end

end Langlands.GaloisCohomology.PoitouTate
