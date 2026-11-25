import Langlands.GaloisCohomology.Global.PoitouTate.LocalDuality
import Langlands.GaloisCohomology.Global.Units.Brauer
import Langlands.GaloisCohomology.Global.BrauerSequence.Hasse
import Langlands.GaloisCohomology.Global.RealPlaces.HighDegree
import Langlands.GaloisCohomology.Field.Hilbert90

/-!
# `Ш²` of the roots of unity

Let `K` be a number field, `S` a finite set of finite places containing the places above a prime
`ℓ`, and `μ_ℓ = μ_ℓ(K_S)`. A class `x ∈ H²(G_S, μ_ℓ)` lies in `Ш²_S(μ_ℓ)` exactly when its image in
`H²(G_S, 𝒪_Sˣ)` vanishes (`mem_sha_iff_coeffMap_rootsOfUnityToSUnits_eq_zero`), provided `ℓ` is odd
or `K` is totally complex. In one direction, the image of `x` in the Brauer group of `K` is locally
trivial at the places of `S` (local Kummer theory: `H²(K_v, μ_ℓ) → Br(K_v)` is injective,
`injective_coeffMap_rootsOfUnityLocalHom_two` of `Langlands.GaloisCohomology.Global.PoitouTate.Trace`,
by Hilbert 90), outside `S` (it comes from the
`S`-units) and at the infinite places, hence zero (Hasse); the image in `H²(G_S, 𝒪_Sˣ)` is killed by
`ℓ` and is zero in the Brauer group, hence zero. In the other direction the localizations of `x` at
the places of `S` vanish by the same injectivity, and at the real places `H²(K_w, μ_ℓ) = 0` for `ℓ`
odd. By the Kummer sequence of the `S`-units, `Ш²_S(μ_ℓ)` is the image of the connecting map
`H¹(G_S, 𝒪_Sˣ) → H²(G_S, μ_ℓ)` (`mem_sha_iff_exists_δ`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  PoitouTate

universe u

noncomputable section

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)

attribute [local instance 2000] IsSepClosure.isGalois

section Sha

include hS in
/-- **`Ш²` of `μ_ℓ` and the `S`-units.** For a prime `N = ℓ` which is odd or with `K` totally
complex, a class of `H²(G_S, μ_ℓ)` lies in `Ш²_S(μ_ℓ)` exactly when its image in `H²(G_S, 𝒪_Sˣ)`
vanishes. -/
theorem mem_sha_iff_coeffMap_rootsOfUnityToSUnits_eq_zero (hN : N.Prime)
    (hK : N ≠ 2 ∨ IsTotallyComplex K) (x : cohomology (dualizingModule K Ω S N) 2) :
    x ∈ sha ι (dualizingModule K Ω S N) 2 ↔
      (coeffMap (rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) N) 2).hom x = 0 := by
  rw [mem_sha]
  constructor
  · rintro ⟨hfin, hreal⟩
    set y := (coeffMap (rootsOfUnityToSUnits S (maximalUnramifiedOutside K Ω S) N) 2).hom x
    have hB : brauerClass Ω S N x = 0 := by
      refine eq_zero_of_brauerLocalization_eq_zero' ι _ (fun v => ?_) (fun w => ?_)
      · by_cases hv : v ∈ S
        · rw [brauerLocalization_brauerClass, hfin v hv, map_zero]
        · exact brauerLocalization_brauerClass_eq_zero ι S N hv x
      · by_cases hw : w.IsReal
        · rw [realBrauerLocalization_brauerClass, hreal w hw, map_zero]
        · have := subsingleton_realBrauerGroup_of_isComplex w
            (InfinitePlace.not_isReal_iff_isComplex.1 hw)
          exact Subsingleton.elim _ _
    rw [brauerClass_eq_maximalSUnitsInflation] at hB
    have hy : N ^ 1 • y = 0 := by
      rw [pow_one, ← map_nsmul, nsmul_cohomology_eq_zero _ (nsmul_dualizingModule S N) 2 x,
        map_zero]
    exact eq_zero_of_maximalSUnitsInflation_eq_zero S hN hS y hy hB
  · intro hx
    have hB : brauerClass Ω S N x = 0 := by
      rw [brauerClass_eq_maximalSUnitsInflation, hx, map_zero]
    refine ⟨fun v hv => injective_coeffMap_rootsOfUnityLocalHom_two ι N hS v ?_, fun w hw => ?_⟩
    · rw [← brauerLocalization_brauerClass, hB, map_zero, map_zero]
    · rcases hK with ho | hc
      · exact eq_zero_cohomology_closureGalois_of_odd w hw _ (hN.odd_of_ne_two ho)
          (fun a => nsmul_dualizingModule S N a) (by norm_num) _
      · exact absurd hw (InfinitePlace.not_isReal_iff_isComplex.2 (hc.isComplex w))

end Sha

end

end Langlands.GaloisCohomology
