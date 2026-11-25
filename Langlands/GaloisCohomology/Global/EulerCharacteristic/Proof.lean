import Langlands.GaloisCohomology.Global.EulerCharacteristic.Statement
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.Base
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.ShaCount

/-!
# The global Euler characteristic formula: proof

Tate's global Euler characteristic formula `GlobalEulerCharacteristicStatement`, for every finite
module, and its `ℓ`-primary case. The degree-three case of Tate's theorem on the real places, which
the multiplicativity of the ratio uses (`globalEulerRatio_shortExact`), is
`realLocalizationDegreeThreeStatement` of
`Langlands.GaloisCohomology.Global.RealPlaces.DegreeThreeProof`; the base case uses the nine-term
sequence of Poitou–Tate (`poitouTateNineTermStatement`, through
`card_cohomology_two_mul_card_dual_zero`) and the count of `Ш²` (`shaTwoBaseCount`).
-/

namespace Langlands.GaloisCohomology

open Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

/-- **The `ℓ`-primary case** of the global Euler characteristic formula: for a prime `ℓ` with the
places above `ℓ` in `S` and a finite smooth `G_S`-module killed by a power of `ℓ`. -/
theorem eulerCharacteristic_eq_of_primary
    {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    {r : ℕ} (hr : ∀ m : M, (ℓ ^ r) • m = 0) :
    eulerCharacteristic M =
      (∏ w : {w : InfinitePlace K // w.IsReal},
        (Nat.card (cohomology (realLocalModule ι M w.1) 0) : ℚ)) /
        (Nat.card M : ℚ) ^ Fintype.card (InfinitePlace K) :=
  (globalEulerRatio_eq_one_iff ι M).1 (globalEulerRatio_eq_one_of_primary_of_base ι
    (globalEulerCharacteristicBase_of_shaTwoBaseCount shaTwoBaseCount) hℓ hS M hr)

/-- **Tate's global Euler characteristic formula** for every finite module. -/
theorem globalEulerCharacteristic : GlobalEulerCharacteristicStatement.{u} := by
  intro K Ω _ _ _ _ _ S _ ι M _ _ hS
  exact (globalEulerRatio_eq_one_iff ι M).1 (globalEulerRatio_eq_one_of_base ι
    (globalEulerCharacteristicBase_of_shaTwoBaseCount shaTwoBaseCount) M hS)

/-- **The order of `H¹(G_S, M)`** (from the global Euler characteristic formula): for every finite
smooth `G_S`-module `M` with the places above `#M` in `S`,
`#H¹(G_S, M) · ∏_{w real} #H⁰(K_w, M) = #H⁰(G_S, M) · #H²(G_S, M) · (#M)^{[K : ℚ]_∞}`, the exponent
being the number of infinite places of `K`. -/
theorem card_cohomology_one_mul_prod
    {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {S : Set (HeightOneSpectrum (𝓞 K))} [Finite S] (ι : PlaceEmbeddings K Ω)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    Nat.card (cohomology M 1) * ∏ w : {w : InfinitePlace K // w.IsReal},
        Nat.card (cohomology (realLocalModule ι M w.1) 0) =
      Nat.card (cohomology M 0) * Nat.card (cohomology M 2) *
        Nat.card M ^ Fintype.card (InfinitePlace K) := by
  have h := globalEulerCharacteristic K Ω S ι M hS
  rw [ProfiniteCohomology.eulerCharacteristic_eq] at h
  have hSM := mem_of_natCard_mem_of_nsmul_eq_zero hS (fun _ => card_nsmul_eq_zero')
  have := finite_cohomology_of_le_two M hSM 1 (by norm_num)
  have h1 : (Nat.card (cohomology M 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hM : (Nat.card M : ℚ) ^ Fintype.card (InfinitePlace K) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  rw [div_eq_div_iff h1 hM] at h
  exact_mod_cast (by push_cast; linarith [h] :
    ((Nat.card (cohomology M 1) * ∏ w : {w : InfinitePlace K // w.IsReal},
        Nat.card (cohomology (realLocalModule ι M w.1) 0) : ℕ) : ℚ) =
      ((Nat.card (cohomology M 0) * Nat.card (cohomology M 2) *
        Nat.card M ^ Fintype.card (InfinitePlace K) : ℕ) : ℚ))

end Langlands.GaloisCohomology
