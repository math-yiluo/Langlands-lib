import Langlands.Galois.RestrictedRamification.OpenSubgroups
import Langlands.GaloisCohomology.Local.Dimension

/-!
# Statement: the `ℓ`-cohomological dimension of `G_S`

Let `K` be a number field, `Ω` a separable closure, `S` a set of finite places of `K` and
`G_S = Gal(K_S/K)` the Galois group of the maximal extension of `K` in `Ω` unramified outside `S` (the
infinite places may ramify).

* `CohomologicalDimensionStatement`: for every prime `ℓ` such that `S` contains the places above `ℓ`
  and `ℓ` is odd or `K` has no real place, `cd_ℓ(G_S) ≤ 2`.
* Consequences, from the statement: `Hʳ(U, M) = 0` for `r ≥ 3`, an open subgroup `U` of `G_S` and a
  smooth module `M` killed by an integer `n ≠ 0` whose prime divisors lie under `S`, with `n` odd or
  `K` totally complex (`subsingleton_cohomology_res_of_three_le`, and
  `subsingleton_cohomology_of_three_le` for `G_S` itself).
-/

namespace Langlands.GaloisCohomology

open Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

/-- **`cd_ℓ(G_S) ≤ 2`.** For every number field `K`, separable closure `Ω` of `K`, set `S` of finite
places of `K` and prime `ℓ` such that every finite place above `ℓ` lies in `S` and `ℓ` is odd or `K`
has no real place, the `ℓ`-cohomological dimension of the Galois group of the maximal extension of `K`
in `Ω` unramified outside `S` is at most `2`. -/
def CohomologicalDimensionStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (S : Set (HeightOneSpectrum (𝓞 K))) (ℓ : ℕ), ℓ.Prime →
    (∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) →
    (ℓ ≠ 2 ∨ IsTotallyComplex K) → cd ℓ (GaloisGroupUnramifiedOutside K Ω S) ≤ 2

namespace CohomologicalDimensionStatement

variable (h : CohomologicalDimensionStatement.{u}) {K Ω : Type u} [Field K] [NumberField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (S : Set (HeightOneSpectrum (𝓞 K)))
include h

/-- **Vanishing above degree two, open subgroups.** Let `n ≠ 0` be such that every finite place above
`n` lies in `S`, and `n` odd or `K` totally complex. For an open subgroup `U` of `G_S` and a smooth
module `M` of `U` killed by `n`, `Hʳ(U, M) = 0` for every `r ≥ 3`. -/
theorem subsingleton_cohomology_res_of_three_le {n : ℕ} (hn : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : Odd n ∨ IsTotallyComplex K) (U : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S))
    (M : Rep.{u} (ULift.{u} ℤ) (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S))) [IsSmoothRep M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 3 ≤ r) : Subsingleton (cohomology M r) := by
  have htors : IsAddTorsion M := fun m =>
    isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, Nat.pos_of_ne_zero hn, hM m⟩
  suffices hx : ∀ x : cohomology M r, x = 0 from ⟨fun x y => (hx x).trans (hx y).symm⟩
  intro x
  refine eq_zero_of_primaryComponent_eq_bot n hn (fun ℓ hℓ hℓn => ?_) x
    (nsmul_cohomology_eq_zero M hM r x)
  have hSℓ : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S := fun v hv =>
    hS v (by
      obtain ⟨c, hc⟩ := hℓn
      rw [hc, Nat.cast_mul]
      exact v.asIdeal.mul_mem_right _ hv)
  have hKℓ : ℓ ≠ 2 ∨ IsTotallyComplex K := hK.imp (fun ho h2 => by
    rw [h2] at hℓn
    exact (Nat.not_even_iff_odd.2 ho) (even_iff_two_dvd.2 hℓn)) id
  refine primaryComponent_cohomology_eq_bot_of_cd_lt (p := ℓ) M htors ?_
  calc cd ℓ (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
      ≤ cd ℓ (GaloisGroupUnramifiedOutside K Ω S) := cd_openSubgroup_le ℓ U
    _ ≤ 2 := h K Ω S ℓ hℓ hSℓ hKℓ
    _ < r := by exact_mod_cast (show 2 < r by omega)

/-- **Vanishing above degree two.** Let `n ≠ 0` be such that every finite place above `n` lies in
`S`, and `n` odd or `K` totally complex. For a smooth module `M` of `G_S` killed by `n`,
`Hʳ(G_S, M) = 0` for every `r ≥ 3`. -/
theorem subsingleton_cohomology_of_three_le {n : ℕ} (hn : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hK : Odd n ∨ IsTotallyComplex K)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 3 ≤ r) : Subsingleton (cohomology M r) :=
  have := h.subsingleton_cohomology_res_of_three_le S hn hS hK ⊤
    (Rep.res ((⊤ : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype M) hM hr
  (bijective_res_top M r).1.subsingleton

end CohomologicalDimensionStatement

end Langlands.GaloisCohomology
