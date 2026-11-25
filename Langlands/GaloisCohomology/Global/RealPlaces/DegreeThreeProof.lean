import Langlands.GaloisCohomology.Global.PoitouTate.Corollaries
import Langlands.GaloisCohomology.Global.RealPlaces.VanishingProof

/-!
# The real places in degrees `≥ 3`

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`,
`G_S = Gal(K_S/K)`, `ι : PlaceEmbeddings K Ω` and `M` a finite smooth `G_S`-module killed by `n ≠ 0`
with the places above `n` in `S`. Consider the localization `Hʳ(G_S, M) → ∏_{w real} Hʳ(K_w, M)`.

* `surjective_realLocalization_of_three_le`: it is surjective for `r ≥ 3`, and
  `injective_realLocalization_of_four_le`: injective for `r ≥ 4`: by the vanishing of `Ĥ_cʳ⁺¹(G_S, M)`
  and of `Ĥ_cʳ(G_S, M)` (`tateCompactSupportVanishingStatement`) and the exact sequence of the
  cohomology with compact support (the finite local terms vanish in degrees `≥ 3`); so it is bijective
  for `r ≥ 4` (`bijective_realLocalization_of_four_le`).
* `injective_realLocalization_three`: it is injective in degree `3`: Poitou–Tate duality gives the
  hypotheses of the abstract nine-term sequence (`PoitouTate.tatePoitouTateHypotheses`), whose
  localization in degree `3` is injective (`TatePoitouTateHypotheses.injective_ptTGlobalToLocal_three`).
* **`realLocalizationDegreeThreeStatement : RealLocalizationDegreeThreeStatement`**: hence the
  bijectivity in degree `3`, and in every degree `r ≥ 3` (`bijective_realLocalization_of_nsmul`,
  and `bijective_realLocalization` for the places above `#M` in `S`), by
  `bijective_realLocalization_of_nsmul_of_degreeThree` and `bijective_realLocalization_of_degreeThree`
  of `Langlands.GaloisCohomology.Global.RealPlaces.HighDegree`;
* `realLocalizationEquiv`: the isomorphism `Hʳ(G_S, M) ≃ ∏_{w real} Hʳ(K_w, M)` for `r ≥ 3`.

This is Tate's theorem on the real places (NSW (8.6.10) (ii), Milne I.4.10 (c)).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
open Langlands.GaloisCohomology.PoitouTate

universe u

noncomputable section

section FromVanishing

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] {n : ℕ} (hn : n ≠ 0)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
  (hM : ∀ m : M, n • m = 0)

include hn hS hM in
/-- **Surjectivity at the real places in degrees `≥ 3`.** -/
theorem surjective_realLocalization_of_three_le {r : ℕ} (hr : 3 ≤ r) :
    Function.Surjective fun (x : cohomology M r) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι M w.1 r x :=
  surjective_realLocalization_of_subsingleton ι M hr
    (tateCompactSupportVanishingStatement K Ω S ι M n hn hM hS (r + 1) (by omega))

include hn hS hM in
/-- **Injectivity at the real places in degrees `≥ 4`.** -/
theorem injective_realLocalization_of_four_le {r : ℕ} (hr : 4 ≤ r) :
    Function.Injective fun (x : cohomology M r) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι M w.1 r x :=
  injective_realLocalization_of_subsingleton ι hn M hM (by omega)
    (tateCompactSupportVanishingStatement K Ω S ι M n hn hM hS r hr)

include hn hS hM in
/-- **The real places in degrees `≥ 4`.** -/
theorem bijective_realLocalization_of_four_le {r : ℕ} (hr : 4 ≤ r) :
    Function.Bijective fun (x : cohomology M r) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι M w.1 r x :=
  ⟨injective_realLocalization_of_four_le ι S hn hS M hM hr,
    surjective_realLocalization_of_three_le ι S hn hS M hM (by omega)⟩

end FromVanishing

section Pi

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) {S : Set (HeightOneSpectrum (𝓞 K))}

/-- The localization `Hʳ(G_S, M) → ∏_{w real} Hʳ(K_w, M)` as an additive map. -/
def realLocalizationPi (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S))
    [IsSmoothRep M] (r : ℕ) :
    cohomology M r →+ ∀ w : {w : InfinitePlace K // w.IsReal}, cohomology (realLocalModule ι M w.1) r :=
  AddMonoidHom.mk' (fun x w => realLocalization ι M w.1 r x) fun x y => funext fun _ => map_add _ x y

theorem realLocalizationPi_apply (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S))
    [IsSmoothRep M] (r : ℕ) (x : cohomology M r) (w : {w : InfinitePlace K // w.IsReal}) :
    realLocalizationPi ι M r x w = realLocalization ι M w.1 r x :=
  rfl

end Pi

section DegreeThree

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]

/-- **Injectivity at the real places in degree `3`.** -/
theorem injective_realLocalization_three {n : ℕ} (hn : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hM : ∀ m : M, n • m = 0) :
    Function.Injective fun (x : cohomology M 3) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι M w.1 3 x := by
  by_cases hn1 : n = 1
  · subst hn1
    intro x x' _
    have h0 : ∀ y : cohomology M 3, y = 0 := fun y => by
      simpa using nsmul_cohomology_eq_zero M hM 3 y
    rw [h0 x, h0 x']
  have : NeZero n := ⟨hn⟩
  let _ : Fintype S := Fintype.ofFinite S
  have P := tatePoitouTateHypotheses ι S n hS hn1
  intro x x' hxx
  apply P.injective_ptTGlobalToLocal_three M hM
  rw [ptTGlobalToLocal_apply, ptTGlobalToLocal_apply]
  refine Prod.ext (funext fun v => ?_) (funext fun w => congrFun hxx w)
  have := subsingleton_cohomology_localModule_of_three_le ι S v.1 hn M hM (r := 3) le_rfl
  exact Subsingleton.elim _ _

/-- **The real places in degree three.** For a finite smooth `G_S`-module `M` killed by `n ≠ 0`,
with the places above `n` in `S`, the localization `H³(G_S, M) → ∏_{w real} H³(K_w, M)` is
bijective: injective by Poitou–Tate duality, surjective by the vanishing of `Ĥ_c⁴`. -/
theorem realLocalizationDegreeThreeStatement : RealLocalizationDegreeThreeStatement.{u} := by
  intro K _ _ Ω _ _ _ S _ ι M _ _ n hn hM hS
  exact ⟨injective_realLocalization_three ι S hn hS M hM,
    surjective_realLocalization_of_three_le ι S hn hS M hM le_rfl⟩

/-- **The real places above degree two**: for the finite smooth `G_S`-modules killed by `n ≠ 0`,
with the places above `n` in `S`, `Hʳ(G_S, M) → ∏_{w real} Hʳ(K_w, M)` is bijective for every
`r ≥ 3`. -/
theorem bijective_realLocalization_of_nsmul {n : ℕ} (hn : n ≠ 0)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {r : ℕ} (hr : 3 ≤ r) :
    ∀ (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M],
      (∀ m : M, n • m = 0) →
      Function.Bijective fun (x : cohomology M r) (w : {w : InfinitePlace K // w.IsReal}) =>
        realLocalization ι M w.1 r x :=
  bijective_realLocalization_of_nsmul_of_degreeThree S ι realLocalizationDegreeThreeStatement hn hS
    hr

/-- **Tate's theorem on the real places**: for a finite smooth `G_S`-module `M` with the places above
`#M` in `S`, `Hʳ(G_S, M) → ∏_{w real} Hʳ(K_w, M)` is bijective for every `r ≥ 3`. -/
theorem bijective_realLocalization
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {r : ℕ} (hr : 3 ≤ r) :
    Function.Bijective fun (x : cohomology M r) (w : {w : InfinitePlace K // w.IsReal}) =>
      realLocalization ι M w.1 r x :=
  bijective_realLocalization_of_degreeThree S ι realLocalizationDegreeThreeStatement M hS hr

/-- **`Hʳ(G_S, M) ≃ ∏_{w real} Hʳ(K_w, M)` for `r ≥ 3`**, for a finite smooth `G_S`-module `M`
with the places above `#M` in `S`. -/
def realLocalizationEquiv
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {r : ℕ} (hr : 3 ≤ r) :
    cohomology M r ≃+ ∀ w : {w : InfinitePlace K // w.IsReal}, cohomology (realLocalModule ι M w.1) r :=
  AddEquiv.ofBijective (realLocalizationPi ι M r) (bijective_realLocalization ι S M hS hr)

theorem realLocalizationEquiv_apply
    (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((Nat.card M : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    {r : ℕ} (hr : 3 ≤ r) (x : cohomology M r) (w : {w : InfinitePlace K // w.IsReal}) :
    realLocalizationEquiv ι S M hS hr x w = realLocalization ι M w.1 r x :=
  rfl

end DegreeThree

end

end Langlands.GaloisCohomology
