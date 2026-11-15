import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreGenericNoLargerLift
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreGenericLiftDescent
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreGenericLiftAlgebra

/-! # Proof of Murre's Lemma 2, first half of case (b)

We prove `GenericNoLargerLiftStatement`. Let `P ⊆ R'` be the prime under `y`. It is a
minimal prime, so some `h ∉ P` lies in all other minimal primes and `Spec R'[1/h]` is
irreducible. Put `A = R'[1/h]/(𝔍 N)`, `N` the nilradical of `R'[1/h]`, and `I = 𝔍A`; then
`I` is nilpotent with `I · N_A = 0`, and the generic point `t` of `Spec A` lies over `P`. As
`A_t` is local artinian, infinitesimal étaleness of `ξ` at `y` and formal unramifiedness of
`R'` over `R` show that the restriction of `ξ` lifts to no larger subscheme of `Spec A_t`.
Condition (F8) gives `g₀ ∈ A` with the same property on all `D(g) ⊆ D(g₀)`; a multiple of
`g₀` is the image of some `r₀ ∈ R'`. For a prime `Q` of `R'` with `h r₀ ∉ Q`, the ring
`R'_Q/(𝔍N)R'_Q` is a localization of `A` at a submonoid containing that multiple, so
condition (F2) passes the property to it, and Nakayama's lemma transfers it to `R'_Q`. The
open set is `V = D(h r₀)`. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace EtaleLocus

open GenericLift

theorem genericNoLargerLift : GenericNoLargerLiftStatement.{u, v} := by
  intro R _ F hF R' _ _ _ 𝔍 ξ y hy hyR
  obtain ⟨-, hZ, -, h2, -, -, -, -, -, h8⟩ := hF
  have : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  -- The prime `P` under `y`.
  obtain ⟨P, hPy⟩ : ∃ P : Ideal R', P = y.asIdeal.comap (Ideal.Quotient.mk 𝔍) := ⟨_, rfl⟩
  have hPprime : P.IsPrime := hPy ▸ Ideal.comap_isPrime _ _
  have h𝔍P : 𝔍 ≤ P := fun x hx ↦ by
    rw [hPy, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact y.asIdeal.zero_mem
  have hPR : P.under R ≤ nilradical R := by
    rw [hPy]
    change Ideal.comap (algebraMap R R') (Ideal.comap (Ideal.Quotient.mk 𝔍) y.asIdeal) ≤ _
    rw [Ideal.comap_comap]
    exact hyR
  have hPmin := mem_minimalPrimes_of_under_le_nilradical (R := R) P hPR
  obtain ⟨h, hhP, hh⟩ := exists_mem_other_minimalPrimes hPmin
  have hle : ∀ Q : Ideal R', Q.IsPrime → h ∉ Q → P ≤ Q := fun Q _ hQ ↦
    le_of_notMem_of_mem_other hh Q hQ
  have hnilRh := nilradical_away_eq hhP hle
  have hd : Disjoint (Submonoid.powers h : Set R') P :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime h).2 hhP
  have : (nilradical (Localization.Away h)).IsPrime := by
    rw [hnilRh]
    exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers h) _ P hPprime hd
  have h𝔍nil : 𝔍.map (algebraMap R' (Localization.Away h)) ≤
      nilradical (Localization.Away h) := by
    rw [hnilRh]
    exact Ideal.map_mono h𝔍P
  -- The ring `A = R'[1/h] / (𝔍 N)`.
  obtain ⟨K', hK'⟩ : ∃ K' : Ideal (Localization.Away h),
      K' = 𝔍.map (algebraMap R' (Localization.Away h)) * nilradical (Localization.Away h) :=
    ⟨_, rfl⟩
  have hK'nil : K' ≤ nilradical (Localization.Away h) := hK' ▸ Ideal.mul_le_right
  have : (nilradical (Localization.Away h ⧸ K')).IsPrime := isPrime_nilradical_quotient hK'nil
  have hcomap : (nilradical (Localization.Away h ⧸ K')).comap
      (algebraMap R' (Localization.Away h ⧸ K')) = P := by
    rw [IsScalarTower.algebraMap_eq R' (Localization.Away h) (Localization.Away h ⧸ K'),
      ← Ideal.comap_comap, Ideal.Quotient.algebraMap_eq, comap_nilradical_quotient hK'nil,
      hnilRh]
    exact IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers h) _ hPprime hd
  have hIeq : 𝔍.map (algebraMap R' (Localization.Away h ⧸ K')) =
      (𝔍.map (algebraMap R' (Localization.Away h))).map (Ideal.Quotient.mk K') := by
    rw [Ideal.map_map, IsScalarTower.algebraMap_eq R' (Localization.Away h)
      (Localization.Away h ⧸ K'), Ideal.Quotient.algebraMap_eq]
  have hInil : IsNilpotent (𝔍.map (algebraMap R' (Localization.Away h ⧸ K'))) := by
    obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical (Localization.Away h ⧸ K')
    refine ⟨n, eq_bot_iff.2 ((Ideal.pow_right_mono ?_ n).trans hn.le)⟩
    rw [hIeq, nilradical_quotient_eq_map hK'nil]
    exact Ideal.map_mono h𝔍nil
  have hIN : 𝔍.map (algebraMap R' (Localization.Away h ⧸ K')) *
      nilradical (Localization.Away h ⧸ K') = ⊥ := by
    rw [hIeq, nilradical_quotient_eq_map hK'nil, ← Ideal.map_mul, ← hK',
      Ideal.map_quotient_self]
  -- The generic point `t` of `Spec A` and the local artinian ring `A_t`.
  have hgen : IsGenericPoint
      (⟨nilradical (Localization.Away h ⧸ K'), inferInstance⟩ :
        PrimeSpectrum (Localization.Away h ⧸ K')) Set.univ :=
    (PrimeSpectrum.closure_singleton _).trans
      (Set.eq_univ_of_forall fun q ↦ fun _ hx ↦ nilradical_le_prime q.asIdeal hx)
  have hmaxt : maximalIdeal (Localization.AtPrime (nilradical (Localization.Away h ⧸ K'))) =
      nilradical (Localization.AtPrime (nilradical (Localization.Away h ⧸ K'))) := by
    refine le_antisymm ?_ (nilradical_le_prime _)
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_le_iff_le_comap.2 fun x hx ↦ (mem_nilradical.1 hx).map _
  have : (nilradical (Localization.AtPrime (nilradical (Localization.Away h ⧸ K')))).IsMaximal :=
    hmaxt ▸ maximalIdeal.isMaximal _
  have : Ring.KrullDimLE 0 (Localization.AtPrime (nilradical (Localization.Away h ⧸ K'))) :=
    Ring.KrullDimLE.of_isMaximal_nilradical _
  have : IsArtinianRing (Localization.AtPrime (nilradical (Localization.Away h ⧸ K'))) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
      (R := Localization.AtPrime (nilradical (Localization.Away h ⧸ K')))
  have hAt : NoLargerLift (f := Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (Localization.AtPrime (nilradical (Localization.Away h ⧸ K'))) ξ := by
    refine noLargerLift_of_isArtinianRing R hy _ ?_
    rw [IsScalarTower.algebraMap_eq R' (Localization.Away h ⧸ K')
      (Localization.AtPrime (nilradical (Localization.Away h ⧸ K'))), ← Ideal.comap_comap,
      show Ideal.comap (algebraMap (Localization.Away h ⧸ K')
          (Localization.AtPrime (nilradical (Localization.Away h ⧸ K'))))
          (maximalIdeal (Localization.AtPrime (nilradical (Localization.Away h ⧸ K')))) =
          nilradical (Localization.Away h ⧸ K') from Localization.AtPrime.under_maximalIdeal,
      hcomap, hPy]
  -- Condition (F8).
  obtain ⟨g₀, ⟨q₀, hq₀⟩, Hg₀⟩ := h8 (Localization.Away h ⧸ K') _ hgen _ hInil hIN
    (baseOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Localization.Away h ⧸ K'))
    (restrictBase (Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (Localization.Away h ⧸ K') 𝔍 ξ)
    ((noLargerLift_restrictBase_iff _ _ 𝔍 _ ξ).2 hAt)
  have hg₀t : g₀ ∉ nilradical (Localization.Away h ⧸ K') := fun hm ↦
    (PrimeSpectrum.mem_basicOpen _ _).1 hq₀ (nilradical_le_prime _ hm)
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective g₀
  obtain ⟨⟨r₀, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers h) x
  have hr₀eq : algebraMap R' (Localization.Away h ⧸ K') r₀ =
      Ideal.Quotient.mk K' x * Ideal.Quotient.mk K' (algebraMap R' (Localization.Away h) s) := by
    rw [← map_mul, hs, IsScalarTower.algebraMap_apply R' (Localization.Away h)
      (Localization.Away h ⧸ K'), Ideal.Quotient.algebraMap_eq]
  have hdvd : Ideal.Quotient.mk K' x ∣ algebraMap R' (Localization.Away h ⧸ K') r₀ :=
    ⟨_, hr₀eq⟩
  have hr₀P : r₀ ∉ P := fun hm ↦ by
    rw [← hcomap, Ideal.mem_comap, hr₀eq] at hm
    have hu : IsUnit (Ideal.Quotient.mk K' (algebraMap R' (Localization.Away h) s)) :=
      (IsLocalization.map_units (Localization.Away h) s).map _
    exact hg₀t ((Ideal.mul_unit_mem_iff_mem _ hu).1 hm)
  have H' : ∀ g, algebraMap R' (Localization.Away h ⧸ K') r₀ ∣ g →
      NoLargerLift (f := baseOver (Spec.map (CommRingCat.ofHom (algebraMap R R')))
        (Localization.Away h ⧸ K')) (Localization.Away g)
        (restrictBase (Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (Localization.Away h ⧸ K') 𝔍 ξ) := fun g hg ↦ Hg₀ g (by
    obtain ⟨c, rfl⟩ := dvd_trans hdvd hg
    exact PrimeSpectrum.basicOpen_mul_le_left _ _)
  -- The conclusion at a prime `Q` of `R'` not containing `h r₀`.
  have key : ∀ (Q : Ideal R') [Q.IsPrime], h * r₀ ∉ Q →
      IsNilpotent (𝔍.map (algebraMap R' (Localization.AtPrime Q))) ∧
        NoLargerLift (f := Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (Localization.AtPrime Q) ξ := by
    intro Q _ hQ
    have hhQ : h ∉ Q := fun hm ↦ hQ (Q.mul_mem_right _ hm)
    have hr₀Q : r₀ ∉ Q := fun hm ↦ hQ (Q.mul_mem_left _ hm)
    have hpow : Submonoid.powers h ≤ Q.primeCompl := Submonoid.powers_le.2 hhQ
    let : Algebra (Localization.Away h) (Localization.AtPrime Q) :=
      IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers h) Q.primeCompl hpow
    have : IsScalarTower R' (Localization.Away h) (Localization.AtPrime Q) :=
      IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hpow
    have : IsLocalization (Q.primeCompl.map (algebraMap R' (Localization.Away h)))
        (Localization.AtPrime Q) :=
      IsLocalization.isLocalization_of_submonoid_le _ _ _ _ hpow
    have hnilQ : 𝔍.map (algebraMap R' (Localization.AtPrime Q)) ≤
        nilradical (Localization.AtPrime Q) := by
      rw [IsScalarTower.algebraMap_eq R' (Localization.Away h) (Localization.AtPrime Q),
        ← Ideal.map_map]
      exact (Ideal.map_mono h𝔍nil).trans
        (Ideal.map_le_iff_le_comap.2 fun x hx ↦ (mem_nilradical.1 hx).map _)
    refine ⟨?_, ?_⟩
    · obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical (Localization.AtPrime Q)
      exact ⟨n, eq_bot_iff.2 ((Ideal.pow_right_mono hnilQ n).trans hn.le)⟩
    have hmem : algebraMap R' (Localization.Away h ⧸ K') r₀ ∈
        Algebra.algebraMapSubmonoid (Localization.Away h ⧸ K')
          (Q.primeCompl.map (algebraMap R' (Localization.Away h))) :=
      ⟨algebraMap R' (Localization.Away h) r₀, ⟨r₀, hr₀Q, rfl⟩,
        (IsScalarTower.algebraMap_apply R' (Localization.Away h)
          (Localization.Away h ⧸ K') r₀).symm⟩
    have HB := noLargerLift_of_isLocalization
      (baseOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Localization.Away h ⧸ K')) _
      (Localization.AtPrime Q ⧸ K'.map (algebraMap (Localization.Away h)
        (Localization.AtPrime Q))) hZ h2 _ _ hmem H'
    have : IsScalarTower R' (Localization.Away h ⧸ K') (Localization.AtPrime Q ⧸
        K'.map (algebraMap (Localization.Away h) (Localization.AtPrime Q))) :=
      IsScalarTower.of_algebraMap_eq (R := R') (S := Localization.Away h ⧸ K')
        (A := Localization.AtPrime Q ⧸
          K'.map (algebraMap (Localization.Away h) (Localization.AtPrime Q))) fun r ↦ by
        change Ideal.Quotient.mk _ (algebraMap R' (Localization.AtPrime Q) r) =
          Ideal.Quotient.mk _ (algebraMap (Localization.Away h) (Localization.AtPrime Q)
            (algebraMap R' (Localization.Away h) r))
        rw [← IsScalarTower.algebraMap_apply]
    have HB' := (noLargerLift_restrictBase_iff _ _ 𝔍 _ ξ).1 HB
    refine noLargerLift_of_surjective (Ideal.Quotient.mkₐ R'
      (K'.map (algebraMap (Localization.Away h) (Localization.AtPrime Q))))
      (Ideal.Quotient.mkₐ_surjective R' _) ?_ HB'
    change RingHom.ker (Ideal.Quotient.mk _) ≤ _
    rw [Ideal.mk_ker, hK', Ideal.map_mul, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    refine (Ideal.mul_mono_right ?_).trans_eq (mul_comm _ _)
    exact Ideal.map_le_iff_le_comap.2 fun x hx ↦
      Ideal.mem_comap.2 (nilradical_le_prime _ (mem_nilradical.2 ((mem_nilradical.1 hx).map _)))
  -- The neighbourhood `V = D(h r₀)`.
  refine ⟨PrimeSpectrum.basicOpen (Ideal.Quotient.mk 𝔍 (h * r₀)),
    PrimeSpectrum.isOpen_basicOpen, ?_, fun w hw ↦ key _ ?_⟩
  · rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
    intro hm
    have : h * r₀ ∈ P := by rw [hPy]; exact hm
    exact (hPprime.mem_or_mem this).elim hhP hr₀P
  · rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hw
    exact hw

end EtaleLocus

end Langlands.AlgebraicGeometry.UnramifiedFunctor
