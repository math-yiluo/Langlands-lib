import Mathlib.RingTheory.LocalProperties.Basic
import Langlands.GroupScheme.Reductive.AffineSplitSurjectionLocalBaseChange
import Langlands.GroupScheme.Reductive.AffineSplitSurjectionFieldIsogeny

/-! # Proof: quasi-finite surjections of split reductive groups respect the splittings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffineSplitSurjection

variable {R : Type u} [CommRing R]

/-- If `t * n = 0` in `R`, then the integer `n` vanishes on the basic open set of `t`. -/
theorem natCast_eq_zero_on_basicOpen {t : R} {n : ℕ} (h : t * n = 0) :
    (n : Γ(Spec (CommRingCat.of R),
      (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv t))) = 0 := by
  let X := Spec (CommRingCat.of R)
  let f : Γ(X, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv t
  let ρ := X.presheaf.map (homOfLE (X.basicOpen_le f)).op
  have hu : IsUnit (ρ f) := X.toRingedSpace.isUnit_res_basicOpen f
  have hmul : ρ f * (n : Γ(X, X.basicOpen f)) = 0 := by
    rw [← map_natCast ρ.hom n, ← map_natCast (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom n,
      ← map_mul, ← map_mul, h, map_zero, map_zero]
  exact hu.mul_right_eq_zero.mp hmul

/-- The closed point of the spectrum of the localization at a prime `s` lies over `s`, so the
spectrum of the localization maps into every open set containing `s`. -/
theorem algebraBaseMap_preimage_basicOpen_eq_top (s : Spec (CommRingCat.of R)) {e : R}
    (hs : s ∈ (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv e)) :
    algebraBaseMap R (Localization.AtPrime s.asIdeal) ⁻¹ᵁ
      (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv e) = ⊤ := by
  apply Scheme.preimage_eq_top_of_closedPoint_mem
  rw [basicOpen_eq_of_affine] at hs ⊢
  change e ∉ (PrimeSpectrum.comap (algebraMap R (Localization.AtPrime s.asIdeal))
    (IsLocalRing.closedPoint (Localization.AtPrime s.asIdeal))).asIdeal
  rw [PrimeSpectrum.comap_asIdeal]
  change e ∉ Ideal.comap (algebraMap R (Localization.AtPrime s.asIdeal))
    (IsLocalRing.maximalIdeal (Localization.AtPrime s.asIdeal))
  have hu : Ideal.comap (algebraMap R (Localization.AtPrime s.asIdeal))
      (IsLocalRing.maximalIdeal (Localization.AtPrime s.asIdeal)) = s.asIdeal :=
    Localization.AtPrime.under_maximalIdeal (I := s.asIdeal)
  have hs' : e ∉ s.asIdeal := hs
  exact fun hmem => hs' ((Ideal.ext_iff.mp hu e).mp hmem)

variable {I I' : Type u} [Fintype I] [Fintype I']

/-- **Assembly.** Given the field-level construction of a root-datum isogeny whose weight map
is a prescribed locally constant character map, the two conclusions of the statement follow:
the character map is locally constant on basic open sets of idempotents, the characteristic
exponent vanishes on a smaller neighbourhood by the local computation on root groups, and on a
connected base the idempotent is `1` and the vanishing holds in every localization. -/
theorem characterMapOn_of_fieldIsogeny
    {G H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (hG : IsReductive G) (hH : IsReductive H)
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}
    {J J' : Type u} [Finite J] [Finite J']
    {P : RootDatum J (I → ℤ) (I → ℤ)} {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
    [P.IsReduced] [Q.IsReduced]
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hrootG : ∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') i')
    (hQ : IsFibrewiseRootDatumOf I' H i' Q)
    (hrootH : ∀ α : J', Nonempty
      (splitTorus.exponentWeightSpace I' H i' (Q.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    {φ : G ⟶ H}
    {τ : splitTorus (Spec (CommRingCat.of R)) I ⟶ splitTorus (Spec (CommRingCat.of R)) I'}
    [LocallyQuasiFinite φ.hom.hom.left] (hsq : i ≫ φ = τ ≫ i')
    (hfield : ∀ (V : (Spec (CommRingCat.of R)).Opens) (h : (I' → ℤ) →ₗ[ℤ] (I → ℤ)),
      splitTorus.CharacterMapOn τ V h → ∀ s ∈ V,
        ∃ (p : ℕ) (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P), r.weightMap = h) :
    (∀ s : Spec (CommRingCat.of R), ∃ V : (Spec (CommRingCat.of R)).Opens, s ∈ V ∧
        ∃ (p : ℕ) (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P),
          (∀ j' : J', f.rootFactor j' ≠ 1 → (p : Γ(Spec (CommRingCat.of R), V)) = 0) ∧
          splitTorus.CharacterMapOn τ V f.weightMap) ∧
      (ConnectedSpace (Spec (CommRingCat.of R)) →
        ∃ (p : ℕ) (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P),
          (∀ j' : J', f.rootFactor j' ≠ 1 → (p : R) = 0) ∧
          splitTorus.CharacterMapOn τ ⊤ f.weightMap) := by
  classical
  refine ⟨fun s => ?_, fun hconn => ?_⟩
  · obtain ⟨e, -, hse, h, hV⟩ := splitTorus.exists_isIdempotentElem_characterMapOn τ s
    obtain ⟨p, r, hr⟩ := hfield _ h hV s hse
    by_cases hβ : ∃ β, r.rootFactor β ≠ 1
    · obtain ⟨β, hβ⟩ := hβ
      have hp := natCast_eq_zero_of_local_baseChange (Localization.AtPrime s.asIdeal) hG hH
        hmax hP hrootG hmax' hQ hrootH hsq hV r hr
        (algebraBaseMap_preimage_basicOpen_eq_top s hse) β hβ
      obtain ⟨⟨t, ht⟩, htp⟩ := IsLocalization.exists_of_eq
        (M := s.asIdeal.primeCompl) (S := Localization.AtPrime s.asIdeal)
        (x := (p : R)) (y := 0) (by rw [map_natCast, map_zero]; exact hp)
      rw [mul_zero] at htp
      have hes : e ∉ s.asIdeal := by
        rw [basicOpen_eq_of_affine] at hse
        exact hse
      refine ⟨(Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (e * t)),
        ?_, p, r, fun _ _ => ?_, ?_⟩
      · rw [basicOpen_eq_of_affine]
        change e * t ∉ s.asIdeal
        intro hmem
        rcases s.isPrime.mem_or_mem hmem with h₁ | h₁
        · exact hes h₁
        · exact ht h₁
      · apply natCast_eq_zero_on_basicOpen
        rw [mul_assoc, htp, mul_zero]
      · intro U hU x m
        rw [hr]
        apply hV U _ x m
        apply top_le_iff.mp
        rw [← hU]
        apply Scheme.Hom.preimage_mono
        rw [map_mul, Scheme.basicOpen_mul]
        exact inf_le_left
    · push Not at hβ
      exact ⟨_, hse, p, r, fun j' hj' => absurd (hβ j') hj', hr ▸ hV⟩
  · obtain ⟨s⟩ : Nonempty (Spec (CommRingCat.of R)) := inferInstance
    obtain ⟨e, he, hse, h, hV⟩ := splitTorus.exists_isIdempotentElem_characterMapOn τ s
    obtain ⟨p, r, hr⟩ := hfield _ h hV s hse
    have htop : (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv e) =
        ⊤ := by
      have hclopen : IsClopen ((Spec (CommRingCat.of R)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv e) : Set (Spec (CommRingCat.of R))) := by
        rw [basicOpen_eq_of_affine]
        exact PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩
      rcases isClopen_iff.mp hclopen with h₀ | h₁
      · exact absurd (h₀ ▸ hse : s ∈ (∅ : Set (Spec (CommRingCat.of R)))) (Set.notMem_empty s)
      · exact SetLike.coe_injective h₁
    refine ⟨p, r, fun β hβ => ?_, ?_⟩
    · apply eq_zero_of_localization
      intro 𝔪 _
      rw [map_natCast]
      refine natCast_eq_zero_of_local_baseChange (Localization.AtPrime 𝔪) hG hH
        hmax hP hrootG hmax' hQ hrootH hsq hV r hr ?_ β hβ
      rw [htop, Scheme.Hom.preimage_top]
    · rw [hr, ← htop]
      exact hV

end Langlands.GroupScheme.AffineSplitSurjection

namespace Langlands.GroupScheme

open AffineSplitSurjection

/-- **Quasi-finite surjections between split reductive groups are compatible with the
splittings** (Conrad, *Reductive group schemes* (2014), Proposition 6.1.7, over `Spec R`). -/
theorem affineSplitSurjectionRootDatum : AffineSplitSurjectionRootDatumStatement.{u} := by
  intro R _ G H hG hH I I' _ _ i i' J J' _ _ P Q _ _ _ hmax hP hrootG _ hmax' hQ hrootH φ τ hφ
    hsurj hsq
  have := hG.isAffineHom
  have := hH.isAffineHom
  have := hφ
  obtain ⟨h₁, h₂⟩ := characterMapOn_of_fieldIsogeny hG hH hmax hP hrootG hmax' hQ hrootH hsq
    (fun V h hV s hs =>
      exists_rootDatumIsogeny_weightMap hG hH hmax hP hmax' hQ hφ hsurj hsq hV s hs)
  refine ⟨h₁, fun hconn => ?_⟩
  obtain ⟨p, f, hp, hf⟩ := h₂ hconn
  exact ⟨p, f, hp, fun U x m => hf U (Scheme.Hom.preimage_top _) x m⟩

end Langlands.GroupScheme
