/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # The Cartier complement over its generic DVR stalk

## References

* Stacks Project, Tag 01WQ
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem fractionRing_away_uniformizer
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ (FractionRing R) := by
  apply (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ)
    (nonZeroDivisors R) ?_ ?_).mpr inferInstance
  · rintro x ⟨n, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hϖ.ne_zero)
  · intro x hx
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp hx) hϖ
    exact ⟨ϖ ^ n, ⟨n, rfl⟩, hn.dvd⟩

private theorem dvr_prime_dichotomy
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (x : PrimeSpectrum R) : x.asIdeal = ⊥ ∨ x = IsLocalRing.closedPoint R := by
  by_cases hx : x.asIdeal = ⊥
  · exact Or.inl hx
  · right
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal (x.isPrime.isMaximal hx)

private theorem cartier_preimage_closedPoint
    {N D : Scheme.{u}} (j : D ⟶ N) (hj : IsEffectiveCartierCenter j)
    (z : N) (hz : z ∈ Set.range j)
    [IsDomain (N.presheaf.stalk z)] [IsDiscreteValuationRing (N.presheaf.stalk z)]
    (x : Spec (N.presheaf.stalk z)) :
    N.fromSpecStalk z x ∈ Set.range j ↔
      x = IsLocalRing.closedPoint (N.presheaf.stalk z) := by
  let R := N.presheaf.stalk z
  obtain ⟨J, hJ, α, hα⟩ := hj
  have hr : Set.range j = (J.support : Set N) := by
    rw [← hα]
    change Set.range (J.subschemeι ∘ α.hom) = _
    have hs : Set.range α.hom = Set.univ :=
      Set.range_eq_univ.mpr (Scheme.Hom.homeomorph α.hom).surjective
    rw [Set.range_comp, hs,
      Set.image_univ, IdealSheafData.range_subschemeι]
  let I := J.comap (N.fromSpecStalk z)
  have hI : I.IsInvertible := hJ.comap_of_flat (N.fromSpecStalk z)
  obtain ⟨U, hU, a, ha, hgen⟩ := hI (IsLocalRing.closedPoint R)
  have htop : U = ⟨⊤, isAffineOpen_top _⟩ :=
    Subtype.ext ((IsLocalRing.closedPoint_mem_iff U.1).mp hU)
  subst U
  have hsupport : (I.support : Set (Spec R)) = (Spec R).zeroLocus ({a} : Set Γ(Spec R, ⊤)) := by
    have heq : I = IdealSheafData.ofIdealTop (Ideal.span {a}) :=
      IdealSheafData.ext_of_isAffine (by simpa using hgen)
    rw [heq, IdealSheafData.coe_support_ofIdealTop, Scheme.zeroLocus_span]
  have hmem : N.fromSpecStalk z x ∈ Set.range j ↔ x ∈ I.support := by
    rw [hr, IdealSheafData.support_comap]
    rfl
  rw [hmem]
  constructor
  · intro hx
    rcases dvr_prime_dichotomy R x with hbot | hclosed
    · have hx' : x ∈ PrimeSpectrum.zeroLocus
          ((ΓSpecIso R).inv ⁻¹' ({a} : Set Γ(Spec R, ⊤))) := by
        change x ∈ (I.support : Set (Spec R)) at hx
        rwa [hsupport, Spec_zeroLocus] at hx
      have helem : (ΓSpecIso R).hom a ∈ x.asIdeal :=
        hx' (by simp)
      have ha0 : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp ha
      apply False.elim
      apply ha0
      have helem0 : (ΓSpecIso R).hom a = 0 := by simpa [hbot] using helem
      exact ((ConcreteCategory.bijective_of_isIso (ΓSpecIso R).hom).1)
        (by simpa using helem0)
    · exact hclosed
  · rintro rfl
    apply hmem.mp
    simpa only [fromSpecStalk_closedPoint] using hz

/-- The Cartier complement at its generic DVR stalk is the fraction-field spectrum. -/
theorem cartier_stalk_punctured_complement
    {N : Scheme.{u}} [IsLocallyNoetherian N] (V : N.Opens)
    (D : Scheme.{u}) (j : D ⟶ N) (hD : IsIntegral D)
    (hj : IsEffectiveCartierCenter j) (hV : ∀ z : N, z ∈ V ↔ z ∉ Set.range j)
    (η : D) (hη : IsGenericPoint η Set.univ)
    [IsDomain (N.presheaf.stalk (j η))]
    [IsDiscreteValuationRing (N.presheaf.stalk (j η))] :
    let R := N.presheaf.stalk (j η)
    ∃ t : Spec (CommRingCat.of (FractionRing R)) ⟶ V.toScheme,
      IsPullback t (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
        V.ι (N.fromSpecStalk (j η)) := by
  have := hD
  have := hη
  let R := N.presheaf.stalk (j η)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away ϖ (FractionRing R) :=
    fractionRing_away_uniformizer R ϖ hϖ
  let i := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have : IsOpenImmersion i := IsOpenImmersion.of_isLocalization ϖ
  have hr : Set.range i = {x | ϖ ∉ x.asIdeal} :=
    PrimeSpectrum.localization_away_comap_range (FractionRing R) ϖ
  have haway (x : Spec R) : x ∈ i.opensRange ↔ x ≠ IsLocalRing.closedPoint R := by
    change x ∈ Set.range i ↔ _
    rw [hr]
    change ϖ ∉ x.asIdeal ↔ _
    constructor
    · intro hx heq
      subst x
      apply hx
      change ϖ ∈ IsLocalRing.maximalIdeal R
      rw [hϖ.maximalIdeal_eq]
      exact Ideal.subset_span (Set.mem_singleton ϖ)
    · intro hx
      rcases dvr_prime_dichotomy R x with hbot | hclosed
      · simpa only [hbot, Ideal.mem_bot] using hϖ.ne_zero
      · exact False.elim (hx hclosed)
  have hpre : (N.fromSpecStalk (j η)) ⁻¹ᵁ V = i.opensRange := by
    ext x
    change N.fromSpecStalk (j η) x ∈ V ↔ x ∈ i.opensRange
    rw [hV, haway, cartier_preimage_closedPoint j hj (j η) ⟨η, rfl⟩ x]
  have hfactor : Set.range (i ≫ N.fromSpecStalk (j η)) ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Opens.range_ι]
    change N.fromSpecStalk (j η) (i x) ∈ V
    change i x ∈ (N.fromSpecStalk (j η)) ⁻¹ᵁ V
    rw [hpre]
    exact Set.mem_range_self x
  refine ⟨IsOpenImmersion.lift V.ι (i ≫ N.fromSpecStalk (j η)) hfactor, ?_⟩
  apply IsOpenImmersion.isPullback
  · exact (IsOpenImmersion.lift_fac _ _ hfactor).symm
  · simpa only [Opens.opensRange_ι] using hpre

end AlgebraicGeometry.Scheme
