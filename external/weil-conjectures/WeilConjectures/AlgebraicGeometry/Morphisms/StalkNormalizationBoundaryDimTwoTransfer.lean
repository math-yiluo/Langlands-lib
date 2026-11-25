/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationNormalDense
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteNormalDenseEtaleGoingDown
import WeilConjectures.RingTheory.SmoothNormalRing
import WeilConjectures.RingTheory.KrullDimension.GoingDown
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.RingTheory.Depth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization

/-!
# Boundary dimension estimate transferred along finite normalizations

## References

* Stacks Project, Tags 0337, 00LK, 033C and 00H8
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
private theorem normal_stalks_of_smooth_integral_base {X Y : Scheme.{u}} [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (g : X ⟶ Y) [Smooth g] (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨U, hU, V, hV, hx, hVU, hg⟩ := Smooth.exists_isStandardSmooth g x
  let : Nonempty U := ⟨⟨g x, hVU hx⟩⟩
  let : IsIntegrallyClosed Γ(Y, U) := isIntegrallyClosed_of_isIntegrallyClosed_stalk hY U
  have hnormal := (g.smooth_appLE hU hV hVU).isNormalRing (fun p hp ↦ by
    let : IsIntegrallyClosed (Localization.AtPrime p) :=
      isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
    exact ⟨inferInstance, inferInstance⟩)
  let : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  let p := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  obtain ⟨hd, hi⟩ := hnormal p
  let : IsDomain (Localization.AtPrime p) := hd
  let : IsIntegrallyClosed (Localization.AtPrime p) := hi
  let e := IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
    (X.presheaf.stalk x)
  exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

private theorem normal_stalks_of_flat_preimmersion {X Y : Scheme.{u}}
    (g : X ⟶ Y) [Flat g] [IsPreimmersion g]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y)) (x : X) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨hd, hi⟩ := hY (g x)
  let : IsDomain (Y.presheaf.stalk (g x)) := hd
  let : IsIntegrallyClosed (Y.presheaf.stalk (g x)) := hi
  algebraize [(g.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (g x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap g x) (g.toLRSHom.prop x)
  have hf : RingHom.FaithfullyFlat (g.stalkMap x).hom :=
    ‹Module.FaithfullyFlat (Y.presheaf.stalk (g x)) (X.presheaf.stalk x)›
  let e := RingEquiv.ofBijective (g.stalkMap x).hom
    ⟨hf.injective,
      g.stalkMap_surjective x⟩
  exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e⟩

private theorem normalization_etale_restrict {P X : Scheme.{u}} (V : X.Opens)
    (π : P ⟶ V.toScheme) [IsFinite π] [Etale π] [QuasiCompact V.ι] :
    Etale ((π ≫ V.ι).fromNormalization ∣_ V) := by
  let f := π ≫ V.ι
  have hpb : IsPullback (𝟙 P) π f V.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by simp [f]⟩
  have hfin : IsFinite (pullback.snd f V.ι) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite hpb.isoPullback.hom,
      hpb.isoPullback_hom_snd]
    infer_instance
  have het : Etale (pullback.snd f V.ι) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @Etale hpb.isoPullback.hom,
      hpb.isoPullback_hom_snd]
    infer_instance
  have hn : Etale (pullback.snd f V.ι).fromNormalization := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @Etale
      (pullback.snd f V.ι).toNormalization, Hom.toNormalization_fromNormalization]
    exact het
  have hp : Etale (pullback.snd f.fromNormalization V.ι) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso @Etale (f.normalizationPullback V.ι),
      Hom.normalizationPullback_snd]
    exact hn
  rw [← MorphismProperty.cancel_left_of_respectsIso @Etale
    (pullbackRestrictIsoRestrict f.fromNormalization V).hom,
    pullbackRestrictIsoRestrict_hom_morphismRestrict]
  exact hp

set_option backward.isDefEq.respectTransparency false in
private theorem morphismProperty_pullback_restrict
    (p : MorphismProperty Scheme.{u}) [p.IsStableUnderBaseChange]
    {X Y T : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y) (U : Y.Opens) (hf : p (f ∣_ U)) :
    p (pullback.snd f g ∣_ (g ⁻¹ᵁ U)) := by
  let n := pullback.snd f g
  have hp := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g)
    (US := U) (UT := g ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U)
    (UY := n ⁻¹ᵁ (g ⁻¹ᵁ U)) le_rfl le_rfl (by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
      exact (inf_idem _).symm)
  dsimp only [n] at hp
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at hp
  exact p.of_isPullback hp hf

private theorem local_dimension_le_of_goingDown
    {R T : Type u} [CommRing R] [CommRing T] [IsLocalRing R] [IsLocalRing T]
    (φ : R →+* T) [IsLocalHom φ]
    (hgoing : letI := φ.toAlgebra; Algebra.HasGoingDown R T) :
    ringKrullDim R ≤ ringKrullDim T := by
  let := φ.toAlgebra
  let : Algebra.HasGoingDown R T := hgoing
  apply ringKrullDim_le_of_goingDown_of_surjective φ hgoing
  intro p
  let : (IsLocalRing.maximalIdeal T).LiesOver (IsLocalRing.maximalIdeal R) := by
    constructor
    exact (IsLocalRing.maximalIdeal_comap φ).symm
  obtain ⟨q, _, hq, hlo⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (IsLocalRing.maximalIdeal T) (IsLocalRing.le_maximalIdeal_of_isPrime p.asIdeal)
  exact ⟨⟨q, hq⟩, PrimeSpectrum.ext_iff.mpr hlo.over.symm⟩

/-- Finite normalizations transfer the boundary dimension estimate to source stalks. -/
theorem stalk_normalization_boundary_dimension_two_transfer {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S)
    (hboundary : let a := S.fromSpecStalk s
      ∀ y : (pullback c a : Scheme.{u}),
        y ∉ (pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U) →
        (2 : WithBot ℕ∞) ≤ ringKrullDim ((pullback c a).presheaf.stalk y)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    IsFinite n → ∀ z : (pullback
      (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a) : Scheme.{u}),
      n z ∉ (pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U) →
      (2 : WithBot ℕ∞) ≤ ringKrullDim
        ((pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
          (pullback.fst c a) : Scheme.{u}).presheaf.stalk z) := by
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  intro a n hn z hz
  let : IsFinite n := hn
  let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
  let l := pullback.fst c a
  let V := l ⁻¹ᵁ (c ⁻¹ᵁ U)
  have hnormal := stalk_normalization_normal_and_dense hS c U PA s
  have het : Etale (n ∣_ V) :=
    morphismProperty_pullback_restrict @Etale f.fromNormalization l (c ⁻¹ᵁ U)
      (normalization_etale_restrict (c ⁻¹ᵁ U) PA.obj.hom)
  have hL := normal_stalks_of_flat_preimmersion l
    (normal_stalks_of_smooth_integral_base hS c)
  have hgoing := finite_normal_dense_etale_stalk_goingDown n hL hnormal.1 V
    hnormal.2 het z
  exact (hboundary (n z) hz).trans
    (local_dimension_le_of_goingDown (n.stalkMap z).hom hgoing)
end AlgebraicGeometry.Scheme
