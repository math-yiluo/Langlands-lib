import Mathlib

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.SmoothReducedProof

universe u v

lemma isReduced_of_etale_of_domain (R : Type u) (A : Type v) [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Algebra.Etale R A] : IsReduced A := by
  let K := FractionRing R
  have : IsReduced (K ⊗[R] A) := Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A)
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))

lemma isReduced_of_smooth_of_domain (R : Type u) (A : Type v) [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Algebra.Smooth R A] : IsReduced A := by
  constructor
  intro x hx
  apply eq_zero_of_localization x
  intro P hP
  obtain ⟨f, hf, n, hAlg, hTower, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := P)
  let := hAlg
  let := hTower
  let := hEtale
  have : IsReduced (Localization.Away f) :=
    isReduced_of_etale_of_domain (MvPolynomial (Fin n) R) _
  have hz : algebraMap A (Localization.Away f) x = 0 :=
    (hx.map (algebraMap A (Localization.Away f))).eq_zero
  have hu : IsUnit (algebraMap A (Localization.AtPrime P) f) :=
    IsLocalization.map_units (M := P.primeCompl) (Localization.AtPrime P) ⟨f, hf⟩
  simpa using congrArg (IsLocalization.Away.lift (S := Localization.Away f) f hu) hz

lemma isReduced_of_smooth_over_field (K : Type u) [Field K] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of K)) [Smooth p] : AlgebraicGeometry.IsReduced X := by
  apply +allowSynthFailures @AlgebraicGeometry.IsReduced.of_openCover X X.affineCover
  intro i
  let q := X.affineCover.f i ≫ p
  have : Smooth q := inferInstance
  let g : CommRingCat.of K ⟶ Γ(X.affineCover.X i, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop
  have hg : g.hom.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.bijective)
    (HasRingHomProperty.appTop @Smooth q inferInstance)
  algebraize [g.hom]
  have : Algebra.Smooth K Γ(X.affineCover.X i, ⊤) := (RingHom.smooth_algebraMap).mp hg
  have : _root_.IsReduced Γ(X.affineCover.X i, ⊤) := isReduced_of_smooth_of_domain K _
  exact isReduced_of_isAffine_isReduced _

lemma geometricallyReduced_of_smooth {X S : Scheme.{u}} (p : X ⟶ S) [Smooth p] :
    GeometricallyReduced p := by
  constructor
  intro K _ y Z fst snd h
  have : Smooth snd := MorphismProperty.of_isPullback h ‹Smooth p›
  exact isReduced_of_smooth_over_field K Z snd

end Langlands.AlgebraicGeometry.SmoothReducedProof
