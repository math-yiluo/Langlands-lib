import Langlands.AlgebraicGeometry.AffineQuotientPullback
import Langlands.AlgebraicGeometry.StandardEtaleLift
import Langlands.GroupScheme.Torus.MultiplicativeTypePointwiseSplitting
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Cartesian lifting of étale splitting covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry

/-- An étale morphism to an affine base admits a standard étale chart at each point. -/
theorem exists_standardEtale_chart {R : Type u} [CommRing R] {U : Scheme.{u}}
    (p : U ⟶ Spec (CommRingCat.of R)) [Etale p] (x : U) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C),
      Algebra.IsStandardEtale R C ∧
        ∃ (a : Spec (CommRingCat.of C) ⟶ U) (z : Spec (CommRingCat.of C)),
          a z = x ∧ a ≫ p = Spec.algebraMap R C := by
  let 𝒱 := U.affineOpenCover
  let i := 𝒱.idx x
  obtain ⟨y, hy⟩ := 𝒱.covers x
  let φ : CommRingCat.of R ⟶ 𝒱.X i := Spec.preimage (𝒱.f i ≫ p)
  have hφ : Spec.map φ = 𝒱.f i ≫ p := Spec.map_preimage _
  let : Algebra R (𝒱.X i) := φ.hom.toAlgebra
  have : Algebra.Etale R (𝒱.X i) := by
    have h : Etale (Spec.map φ) := by
      rw [hφ]
      infer_instance
    exact RingHom.etale_algebraMap.mp (HasRingHomProperty.Spec_iff.mp h)
  obtain ⟨f, hf, hC⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) y.asIdeal
  let C := Localization.Away f
  obtain ⟨z, hz⟩ := (PrimeSpectrum.localization_away_comap_range C f).ge hf
  refine ⟨C, inferInstance, inferInstance, hC, Spec.algebraMap (𝒱.X i) C ≫ 𝒱.f i, z, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply]
    exact (congrArg (𝒱.f i) hz).trans hy
  · rw [Category.assoc, ← hφ, Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact (IsScalarTower.algebraMap_eq R (𝒱.X i) C).symm

end Langlands.AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeMultiplicativeType

open Langlands.AlgebraicGeometry

/-- Identify the quotient by the extended base ideal with the specified reduction ring. -/
def quotientChartRingEquiv {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] (J : Ideal A) (q : B →+* C) (hsurj : Function.Surjective q)
    (hker : RingHom.ker q = J.map (algebraMap A B)) :
    B ⧸ J.map (algebraMap A B) ≃+* C :=
  (Ideal.quotEquivOfEq hker.symm).trans (q.quotientKerEquivOfSurjective hsurj)

private theorem isPullback_spec_of_quotient {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    (J : Ideal A) [Algebra (A ⧸ J) C] (q : B →+* C)
    (hcomm : q.comp (algebraMap A B) =
      (algebraMap (A ⧸ J) C).comp (Ideal.Quotient.mk J))
    (hsurj : Function.Surjective q) (hker : RingHom.ker q = J.map (algebraMap A B)) :
    IsPullback (Spec.map (CommRingCat.ofHom q)) (Spec.algebraMap (A ⧸ J) C)
      (Spec.algebraMap A B) (Spec.algebraMap A (A ⧸ J)) := by
  let e := quotientChartRingEquiv J q hsurj hker
  have he (b : B) : e (Ideal.Quotient.mk _ b) = q b := by
    simp [e, quotientChartRingEquiv]
  have hpush : IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (algebraMap (A ⧸ J) C))
      (CommRingCat.ofHom q) := by
    refine (Langlands.AlgebraicGeometry.isPushout_quotient_map (algebraMap A B) J).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toCommRingCatIso (by simp) (by simp) ?_ ?_
    · apply CommRingCat.hom_ext
      ext x
      change e (Ideal.Quotient.mk _ (algebraMap A B x)) = _
      rw [he]
      exact DFunLike.congr_fun hcomm x
    · apply CommRingCat.hom_ext
      ext b
      exact he b
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ hpush).flip

/-- Every point of the quotient base lies in a splitting chart that is the actual
reduction of an étale chart over the original base. -/
theorem exists_splitChartLift {A : Type u} [CommRing A] (J : Ideal A)
    {H₀ : GroupScheme (Spec (CommRingCat.of (A ⧸ J)))} (hH₀ : IsMultiplicativeType H₀)
    (x : Spec (CommRingCat.of (A ⧸ J))) :
    ∃ (V V₀ : Scheme.{u}) (p : V ⟶ Spec (CommRingCat.of A))
      (p₀ : V₀ ⟶ Spec (CommRingCat.of (A ⧸ J))) (q : V₀ ⟶ V),
      Etale p ∧ x ∈ Set.range p₀ ∧ IsPullback q p₀ p (Spec.algebraMap A (A ⧸ J)) ∧
        IsDiagonalizable ((baseChange p₀).obj H₀) := by
  obtain ⟨U, f, hf, ⟨y, hy⟩, hsplit⟩ := hH₀.exists_etale_diagonalizable x
  let _ : Etale f := hf
  obtain ⟨C, _, _, hC, a, z, hz, ha⟩ := exists_standardEtale_chart f y
  let _ : Algebra.IsStandardEtale (A ⧸ J) C := hC
  obtain ⟨B, _, _, hB, q, hcomm, hsurj, hker⟩ :=
    StandardEtaleLift.exists_etale_quotient_lift A J C
  refine ⟨Spec (CommRingCat.of B), Spec (CommRingCat.of C), Spec.algebraMap A B,
    Spec.algebraMap (A ⧸ J) C, Spec.map (CommRingCat.ofHom q), ?_, ?_,
    isPullback_spec_of_quotient J q hcomm hsurj hker, ?_⟩
  · exact HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hB)
  · refine ⟨z, ?_⟩
    rw [← ha, Scheme.Hom.comp_apply, hz, hy]
  · rw [← ha]
    exact (hsplit.baseChange a).of_iso (baseChangeCompIso f a H₀)

end Langlands.GroupScheme.RelativeMultiplicativeType
