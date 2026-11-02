import Langlands.AlgebraicGeometry.Picard.DiscreteValuationRingSelfProductLineBundleExtensionStatement
import Langlands.AlgebraicGeometry.Picard.SelfProductBaseChange
import Langlands.AlgebraicGeometry.Picard.OpenImmersionLineBundleExtensionProof
import Langlands.CommutativeAlgebra.SmoothDVRFactorialLocalizationsProof
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Extension of self-product line bundles over a trait -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry

/-- The specified fraction field of a DVR is the localization at any uniformizer. -/
theorem isLocalizationAway_fractionRing_of_dvr
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π) :
    IsLocalization.Away π K := by
  have hle : Submonoid.powers π ≤ nonZeroDivisors R := by
    rintro x ⟨n, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hπ.ne_zero)
  have hdiv : ∀ x ∈ nonZeroDivisors R, ∃ y ∈ Submonoid.powers π, x ∣ y := by
    intro x hx
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp hx) hπ
    exact ⟨π ^ n, ⟨n, rfl⟩, hn.dvd⟩
  exact (IsLocalization.iff_of_le_of_exists_dvd (S := K)
    (Submonoid.powers π) (nonZeroDivisors R) hle hdiv).mpr inferInstance

/-- The actual map from a specified fraction field to a DVR spectrum is open. -/
theorem isOpenImmersion_spec_fractionRing_of_dvr
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have := isLocalizationAway_fractionRing_of_dvr R K hπ
  exact IsOpenImmersion.of_isLocalization π

/-- Every stalk of a smooth scheme over a DVR is factorial. -/
theorem smoothDVR_factorialStalks
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of R)) [Smooth p] (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  let U := X.affineCover.X i
  let q := X.affineCover.f i ≫ p
  have : Smooth q := inferInstance
  let g : CommRingCat.of R ⟶ Γ(U, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ q.appTop
  have hg : g.hom.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective)
    (HasRingHomProperty.appTop @Smooth q inferInstance)
  algebraize [g.hom]
  have : Algebra.Smooth R Γ(U, ⊤) := RingHom.smooth_algebraMap.mp hg
  let P := ((isAffineOpen_top U).primeIdealOf ⟨y, trivial⟩).asIdeal
  have hP : UniqueFactorizationMonoid (Localization.AtPrime P) :=
    Langlands.CommutativeAlgebra.smoothDVRFactorialLocalizations R _ inferInstance P
  let := TopCat.Presheaf.algebra_section_stalk U.presheaf (⟨y, trivial⟩ : (⊤ : U.Opens))
  have := (isAffineOpen_top U).isLocalization_stalk ⟨y, trivial⟩
  have hU : UniqueFactorizationMonoid (U.presheaf.stalk y) :=
    (IsLocalization.algEquiv P.primeCompl (U.presheaf.stalk y)
      (Localization.AtPrime P)).toRingEquiv.toMulEquiv.symm.uniqueFactorizationMonoid hP
  exact (asIso ((X.affineCover.f i).stalkMap y)).commRingCatIsoToRingEquiv.toMulEquiv.symm
    |>.uniqueFactorizationMonoid hU

end Langlands.AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard

/-- The exact canonical self-product map over the fraction field is an open immersion. -/
theorem isOpenImmersion_mumfordProductBaseChangeMap_of_dvr
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (A : AbelianScheme (Spec (CommRingCat.of R))) :
    IsOpenImmersion (mumfordProductBaseChangeMap A
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have : IsOpenImmersion b := isOpenImmersion_spec_fractionRing_of_dvr R K
  rw [← mumfordProductBaseChangeIso_hom_fst A b]
  infer_instance

/-- The actual total self-product is locally Noetherian over a DVR. -/
theorem isLocallyNoetherian_mumfordProduct_of_dvr
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (A : AbelianScheme (Spec (CommRingCat.of R))) :
    IsLocallyNoetherian (mumfordProduct A).left :=
  LocallyOfFiniteType.isLocallyNoetherian (pullback.fst A.X.hom A.X.hom ≫ A.X.hom)

/-- Every stalk on the actual total self-product over a DVR is factorial. -/
theorem factorialStalk_mumfordProduct_of_dvr
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (A : AbelianScheme (Spec (CommRingCat.of R))) (x : (mumfordProduct A).left) :
    UniqueFactorizationMonoid ((mumfordProduct A).left.presheaf.stalk x) :=
  smoothDVR_factorialStalks R _
    (pullback.fst A.X.hom A.X.hom ≫ A.X.hom) x

/-- Every actual line bundle on the generic self-product extends over the DVR. -/
theorem discreteValuationRingSelfProductLineBundleExtension :
    DiscreteValuationRingSelfProductLineBundleExtensionStatement.{u} := by
  intro R _ _ _ K _ _ _ A
  dsimp only
  intro D
  let b := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have : IsOpenImmersion (mumfordProductBaseChangeMap A b) :=
    isOpenImmersion_mumfordProductBaseChangeMap_of_dvr R K A
  have : IsLocallyNoetherian (mumfordProduct A).left :=
    isLocallyNoetherian_mumfordProduct_of_dvr R A
  exact openImmersionLineBundleExtension (mumfordProduct A).left
    (mumfordProduct ((baseChange b).obj A)).left (mumfordProductBaseChangeMap A b)
    (fun x _ => factorialStalk_mumfordProduct_of_dvr R A x) D

end Langlands.AbelianScheme
