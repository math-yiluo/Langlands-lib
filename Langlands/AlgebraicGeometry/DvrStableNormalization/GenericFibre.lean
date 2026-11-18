import Langlands.AlgebraicGeometry.Picard.DiscreteValuationRingSelfProductLineBundleExtensionProof
import Mathlib

/-! # Generic fibres of schemes over a discrete valuation ring -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.DvrStableNormalization

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The global section of `Spec R` corresponding to `r : R`. -/
abbrev sec (r : R) : Γ(Spec (CommRingCat.of R), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv r

instance isOpenImmersion_generic : IsOpenImmersion (Spec.algebraMap R (FractionRing R)) :=
  isOpenImmersion_spec_fractionRing_of_dvr R (FractionRing R)

set_option backward.isDefEq.respectTransparency.types false in
/-- The generic point inclusion of a DVR spectrum is the basic open of a uniformizer. -/
theorem opensRange_generic {ϖ : R} (hϖ : Irreducible ϖ) :
    (Spec.algebraMap R (FractionRing R)).opensRange =
      (Spec (CommRingCat.of R)).basicOpen (sec R ϖ) := by
  have := isLocalizationAway_fractionRing_of_dvr R (FractionRing R) hϖ
  refine Eq.trans ?_ (basicOpen_eq_of_affine (R := CommRingCat.of R) ϖ).symm
  exact TopologicalSpace.Opens.ext
    (PrimeSpectrum.localization_away_comap_range (FractionRing R) ϖ)

variable {R}

/-- The inclusion of the generic fibre of a scheme over `Spec R`. -/
abbrev genericι (Z : Over (Spec (CommRingCat.of R))) :
    pullback Z.hom (Spec.algebraMap R (FractionRing R)) ⟶ Z.left :=
  pullback.fst _ _

/-- The pullback of `r : R` to a global section of a scheme over `Spec R`. -/
abbrev pullSec (Z : Over (Spec (CommRingCat.of R))) (r : R) : Γ(Z.left, ⊤) :=
  Z.hom.appTop (sec R r)

/-- The generic fibre is the basic open of the pulled-back uniformizer. -/
theorem opensRange_genericι (Z : Over (Spec (CommRingCat.of R))) {ϖ : R} (hϖ : Irreducible ϖ) :
    (genericι Z).opensRange = Z.left.basicOpen (pullSec Z ϖ) := by
  rw [Scheme.Hom.opensRange_pullbackFst, opensRange_generic R hϖ, Scheme.preimage_basicOpen_top]

/-- The restriction of the pulled-back section `r` to an open `U`. -/
abbrev resSec (Z : Over (Spec (CommRingCat.of R))) (r : R) (U : Z.left.Opens) : Γ(Z.left, U) :=
  Z.left.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (pullSec Z r)

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Over an affine open `U`, the sections of an open immersion whose image is the basic open
`D(f)` are, over the preimage of `U`, the localization of `Γ(Z, U)` away from `f|_U`. -/
theorem isLocalization_app_of_opensRange_eq {W Z : Scheme.{u}} (j : W ⟶ Z) [IsOpenImmersion j]
    (f : Γ(Z, ⊤)) (hj : j.opensRange = Z.basicOpen f) {U : Z.Opens} (hU : IsAffineOpen U) :
    letI := (j.app U).hom.toAlgebra
    IsLocalization.Away (Z.presheaf.map (homOfLE le_top : U ⟶ ⊤).op f) Γ(W, j ⁻¹ᵁ U) := by
  have hV : j ''ᵁ (j ⁻¹ᵁ U) = Z.basicOpen (Z.presheaf.map (homOfLE le_top : U ⟶ ⊤).op f) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, hj, Scheme.basicOpen_res, inf_comm]
  have hle : j ''ᵁ (j ⁻¹ᵁ U) ≤ U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact inf_le_right
  let := (Z.presheaf.map (homOfLE hle).op).hom.toAlgebra
  have h1 : IsLocalization.Away (Z.presheaf.map (homOfLE le_top : U ⟶ ⊤).op f)
      Γ(Z, j ''ᵁ (j ⁻¹ᵁ U)) :=
    hU.isLocalization_of_eq_basicOpen _ (homOfLE hle) hV
  let := (j.app U).hom.toAlgebra
  have hcomm : Z.presheaf.map (homOfLE hle).op ≫ (j.appIso (j ⁻¹ᵁ U)).hom = j.app U := by
    rw [← cancel_mono (j.appIso (j ⁻¹ᵁ U)).inv, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Scheme.Hom.app_appIso_inv]
    rfl
  let e : Γ(Z, j ''ᵁ (j ⁻¹ᵁ U)) ≃ₐ[Γ(Z, U)] Γ(W, j ⁻¹ᵁ U) :=
    { (j.appIso (j ⁻¹ᵁ U)).commRingCatIsoToRingEquiv with
      commutes' := fun r => by
        change (Z.presheaf.map (homOfLE hle).op ≫ (j.appIso (j ⁻¹ᵁ U)).hom) r = _
        rw [hcomm]; rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e

/-- Over an affine open `U`, the sections of the generic fibre over the preimage of `U` are the
localization of `Γ(Z, U)` away from the uniformizer. -/
theorem isLocalization_genericι_app (Z : Over (Spec (CommRingCat.of R))) {ϖ : R}
    (hϖ : Irreducible ϖ) {U : Z.left.Opens} (hU : IsAffineOpen U) :
    letI := ((genericι Z).app U).hom.toAlgebra
    IsLocalization.Away (resSec Z ϖ U)
      Γ(pullback Z.hom (Spec.algebraMap R (FractionRing R)), (genericι Z) ⁻¹ᵁ U) :=
  isLocalization_app_of_opensRange_eq (genericι Z) (pullSec Z ϖ) (opensRange_genericι Z hϖ) hU

omit [IsDiscreteValuationRing R] in
/-- For a flat scheme over `Spec R`, a uniformizer restricts to a non-zero-divisor on every
affine open. -/
theorem resSec_mem_nonZeroDivisors (Z : Over (Spec (CommRingCat.of R))) [Flat Z.hom]
    {ϖ : R} (hϖ : Irreducible ϖ) {U : Z.left.Opens} (hU : IsAffineOpen U) :
    resSec Z ϖ U ∈ nonZeroDivisors Γ(Z.left, U) := by
  have hflat : (Z.hom.appLE ⊤ U le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat Z.hom ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  let φ : R →+* Γ(Z.left, U) :=
    (Z.hom.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hφ : φ = (Z.hom.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    rfl
  have hφflat : φ.Flat := by
    refine RingHom.Flat.comp ?_ hflat
    exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  let := φ.toAlgebra
  have : Module.Flat R Γ(Z.left, U) := hφflat
  have hreg : IsSMulRegular Γ(Z.left, U) ϖ :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)
  have hres : resSec Z ϖ U = algebraMap R Γ(Z.left, U) ϖ := by
    change Z.left.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (Z.hom.appTop (sec R ϖ)) = φ ϖ
    rfl
  rw [hres, mem_nonZeroDivisors_iff_right]
  intro x hx
  apply hreg
  simp only [Algebra.smul_def, mul_zero]
  rw [mul_comm]; exact hx

end Langlands.AlgebraicGeometry.DvrStableNormalization
