import Langlands.Automorphic.CuspidalHilbertOrbitCoefficientProof
import Langlands.Global.ArchimedeanCompactLieOrbitDensityProof
import Langlands.Global.RankinSelberg.ArchimedeanWhittakerRegularity
import Langlands.Global.RankinSelberg.RealPlaceWhittakerCovariance
import Langlands.Global.RankinSelberg.SelfPairPositiveData

/-! # Nonvanishing of the cuspidal Whittaker functional at the identity -/

noncomputable section

universe u

open NumberField
open scoped Classical CategoryTheory.MonObj ContDiff Manifold Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.Global.RankinSelbergGlobal

open Automorphic ArchimedeanGL ArchimedeanWhittakerRegularity
open CuspidalHilbertOrbitCoefficient (exists_center_ideal)
open CuspidalHilbertOrbitCoefficientProof
  (envelopingAction_generator_mul smoothEnvelopingAction_generator_apply)

variable {F : Type u} [Field F] [NumberField F] {r : ℕ}

local instance identitySchemeAffine (n : ℕ) : AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance identitySchemeSmooth (n : ℕ) : AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
local instance identityRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance identityContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance identityFiniteSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance identityAutomorphicGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance identityStableGroup (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance identityRealizationGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace WhittakerIdentity

local notation "n" => r + 1

private def infinitePoint (g : InfiniteAdelicGL F n) : Points F n :=
  adelicPoint F n (archimedeanGLCoordinates F n g) 1

private theorem infinitePoint_eq (g : InfiniteAdelicGL F n) :
    infinitePoint g =
      (GeneralLinearGroupPoints.adelicEquiv F n).symm (AdelicGL.ofInfinite F n g) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  rw [infinitePoint, adelicEquiv_adelicPoint, ContinuousMulEquiv.symm_apply_apply,
    MulEquiv.apply_symm_apply]
  apply AdelicGL.ext_infinite_finite F n <;> simp

private theorem infinitePoint_one : infinitePoint (1 : InfiniteAdelicGL F n) = (1 : Points F n) := by
  rw [infinitePoint_eq, map_one, map_one]

private theorem infinitePoint_mul (g h : InfiniteAdelicGL F n) :
    infinitePoint (g * h) = infinitePoint g * infinitePoint h := by
  simp only [infinitePoint_eq, map_mul]

variable [CompactSpace (AdeleQuotient F)]
  (T : CuspidalOperatorRealization F r) (ψ : AddChar (Adeles F) ℂ)
  (hψ : IsStandardAdditiveCharacter F ψ)

private def coefficientMap : T.Space →ₗ[ℂ] SmoothFunctions F n where
  toFun x := ⟨fun g => cuspWhittaker F T ψ x (infinitePoint g), by
    change ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, ℂ) ∞ _
    intro v
    have hv : ContDiffAt ℝ ∞ (archWhittakerExt T ψ x 1) (v : ArchimedeanMatrix F n) :=
      (contDiffOn_archWhittakerExt T ψ hψ x 1).contDiffAt
        (by
          change {M : ArchimedeanMatrix F n | IsUnit M} ∈ 𝓝 (v : ArchimedeanMatrix F n)
          exact CuspidalHilbertOrbitCoefficientProof.isOpen_unitSet.mem_nhds
            ⟨v, rfl⟩)
    have hval : ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, ArchimedeanMatrix F n) ∞
        (Units.val : ArchimedeanGL F n → ArchimedeanMatrix F n) := Units.contMDiff_val
    have hc := hv.comp_contMDiffAt (hval v)
    simpa only [Function.comp_def, archWhittakerExt_units T ψ hψ,
      infinitePoint, ContinuousMulEquiv.apply_symm_apply, cuspWhittaker,
      Unfolding.whittaker] using hc⟩
  map_add' x y := Subtype.ext (funext fun g =>
    UnramifiedWhittaker.cuspWhittaker_add F ψ hψ T x y (infinitePoint g))
  map_smul' c x := Subtype.ext (funext fun g =>
    UnramifiedWhittaker.cuspWhittaker_smul F ψ T c x (infinitePoint g))

private theorem coefficientMap_lieOperator (X : RealLieAlgebra F n) (x : T.Space) :
    coefficientMap T ψ hψ (T.realization.lieOperator X x) =
      smoothDifferential F n X (coefficientMap T ψ hψ x) := by
  apply Subtype.ext
  funext g
  have hExt (v : ArchimedeanGL F n) :
      archWhittakerExt T ψ x 1 (v : ArchimedeanMatrix F n) =
        (coefficientMap T ψ hψ x).val ((archimedeanGLCoordinates F n).symm v) := by
    change archWhittakerExt T ψ x 1 (v : ArchimedeanMatrix F n) =
      cuspWhittaker F T ψ x (infinitePoint ((archimedeanGLCoordinates F n).symm v))
    rw [infinitePoint, ContinuousMulEquiv.apply_symm_apply, archWhittakerExt_units T ψ hψ]
    rfl
  change cuspWhittaker F T ψ (T.realization.lieOperator X x) (infinitePoint g) = _
  rw [smoothDifferential_eq_of_extension F n X _ _ hExt g,
    fderiv_archWhittakerExt_mul T ψ hψ, archWhittakerExt_units T ψ hψ]
  unfold infinitePoint lieDeriv Unfolding.matrixGenerator
  rw [LinearEquiv.symm_apply_apply]
  rfl

private theorem coefficientMap_envelopingAction (a : EnvelopingAlgebra F n) (x : T.Space) :
    coefficientMap T ψ hψ (T.realization.envelopingAction a x) =
      ArchimedeanGL.envelopingAction F n a (coefficientMap T ψ hψ x) := by
  induction a using enveloping_real_left_induction generalizing x with
  | h1 => simp only [map_one, Module.End.one_apply]
  | hadd a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | hsmul c a ha => simp only [map_smul, LinearMap.smul_apply, ha]
  | hgen X a ha =>
    rw [envelopingAction_generator_mul, coefficientMap_lieOperator, ha,
      envelopingAction_mul, smoothEnvelopingAction_generator_apply]

private theorem coefficientMap_compact (k : standardInfiniteCompact F n) (x : T.Space) :
    coefficientMap T ψ hψ (T.realization.compactRepresentation k x) =
      ArchimedeanGL.smoothRightAction F n k.val (coefficientMap T ψ hψ x) := by
  apply Subtype.ext
  funext g
  change cuspWhittaker F T ψ (T.realization.compactRepresentation k x) (infinitePoint g) =
    cuspWhittaker F T ψ x (infinitePoint (g * k.val))
  rw [RealPlaceWhittaker.cuspWhittaker_compact, infinitePoint_mul, infinitePoint_eq k.val]

private theorem coefficientMap_jointFinite (x : T.Space) :
    IsJointFinite F n (coefficientMap T ψ hψ x) := by
  let C := coefficientMap T ψ hψ
  apply separateJointFinite F n (C x)
  · obtain ⟨I, hI, hz⟩ := exists_center_ideal T.realization x
    change Module.Finite ℂ (centerOrbitSpan F n (C x))
    rw [centerOrbitSpan_eq_range]
    let := hI
    have hle : I.restrictScalars ℂ ≤ LinearMap.ker (centerOrbitMap F n (C x)) := by
      intro z hzI
      rw [LinearMap.mem_ker, centerOrbitMap_apply, centerAction_apply]
      change envelopingAction F n _ (coefficientMap T ψ hψ x) = 0
      rw [← coefficientMap_envelopingAction, hz z hzI, map_zero]
    have : Module.Finite ℂ (EnvelopingCenter F n ⧸ LinearMap.ker (centerOrbitMap F n (C x))) :=
      Module.Finite.of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
    exact Module.Finite.equiv (centerOrbitMap F n (C x)).quotKerEquivRange
  · apply compactGroupFiniteDifferential
    let Φ : T.realization.compactRepresentation.IntertwiningMap
        ((ArchimedeanGL.smoothRightAction F n).comp (standardInfiniteCompact F n).subtype) :=
      { toLinearMap := C
        isIntertwining' := fun k => LinearMap.ext fun x => coefficientMap_compact T ψ hψ k x }
    exact (T.realization.compactRepresentation_isFiniteVector x).map Φ

include hψ in
private theorem coefficientMap_eq_zero_of_identity
    (hzero : ∀ x : T.Space, cuspWhittaker F T ψ x 1 = 0)
    (x : T.Space) (g : InfiniteAdelicGL F n) :
    cuspWhittaker F T ψ x (infinitePoint g) = 0 := by
  let C := coefficientMap T ψ hψ
  obtain ⟨k, hgk⟩ := compactComponentCoverage F n g
  have hjet (a : EnvelopingAlgebra F n) : (envelopingAction F n a (C x)).val k.val = 0 := by
    rw [show envelopingAction F n a (C x) = C (T.realization.envelopingAction a x) from
      (coefficientMap_envelopingAction T ψ hψ a x).symm]
    let y := T.realization.envelopingAction a x
    have hk := congrArg (fun s : SmoothFunctions F n => s.val 1)
      (coefficientMap_compact T ψ hψ k y)
    change cuspWhittaker F T ψ (T.realization.compactRepresentation k y) (infinitePoint 1) =
      cuspWhittaker F T ψ y (infinitePoint (1 * k.val)) at hk
    rw [infinitePoint_one, one_mul, hzero] at hk
    exact hk.symm
  exact analyticMatrixJetUniqueness F n (C x) k.val
    (jointFiniteAnalyticity F n (C x) (coefficientMap_jointFinite T ψ hψ x))
    (envelopingZeroJet F n (C x) k.val hjet) g hgk

end WhittakerIdentity

/-- A standard Whittaker functional on an actual cuspidal realization is nonzero
at the adelic identity on some realized vector. -/
def CuspidalWhittakerIdentityNonzeroStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    ∃ x : T.Space, cuspWhittaker F T ψ x 1 ≠ 0

theorem cuspidalWhittakerIdentityNonzero : CuspidalWhittakerIdentityNonzeroStatement.{u} := by
  intro F _ _ _ r T ψ hψ
  by_contra! hzero
  obtain ⟨x, hx⟩ := exists_ne (0 : T.Space)
  obtain ⟨g, hg⟩ := SelfPair.exists_cuspWhittaker_ne_zero T ψ hψ hx
  let a := AdelicGL.infinite F (r + 1) (GeneralLinearGroupPoints.adelicEquiv F (r + 1) g)
  let b := AdelicGL.finite F (r + 1) (GeneralLinearGroupPoints.adelicEquiv F (r + 1) g)
  have hab : WhittakerIdentity.infinitePoint a *
      (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
        (AdelicGL.ofFinite F (r + 1) b) = g := by
    rw [WhittakerIdentity.infinitePoint_eq]
    apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    rw [← OperatorRealization.pair_eq_ofInfinite_mul_ofFinite]
    exact AdelicGL.pair_projections F (r + 1) _
  have hz := WhittakerIdentity.coefficientMap_eq_zero_of_identity T ψ hψ hzero
    (T.realization.finiteRepresentation b x) a
  rw [UnramifiedWhittaker.cuspWhittaker_finiteRepresentation, hab] at hz
  exact hg hz

end Langlands.Global.RankinSelbergGlobal
