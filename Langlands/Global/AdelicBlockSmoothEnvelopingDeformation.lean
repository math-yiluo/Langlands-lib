import Langlands.Global.AdelicBlockEisensteinSmoothHeight
import Langlands.Global.AdelicBlockHeightMultiplier
import Langlands.Global.AdelicBlockScalarEnvelopingAction
import Langlands.Global.AdelicBlockSmoothFiniteDeformation

/-! # Deformed invariant differentiation on smooth block-induced sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions Langlands.GeneralLinear
open Langlands.Geometry.Manifold ArchimedeanGL EisensteinJet
open AdelicGroupPoints InfiniteAdelicGroupPoints GeneralLinearGroupPoints
open AdelicBlockEisensteinGeometry

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local notation "P" =>
  GroupScheme.GeneralLinear.blockParabolicScheme (Fin n) (CommRingCat.of F)
    (GroupScheme.GeneralLinear.blockShapeWeight B)
local notation "V" => FiniteSmoothRealizedSections F B S
local notation "A" => CompactFiniteRealizedSections F B S
local notation "W" => smoothCompactFiniteSections F B S
local notation "hK" => isIwasawaCompact_blockParabolic F B
local notation "Param" => ComplexCharacterParameter F P
local notation "j" => smoothSectionOnScheme F B S
local notation "inc" => smoothSectionInclusion F B S

local instance blockSmoothEnvGLAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance blockSmoothEnvVAGroup : AddCommGroup V := Submodule.addCommGroup _
local instance blockSmoothEnvAAGroup : AddCommGroup A := Submodule.addCommGroup _
local instance blockSmoothEnvWAGroup : AddCommGroup W := Submodule.addCommGroup _

variable {d : ℕ}

local notation "I" => 𝓘(ℝ, smoothModel F d)
local notation "hH[" h "]" => hasSmoothHeightPairings_blockParabolic F B h
local notation "Y[" h "," X "]" => LinearEquiv.symm (infiniteRealLieAlgebraEquiv F n h) X

private theorem parameterTwist_zero (φ : AdelicGroupPoints F GLG → ℂ) :
    (hK).parameterTwist φ 0 = φ := by
  funext g
  change φ g * Complex.exp (complexParameterPairing F P 0 ((hK).height g)) = φ g
  simp

private theorem sectionDifferential_onScheme
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (X : RealLieAlgebra F n) (f : W) :
    j (sectionDifferential F B S X f) =
      (hK).parameterDirectionalSection hsmooth 0 Y[hsmooth, X] (j f) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  funext g
  let a := infinite F GLG g
  let b := finite F GLG g
  have hg : pair F GLG a b = g := pair_projections F GLG g
  rw [← hg]
  have hh := (hK).parameterTwist_directionalSection hsmooth 0 Y[hsmooth, X] (j f) a b
  rw [parameterTwist_zero, parameterTwist_zero] at hh
  rw [hh]
  have h := infinite_groupDirectionalValue F n hsmooth Y[hsmooth, X]
    (smoothScalarSlice F B S (finiteHomeomorph F n b) f) a
  rw [LinearEquiv.apply_symm_apply, ← smoothScalarSlice_sectionDifferential] at h
  simpa only [← smoothSectionOnScheme_pair] using h.symm

private def smoothHeightMultiplier
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (lam : Param) (Y : smoothModel F d) : Module.End ℂ W :=
  ((A).subtype.comp ((heightSectionMultiplier F B S hsmooth hH[hsmooth] lam Y).comp inc)).codRestrict W
    fun f => by
      let g := heightSectionMultiplier F B S hsmooth hH[hsmooth] lam Y (inc f)
      change g.val ∈ W
      apply (mem_smoothCompactFiniteSections_iff_schemeSlices F B S hsmooth g).mpr
      intro b
      exact contMDiff_heightSectionMultiplier_pair F B S hsmooth hH[hsmooth] lam Y (inc f) b
        (smoothSectionOnScheme_hasSmoothSlices F B S hsmooth f b)

private theorem smoothHeightMultiplier_onScheme
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (lam : Param) (Y : smoothModel F d) (f : W) :
    j (smoothHeightMultiplier F B S hsmooth lam Y f) =
      j f * (hK).heightPairingDirectional hsmooth hH[hsmooth] Y lam :=
  compactFiniteSectionOnScheme_heightSectionMultiplier F B S hsmooth hH[hsmooth] lam Y (inc f)

/-- The deformed differential on the original smooth section carrier is the
ordinary normalized differential plus multiplication by the height derivative. -/
def deformedSmoothSectionDifferential
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (lam : Param) (X : RealLieAlgebra F n) : Module.End ℂ W :=
  sectionDifferential F B S X + smoothHeightMultiplier F B S hsmooth lam Y[hsmooth, X]

theorem deformedSmoothSectionDifferential_onScheme
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) (lam : Param) :
    HasDeformedRealSectionOperators F n hsmooth (hK) lam j
      (deformedSmoothSectionDifferential F B S hsmooth lam) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  intro X f
  rw [deformedSmoothSectionDifferential, LinearMap.add_apply, map_add,
    sectionDifferential_onScheme, smoothHeightMultiplier_onScheme]
  exact ((hK).parameterDirectionalSection_eq_add hsmooth hH[hsmooth] Y[hsmooth, X] (j f)
    (smoothSectionOnScheme_hasSmoothSlices F B S hsmooth f) lam).symm

@[simp]
theorem deformedSmoothSectionDifferential_zero
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) (X : RealLieAlgebra F n) :
    deformedSmoothSectionDifferential F B S hsmooth 0 X = sectionDifferential F B S X := by
  apply LinearMap.ext
  intro f
  apply smoothSectionOnScheme_injective F B S
  exact (deformedSmoothSectionDifferential_onScheme F B S hsmooth 0 X f).trans
    (sectionDifferential_onScheme F B S hsmooth X f).symm

/-- The matrix enveloping algebra action on the smooth carrier at every
complex parameter. -/
def deformedSmoothSectionEnvelopingAction
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (hcalc : AdelicDifferentialCommutator F GLG hsmooth) (lam : Param) :
    EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ W :=
  deformedSectionEnvelopingAction F n hsmooth (hK) hH[hsmooth] lam j
    (smoothSectionOnScheme_hasSmoothSlices F B S hsmooth) (smoothSectionOnScheme_injective F B S)
    (deformedSmoothSectionDifferential F B S hsmooth lam)
    (deformedSmoothSectionDifferential_onScheme F B S hsmooth lam) hcalc

theorem deformedSmoothSectionEnvelopingAction_real_generator
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (hcalc : AdelicDifferentialCommutator F GLG hsmooth) (lam : Param) (X : RealLieAlgebra F n) :
    deformedSmoothSectionEnvelopingAction F B S hsmooth hcalc lam
      (envelopingGenerator F n (complexify F n X)) =
    deformedSmoothSectionDifferential F B S hsmooth lam X :=
  deformedSectionEnvelopingAction_real_generator F n hsmooth (hK) hH[hsmooth] lam j
    (smoothSectionOnScheme_hasSmoothSlices F B S hsmooth) (smoothSectionOnScheme_injective F B S)
    (deformedSmoothSectionDifferential F B S hsmooth lam)
    (deformedSmoothSectionDifferential_onScheme F B S hsmooth lam) hcalc X

@[simp]
theorem deformedSmoothSectionEnvelopingAction_zero
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (hcalc : AdelicDifferentialCommutator F GLG hsmooth) :
    deformedSmoothSectionEnvelopingAction F B S hsmooth hcalc 0 = sectionEnvelopingAction F B S := by
  apply AlgHom.ext
  intro a
  induction a using enveloping_real_left_induction F n with
  | h1 => simp only [map_one]
  | hadd a b ha hb => simp only [map_add, ha, hb]
  | hsmul z a ha => simp only [map_smul, ha]
  | hgen X a ha =>
    rw [map_mul, map_mul, ha, deformedSmoothSectionEnvelopingAction_real_generator,
      deformedSmoothSectionDifferential_zero, sectionEnvelopingAction_real_generator]

theorem deformedSmoothSectionEnvelopingAction_real_generator_onScheme
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) (hcalc : AdelicDifferentialCommutator F GLG hsmooth)
    (lam : Param) (X : RealLieAlgebra F n) (f : W) :
    j (deformedSmoothSectionEnvelopingAction F B S hsmooth hcalc lam
        (envelopingGenerator F n (complexify F n X)) f) =
      (hK).parameterDirectionalSection hsmooth lam Y[hsmooth, X] (j f) := by
  rw [deformedSmoothSectionEnvelopingAction_real_generator]
  exact deformedSmoothSectionDifferential_onScheme F B S hsmooth lam X f

/-- Every real generator has a finite holomorphic expansion on the deformed carrier. -/
theorem deformedSmoothSectionEnvelopingAction_real_generator_mem_finiteHolomorphicSections
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) (hcalc : AdelicDifferentialCommutator F GLG hsmooth)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (e : E →ₗ[ℂ] Param) (X : RealLieAlgebra F n) (f : W) :
    (fun t => deformedSmoothSectionEnvelopingAction F B S hsmooth hcalc (e t)
      (envelopingGenerator F n (complexify F n X)) f) ∈ finiteHolomorphicSections E W := by
  apply FiniteHolomorphicSections.mem_of_injective j (smoothSectionOnScheme_injective F B S)
  simp only [deformedSmoothSectionEnvelopingAction_real_generator_onScheme]
  exact (hK).parameterDirectionalSection_mem_finiteHolomorphicSections hsmooth e hH[hsmooth] Y[hsmooth, X] (j f)
    (smoothSectionOnScheme_hasSmoothSlices F B S hsmooth f)

end Langlands.Global.AdelicBlockScalarSections
