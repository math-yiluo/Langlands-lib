import Langlands.Global.AdelicBlockFiniteSectionDeformation
import Langlands.Global.AdelicBlockScalarLieAction
import Langlands.Global.AdelicEisensteinDeformedEnveloping

/-! # Finite deformation on smooth block-induced sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Classical Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1250000

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.GeneralLinear
open AdelicGroupPoints InfiniteAdelicGroupPoints GeneralLinearGroupPoints
open AdelicBlockEisensteinGeometry PrimitiveAdelicHeight EisensteinJet

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
local notation "e∞" => infiniteHomeomorph F n
local notation "ef" => finiteHomeomorph F n
local notation "eG" => adelicHomeomorph F n
local notation "Std" => FiniteAdelicGL.standardIntegral F n
local notation "Param" => ComplexCharacterParameter F P

local instance blockSmoothFiniteGLAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance blockSmoothFiniteVAGroup : AddCommGroup V := Submodule.addCommGroup _
local instance blockSmoothFiniteAAGroup : AddCommGroup A := Submodule.addCommGroup _
local instance blockSmoothFiniteWAGroup : AddCommGroup W := Submodule.addCommGroup _

/-- The smooth compact-finite section space is included in the full
compact-finite section space on the same matrix model. -/
def smoothSectionInclusion : W →ₗ[ℂ] A :=
  Submodule.inclusion (show W ≤ A from inf_le_left)

theorem smoothSectionInclusion_injective : Function.Injective (smoothSectionInclusion F B S) :=
  Submodule.inclusion_injective _

/-- Scalar evaluation on the actual scheme adeles. -/
def smoothSectionOnScheme : W →ₗ[ℂ] (AdelicGroupPoints F GLG → ℂ) :=
  (compactFiniteSectionOnScheme F B S).comp (smoothSectionInclusion F B S)

theorem smoothSectionOnScheme_injective : Function.Injective (smoothSectionOnScheme F B S) :=
  (compactFiniteSectionOnScheme_injective F B S).comp (smoothSectionInclusion_injective F B S)

theorem compactFiniteSectionOnScheme_pair (f : A) (a : InfiniteAdelicGroupPoints F GLG)
    (b : FiniteAdelicGroupPoints F GLG) :
    compactFiniteSectionOnScheme F B S f (pair F GLG a b) =
      scalarSlice F B S (ef b) f.val (e∞ a) := by
  change f.val.val.val (eG (pair F GLG a b)) = _
  rw [adelicHomeomorph_pair]
  rfl

theorem smoothSectionOnScheme_pair (f : W) (a : InfiniteAdelicGroupPoints F GLG)
    (b : FiniteAdelicGroupPoints F GLG) :
    smoothSectionOnScheme F B S f (pair F GLG a b) =
      (smoothScalarSlice F B S (ef b) f).val (e∞ a) :=
  compactFiniteSectionOnScheme_pair F B S (smoothSectionInclusion F B S f) a b

/-- Smoothness in the scheme atlas is the existing all-slice condition on
the scalar matrices. -/
theorem mem_smoothCompactFiniteSections_iff_schemeSlices {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) (f : A) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F GLG hsmooth
    f.val ∈ W ↔ ∀ b : FiniteAdelicGroupPoints F GLG,
      ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞
        (fun a => compactFiniteSectionOnScheme F B S f (pair F GLG a b)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  have he (b : FiniteAdelicGroupPoints F GLG) := contMDiff_iff_mem_smoothFunctions F n hsmooth
    (fun a => compactFiniteSectionOnScheme F B S f (pair F GLG a b))
  rw [mem_smoothCompactFiniteSections]
  constructor
  · intro h b
    apply (he b).mpr
    simpa only [compactFiniteSectionOnScheme_pair, ContinuousMulEquiv.apply_symm_apply] using h.2 (ef b)
  · intro h
    refine ⟨f.property, fun b => ?_⟩
    have hb := (he ((ef).symm b)).mp (h ((ef).symm b))
    simpa only [compactFiniteSectionOnScheme_pair, ContinuousMulEquiv.apply_symm_apply] using hb

theorem smoothSectionOnScheme_hasSmoothSlices {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
    HasSmoothSectionSlices hsmooth (smoothSectionOnScheme F B S) :=
  fun f => (mem_smoothCompactFiniteSections_iff_schemeSlices F B S hsmooth
    (smoothSectionInclusion F B S f)).mp f.property

private def deformedFiniteOnSmooth (lam : Param) (g : FiniteAdelicGL F n) : Module.End ℂ W :=
  ((A).subtype.comp ((deformedCompactFiniteAction F B S lam g).comp
    (smoothSectionInclusion F B S))).codRestrict W fun f => by
      let x := deformedCompactFiniteAction F B S lam g (smoothSectionInclusion F B S f)
      change x.val ∈ W
      rw [mem_smoothCompactFiniteSections]
      refine ⟨x.property, fun b => ?_⟩
      let c := (hK).finiteTranslationFactor lam ((ef).symm g) ((ef).symm b)
      have h : scalarSlice F B S b x.val = c • scalarSlice F B S (b * g) f.val := by
        funext a
        change x.val.val.val (AdelicGL.pair F n a b) = c * f.val.val.val (AdelicGL.pair F n a (b * g))
        rw [deformedCompactFiniteAction_matrix_pair]
        exact mul_comm _ _
      rw [h]
      exact Submodule.smul_mem _ c ((mem_smoothCompactFiniteSections F B S f.val).mp f.property |>.2 (b * g))

/-- The deformed finite adelic action on the smooth compact-finite carrier. -/
def deformedSmoothFiniteAction (lam : Param) : Representation ℂ (FiniteAdelicGL F n) W where
  toFun := deformedFiniteOnSmooth F B S lam
  map_one' := by
    ext f : 1
    apply smoothSectionInclusion_injective F B S
    change deformedCompactFiniteAction F B S lam 1 (smoothSectionInclusion F B S f) =
      smoothSectionInclusion F B S f
    rw [map_one, Module.End.one_apply]
  map_mul' g h := by
    ext f : 1
    apply smoothSectionInclusion_injective F B S
    change deformedCompactFiniteAction F B S lam (g * h) (smoothSectionInclusion F B S f) =
      deformedCompactFiniteAction F B S lam g
        (deformedCompactFiniteAction F B S lam h (smoothSectionInclusion F B S f))
    rw [map_mul, Module.End.mul_apply]

theorem smoothSectionInclusion_deformedSmoothFiniteAction (lam : Param)
    (g : FiniteAdelicGL F n) (f : W) :
    smoothSectionInclusion F B S (deformedSmoothFiniteAction F B S lam g f) =
      deformedCompactFiniteAction F B S lam g (smoothSectionInclusion F B S f) := rfl

theorem deformedSmoothFiniteAction_of_mem_standardIntegral (lam : Param)
    (g : FiniteAdelicGL F n) (hg : g ∈ Std) :
    deformedSmoothFiniteAction F B S lam g = smoothCompactFiniteAction F B S g := by
  apply LinearMap.ext
  intro f
  apply (smoothSectionInclusion_injective F B S)
  rw [smoothSectionInclusion_deformedSmoothFiniteAction, deformedCompactFiniteAction_of_mem_standardIntegral _ _ _ _ _ hg]
  rfl

@[simp]
theorem deformedSmoothFiniteAction_zero (g : FiniteAdelicGL F n) :
    deformedSmoothFiniteAction F B S 0 g = smoothCompactFiniteAction F B S g := by
  apply LinearMap.ext
  intro f
  apply (smoothSectionInclusion_injective F B S)
  rw [smoothSectionInclusion_deformedSmoothFiniteAction, deformedCompactFiniteAction_zero]
  rfl

theorem smoothSectionOnScheme_deformedFiniteAction (lam : Param) (g : FiniteAdelicGL F n) (f : W) :
    smoothSectionOnScheme F B S (deformedSmoothFiniteAction F B S lam g f) =
      (hK).parameterRightAction lam (ofFinite F GLG ((ef).symm g)) (smoothSectionOnScheme F B S f) :=
  compactFiniteSectionOnScheme_deformedFiniteAction F B S lam g (smoothSectionInclusion F B S f)

theorem smoothSectionOnScheme_compactAction (k : standardInfiniteCompact F n) (f : W) :
    smoothSectionOnScheme F B S (smoothCompactAction F B S k f) = fun g =>
      smoothSectionOnScheme F B S f (g * ofInfinite F GLG ((e∞).symm k.val)) := by
  funext g
  change f.val.val.val (eG g * AdelicGL.ofInfinite F n k.val) =
    f.val.val.val (eG (g * ofInfinite F GLG ((e∞).symm k.val)))
  rw [map_mul, adelicHomeomorph_ofInfinite, ContinuousMulEquiv.apply_symm_apply]

theorem deformedSmoothFiniteAction_mem_finiteHolomorphicSections
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (e : E →ₗ[ℂ] Param) (g : FiniteAdelicGL F n) (f : W) :
    (fun t => deformedSmoothFiniteAction F B S (e t) g f) ∈ finiteHolomorphicSections E W := by
  apply FiniteHolomorphicSections.mem_of_injective (smoothSectionInclusion F B S)
    (smoothSectionInclusion_injective F B S)
  exact deformedCompactFiniteAction_mem_finiteHolomorphicSections F B S e g (smoothSectionInclusion F B S f)

end Langlands.Global.AdelicBlockScalarSections
