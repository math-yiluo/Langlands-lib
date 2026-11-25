import Langlands.Automorphic.JointAdmissibilityCenter
import Langlands.Global.ArchimedeanCenterConjugationKernel
import Langlands.Global.AdelicBlockJointAdmissibility
import Langlands.Global.AdelicBlockScalarEnvelopingAction
import Langlands.Global.AdelicBlockSmoothSectionGrowth

/-! # Automorphic functions on the actual block-parabolic quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.GeneralLinear
open AdelicBlockEisensteinGeometry ArchimedeanGL
open AdelicGroupPoints GeneralLinearGroupPoints InfiniteAdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local notation "std" => GroupScheme.MatrixRepresentation.standard (Fin n) (CommRingCat.of F)
local notation "V" => FiniteSmoothRealizedSections F B S
local notation "A" => CompactFiniteRealizedSections F B S
local notation "W" => smoothCompactFiniteSections F B S
local notation "R" => smoothCompactFiniteAction F B S
local notation "C" => smoothCompactAction F B S
local notation "K" => standardInfiniteCompact F n
local notation "Z" => EnvelopingCenter F n
local notation "j" => smoothSectionOnScheme F B S
local notation "e∞" => infiniteHomeomorph F n

local instance blockAutomorphicGLAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance blockAutomorphicSmoothAddGroup : AddCommGroup V := Submodule.addCommGroup _
local instance blockAutomorphicCompactAddGroup : AddCommGroup A := Submodule.addCommGroup _
local instance blockAutomorphicSectionAddGroup : AddCommGroup W := Submodule.addCommGroup _

/-- Taking smooth infinite slices preserves joint admissibility for the
original finite and compact actions. -/
theorem smoothCompactFiniteSections_isJointlyAdmissible
    (hS : ∀ i, (S i).IsJointlyAdmissible) : Langlands.IsJointlyAdmissible R C :=
  (compactFiniteRealizedSections_isJointlyAdmissible F B S hS).of_injective
    (smoothSectionInclusion F B S) (smoothSectionInclusion_injective F B S)
    (fun _ _ => rfl) (fun _ _ => rfl)

private theorem smoothCompactAction_isFiniteVector (f : W) :
    FiniteVectors.IsFiniteVector C f := by
  let i : Representation.IntertwiningMap C (finiteSmoothCompactAction F B S) :=
    { toLinearMap := (W).subtype
      isIntertwining' _ := rfl }
  exact (FiniteVectors.isFiniteVector_map_iff i Subtype.val_injective f).mp
    ((mem_smoothCompactFiniteSections F B S f.val).mp f.property).1

/-- The actual matrix center action on smooth block-induced sections. -/
def sectionCenterAction : Z →ₐ[ℂ] Module.End ℂ W :=
  (sectionEnvelopingAction F B S).comp (centerInclusion F n)

private theorem finite_centerConjugationImage :
    Finite ((centerConjugationHom F n).comp (standardInfiniteCompact F n).subtype).range := by
  let a := (centerConjugationHom F n).comp (standardInfiniteCompact F n).subtype
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_standardInfiniteCompact F n)
  have h : IsOpen (a.ker : Set K) :=
    (isOpen_ker_centerConjugationHom F n).preimage continuous_subtype_val
  let : Finite (K ⧸ a.ker) := Subgroup.quotient_finite_of_isOpen a.ker h
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange a).toEquiv

private theorem finiteDimensional_sectionCenterOrbit
    (hJ : Langlands.IsJointlyAdmissible R C) (f : W) :
    FiniteDimensional ℂ (LinearMap.range (centralOrbitMap (sectionCenterAction F B S) f)) := by
  let a := (centerConjugationHom F n).comp (standardInfiniteCompact F n).subtype
  let : Finite a.range := finite_centerConjugationImage (n := n) F
  obtain ⟨L, hL⟩ := f.val.property
  refine finiteDimensional_range_centralOrbitMap R C (sectionCenterAction F B S) a hJ
    ?_ ?_ ?_ f (smoothCompactAction_isFiniteVector F B S f) L ?_
  · intro g k v
    exact Subtype.ext (Subtype.ext
      (RealizedSections.finiteAction_infiniteCompactAction F B S g k v.val.val))
  · intro g z v
    exact smoothCompactFiniteAction_sectionEnvelopingAction F B S g (centerInclusion F n z) v
  · intro k z v
    change C k (sectionEnvelopingAction F B S (centerInclusion F n z) v) =
      sectionEnvelopingAction F B S (centerInclusion F n (centerConjugation F n k.val z)) (C k v)
    rw [centerInclusion_centerConjugation]
    exact smoothCompactAction_sectionEnvelopingAction F B S k (centerInclusion F n z) v
  · intro l
    exact Subtype.ext (Subtype.ext (hL l))

namespace SchemeSection

open Langlands.Automorphic.GroupSchemeFunctions

/-- Matrix compact finiteness is exactly what is needed for the same
standard compact on the actual scheme points. -/
theorem isInfiniteSubgroupFiniteFunction (f : W) :
    IsInfiniteSubgroupFiniteFunction F GLG (generalLinearStandardInfiniteCompact F n) (j f) := by
  let U := FiniteVectors.orbitSpan C f
  let : FiniteDimensional ℂ U := smoothCompactAction_isFiniteVector F B S f
  apply Submodule.finiteDimensional_of_le (S₂ := U.map j)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  let k' : K := ⟨e∞ k.val, k.property⟩
  refine ⟨C k' f, FiniteVectors.action_mem_orbitSpan C k' f, ?_⟩
  rw [smoothSectionOnScheme_compactAction]
  have he : (e∞).symm k'.val = k.val := (e∞).symm_apply_apply _
  rw [he]

variable {d : ℕ}

/-- A single cofinite ideal of the actual tangent enveloping center
annihilates every infinite slice of the section. -/
theorem isCenterFiniteFunction
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (hcalc : AdelicDifferentialCommutator F GLG hsmooth)
    (hJ : Langlands.IsJointlyAdmissible R C) (f : W) :
    IsCenterFiniteFunction F GLG hsmooth hcalc (j f) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  let := smoothLieGroup F GLG hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  let e := infiniteCenterEquiv F n hsmooth hcalc
  let D := (sectionCenterAction F B S).comp e.toAlgHom
  let : FiniteDimensional ℂ (LinearMap.range (centralOrbitMap (sectionCenterAction F B S) f)) :=
    finiteDimensional_sectionCenterOrbit F B S hJ f
  have hD : FiniteDimensional ℂ (LinearMap.range (centralOrbitMap D f)) := by
    apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (centralOrbitMap (sectionCenterAction F B S) f))
    rintro _ ⟨z, rfl⟩
    exact ⟨e z, rfl⟩
  obtain ⟨I, hI, hann⟩ := exists_cofiniteIdeal_annihilates_of_finite_centralOrbit D f hD
  refine ⟨I, hI, fun z hz b hb => ?_⟩
  let E := GeneralLinearGroupPoints.plotSmoothGeneralLinearEquiv F n
  let g : InfinitePlotSmoothFunctions F GLG := ⟨functionInfiniteSlice F GLG (j f) b, hb⟩
  have hg : E g = smoothScalarSlice F B S (finiteHomeomorph F n b) f := by
    apply Subtype.ext
    funext a
    change j f (pair F GLG ((e∞).symm a) b) =
      (smoothScalarSlice F B S (finiteHomeomorph F n b) f).val a
    rw [smoothSectionOnScheme_pair, ContinuousMulEquiv.apply_symm_apply]
  apply E.injective
  change E (plotSmoothCenterAction F GLG hsmooth hcalc z g) = E 0
  rw [plotSmoothGeneralLinearEquiv_centerAction F n hsmooth hcalc z g, hg, LinearEquiv.map_zero]
  change envelopingAction F n (centerInclusion F n (e z))
    (smoothScalarSlice F B S (finiteHomeomorph F n b) f) = 0
  rw [← smoothScalarSlice_sectionEnvelopingAction]
  change smoothScalarSlice F B S (finiteHomeomorph F n b) (D z f) = 0
  rw [hann z hz, map_zero]

local notation "wt" => GroupScheme.GeneralLinear.blockShapeWeight B
local notation "p" => GroupScheme.GeneralLinear.blockParabolicHom (Fin n) (CommRingCat.of F) wt

/-- The actual smooth block sections from jointly admissible realizations
are automorphic functions on the standard parabolic quotient. -/
theorem isAutomorphicFunctionOn
    (hn : 0 < n) (hS : ∀ i, (S i).IsJointlyAdmissible)
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (hcalc : AdelicDifferentialCommutator F GLG hsmooth) (f : W) :
    IsAutomorphicFunctionOn F GLG hsmooth hcalc
      (parabolicQuotientSubgroup F p (blockUnipotentInclusion F B) (blockLeviInclusion F B))
      (generalLinearStandardInfiniteCompact F n) std (j f) :=
  ⟨realizedSection_isLeftInvariantUnder_parabolic F B S f.val.val,
    isAdelicSmoothFunction F B S f hsmooth,
    isInfiniteSubgroupFiniteFunction F B S f,
    isCenterFiniteFunction F B S hsmooth hcalc (smoothCompactFiniteSections_isJointlyAdmissible F B S hS) f,
    hasModerateGrowthFunction F B S hn f⟩

end SchemeSection

end Langlands.Global.AdelicBlockScalarSections
