import Langlands.Automorphic.GeneralLinearFiniteAdelicEnveloping
import Langlands.Automorphic.DifferentialCenterFinite
import Langlands.Automorphic.GroupSchemeForms
import Langlands.Automorphic.GroupSchemeActualDifferential

/-! # General-linear comparison of whole-function center finiteness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints
open Langlands.Geometry.Manifold

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance centerFiniteGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance centerFiniteGeneralLinearAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
  Module.addCommMonoidToAddCommGroup ℂ

local instance centerFiniteMatrixRationalAddCommGroup :
    AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _

local instance centerFiniteMatrixContinuousAddCommGroup :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _

local instance centerFiniteMatrixAddCommGroup :
    AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _

variable {d : ℕ} (hsmooth : SmoothOfRelativeDimension d
  (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom)
  (hcalc : AdelicDifferentialCommutator F
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) hsmooth)

/-- The unchanged function comparison intertwines every actual center operator. -/
theorem finitePlotSmoothGeneralLinearEquiv_adelicCenterAction
    (z : AdelicEnvelopingCenter F GLG hsmooth) (f : FinitePlotSmoothRationalFunctions F GLG) :
    finitePlotSmoothGeneralLinearEquiv F n (adelicCenterAction F GLG hsmooth hcalc z f) =
      Langlands.Automorphic.finiteSmoothCenterAction F n
        (GeneralLinearGroupPoints.infiniteCenterEquiv F n hsmooth hcalc z)
        (finitePlotSmoothGeneralLinearEquiv F n f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  let := smoothLieGroup F GLG hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F GLG) := LieGroup.of_le (n := ∞) (by simp)
  exact finitePlotSmoothGeneralLinearEquiv_centerAction F n hsmooth hcalc z f

/-- The original function equivalence as an intertwiner for the reindexed center action. -/
def generalLinearAdelicCenterIntertwiner :
    Representation.IntertwiningMap (adelicCenterAction F GLG hsmooth hcalc).toMonoidHom
      ((Langlands.Automorphic.finiteSmoothCenterRepresentation F n).comp
        (GeneralLinearGroupPoints.infiniteCenterEquiv F n hsmooth hcalc).toMonoidHom) where
  toLinearMap := (finitePlotSmoothGeneralLinearEquiv F n).toLinearMap
  isIntertwining' z := by
    apply LinearMap.ext
    intro f
    exact finitePlotSmoothGeneralLinearEquiv_adelicCenterAction F n hsmooth hcalc z f

/-- The center equivalence reindexes the full orbit, with no separate bounds on slices. -/
theorem isAdelicCenterFinite_iff_generalLinear
    (f : FinitePlotSmoothRationalFunctions F GLG) :
    IsAdelicCenterFinite F GLG hsmooth hcalc f ↔
      Langlands.Automorphic.IsCenterFinite F n
        (Langlands.Automorphic.finiteSmoothInclusion F n
          (finitePlotSmoothGeneralLinearEquiv F n f)) := by
  rw [Langlands.Automorphic.isCenterFinite_iff_finiteSmoothCenterVector]
  refine (Langlands.FiniteVectors.isFiniteVector_map_iff
    (generalLinearAdelicCenterIntertwiner F n hsmooth hcalc)
    (finitePlotSmoothGeneralLinearEquiv F n).injective f).symm.trans ?_
  change Module.Finite ℂ (Submodule.span ℂ (Set.range
    ((fun z => Langlands.Automorphic.finiteSmoothCenterAction F n z
      (finitePlotSmoothGeneralLinearEquiv F n f)) ∘
        GeneralLinearGroupPoints.infiniteCenterEquiv F n hsmooth hcalc))) ↔ _
  rw [(GeneralLinearGroupPoints.infiniteCenterEquiv F n hsmooth hcalc).surjective.range_comp]
  rfl

/-- The actual global annihilator is the pullback of the original common slice-family ideal. -/
theorem generalLinearAdelicCenterAnnihilator
    (f : FinitePlotSmoothRationalFunctions F GLG) :
    Ideal.comap (GeneralLinearGroupPoints.infiniteCenterEquiv F n hsmooth hcalc).toRingHom
      (Langlands.Automorphic.centerFamilyAnnihilator F n
        (Langlands.Automorphic.finiteSmoothCenterSlices F n
          (finitePlotSmoothGeneralLinearEquiv F n f))) =
      adelicCenterAnnihilator F GLG hsmooth hcalc f := by
  ext z
  change (GeneralLinearGroupPoints.infiniteCenterEquiv F n hsmooth hcalc z ∈
    Langlands.Automorphic.centerFamilyAnnihilator F n
      (Langlands.Automorphic.finiteSmoothCenterSlices F n
        (finitePlotSmoothGeneralLinearEquiv F n f))) ↔
      adelicCenterAction F GLG hsmooth hcalc z f = 0
  rw [Langlands.Automorphic.mem_centerFamilyAnnihilator]
  constructor
  · intro hz
    apply (finitePlotSmoothGeneralLinearEquiv F n).injective
    rw [map_zero, finitePlotSmoothGeneralLinearEquiv_adelicCenterAction]
    apply Langlands.Automorphic.finiteSmoothSlice_injective F n
    funext b
    dsimp only
    rw [Langlands.Automorphic.finiteSmoothSlice_centerAction, map_zero]
    exact hz b
  · intro hz b
    have h := finitePlotSmoothGeneralLinearEquiv_adelicCenterAction F n hsmooth hcalc z f
    rw [hz, map_zero] at h
    have hs := congrArg (Langlands.Automorphic.finiteSmoothSlice F n b) h
    change Langlands.Global.ArchimedeanGL.centerAction F n
      (GeneralLinearGroupPoints.infiniteCenterEquiv F n hsmooth hcalc z)
      (Langlands.Automorphic.finiteSmoothSlice F n b
        (finitePlotSmoothGeneralLinearEquiv F n f)) = 0
    simpa only [map_zero, Langlands.Automorphic.finiteSmoothSlice_centerAction] using hs.symm

/-- Restrict the original function equivalence to the two existing global center-finite spaces. -/
def finitePlotSmoothGeneralLinearCenterEquiv :
    adelicCenterFiniteSubmodule F GLG hsmooth hcalc ≃ₗ[ℂ]
      Langlands.Automorphic.CenterFiniteFiniteSmoothRationalFunctions F n where
  toFun f := ⟨finitePlotSmoothGeneralLinearEquiv F n f.val,
    (isAdelicCenterFinite_iff_generalLinear F n hsmooth hcalc f.val).mp f.property⟩
  invFun f := ⟨(finitePlotSmoothGeneralLinearEquiv F n).symm f.val,
    (isAdelicCenterFinite_iff_generalLinear F n hsmooth hcalc _).mpr (by
      rw [LinearEquiv.apply_symm_apply]
      exact f.property)⟩
  left_inv f := Subtype.ext ((finitePlotSmoothGeneralLinearEquiv F n).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((finitePlotSmoothGeneralLinearEquiv F n).apply_symm_apply f.val)
  map_add' f g := Subtype.ext (map_add (finitePlotSmoothGeneralLinearEquiv F n) f.val g.val)
  map_smul' z f := Subtype.ext (map_smul (finitePlotSmoothGeneralLinearEquiv F n) z f.val)

@[simp]
theorem finitePlotSmoothGeneralLinearCenterEquiv_val
    (f : adelicCenterFiniteSubmodule F GLG hsmooth hcalc) :
    (finitePlotSmoothGeneralLinearCenterEquiv F n hsmooth hcalc f).val =
      finitePlotSmoothGeneralLinearEquiv F n f.val := rfl

/-- The calculus proof in these comparisons can always be supplied by the actual atlas theorem. -/
theorem isActualAdelicCenterFinite_iff_generalLinear
    (f : FinitePlotSmoothRationalFunctions F GLG) :
    IsAdelicCenterFinite F GLG hsmooth
        (adelicDifferentialCommutator_of_smooth F GLG hsmooth) f ↔
      Langlands.Automorphic.IsCenterFinite F n
        (Langlands.Automorphic.finiteSmoothInclusion F n
          (finitePlotSmoothGeneralLinearEquiv F n f)) :=
  isAdelicCenterFinite_iff_generalLinear F n hsmooth
    (adelicDifferentialCommutator_of_smooth F GLG hsmooth) f

end Langlands.Automorphic.GroupSchemeFunctions
