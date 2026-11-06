import Langlands.Automorphic.GeneralLinearAdelicCenterFinite
import Langlands.Automorphic.GroupSchemeAdelicSliceGrowth
import Langlands.Automorphic.GeneralLinearGrowthIndependence
import Langlands.Automorphic.Forms

/-! # Original-function inclusions into the existing general-linear form space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance formsGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance formsGeneralLinearAddCommGroup :
    AddCommGroup (FinitePlotSmoothRationalFunctions F GLG) :=
  Module.addCommMonoidToAddCommGroup ℂ

local instance formsMatrixRationalAddCommGroup :
    AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _

local instance formsMatrixContinuousAddCommGroup :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _

local instance formsMatrixAddCommGroup :
    AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _

/-- The original standard infinite compact, on the actual group-scheme point carrier. -/
def generalLinearStandardInfiniteCompact : Subgroup (InfiniteAdelicGroupPoints F GLG) :=
  (standardInfiniteCompact F n).comap
    (GeneralLinearGroupPoints.infiniteHomeomorph F n).toMonoidHom

/-- The original maximal-compact proof transports through the actual homeomorphism. -/
theorem generalLinearStandardInfiniteCompact_isMaximalCompact :
    Langlands.CompactIwasawa.IsMaximalCompact (generalLinearStandardInfiniteCompact F n) := by
  have hK : Langlands.CompactIwasawa.IsMaximalCompact (standardInfiniteCompact F n) :=
    ⟨isCompact_standardInfiniteCompact F n, standardInfiniteCompactMaximality F n⟩
  rw [generalLinearStandardInfiniteCompact, Subgroup.comap_equiv_eq_map_symm']
  exact hK.map (GeneralLinearGroupPoints.infiniteHomeomorph F n).symm

variable (U : Subgroup (InfiniteAdelicGL F n))

/-- The original ambient function map intertwines the corresponding subgroup actions. -/
def generalLinearAdelicInfiniteIntertwiner :
    Representation.IntertwiningMap
      (finitePlotSmoothInfiniteSubgroupAction F GLG
        (U.comap (GeneralLinearGroupPoints.infiniteHomeomorph F n).toMonoidHom))
      ((Langlands.Automorphic.infiniteSubgroupRightAction F n U).comp
        ((GeneralLinearGroupPoints.infiniteHomeomorph F n).toMonoidHom.subgroupComap U)) where
  toLinearMap := (continuousGeneralLinearEquiv F n).toLinearMap.comp
    (finitePlotSmoothRationalSubrepresentation F GLG).toSubmodule.subtype
  isIntertwining' k := by
    apply LinearMap.ext
    intro f
    change continuousGeneralLinearEquiv F n
        (continuousRightAction F GLG (AdelicGroupPoints.ofInfinite F GLG k.val) f.val) =
      Langlands.Automorphic.continuousRightAction F n
        (AdelicGL.ofInfinite F n (GeneralLinearGroupPoints.infiniteHomeomorph F n k.val))
        (continuousGeneralLinearEquiv F n f.val)
    rw [continuousGeneralLinearEquiv_rightAction,
      GeneralLinearGroupPoints.adelicHomeomorph_ofInfinite]

/-- Whole-function infinite-subgroup finiteness is preserved and reflected. -/
theorem isAdelicInfiniteFinite_iff_generalLinear
    (f : FinitePlotSmoothRationalFunctions F GLG) :
    IsAdelicInfiniteFinite F GLG
        (U.comap (GeneralLinearGroupPoints.infiniteHomeomorph F n).toMonoidHom) f ↔
      Langlands.Automorphic.IsInfiniteFinite F n U (continuousGeneralLinearEquiv F n f.val) := by
  refine (Langlands.FiniteVectors.isFiniteVector_map_iff
    (generalLinearAdelicInfiniteIntertwiner F n U)
    ((continuousGeneralLinearEquiv F n).injective.comp Subtype.val_injective) f).symm.trans ?_
  change Module.Finite ℂ (Submodule.span ℂ (Set.range
    ((fun k => Langlands.Automorphic.infiniteSubgroupRightAction F n U k
      (continuousGeneralLinearEquiv F n f.val)) ∘
        (GeneralLinearGroupPoints.infiniteHomeomorph F n).toMonoidHom.subgroupComap U))) ↔ _
  rw [((GeneralLinearGroupPoints.infiniteHomeomorph F n).toMonoidHom.subgroupComap_surjective
    U (GeneralLinearGroupPoints.infiniteHomeomorph F n).surjective).range_comp]
  rfl

variable {d N : ℕ}
  (rho : GroupScheme.MatrixRepresentation
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) (Fin N))
  (hsmooth : SmoothOfRelativeDimension d
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom)
  (hcalc : AdelicDifferentialCommutator F
    (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)) hsmooth)
  (hrho : GroupScheme.IsClosedSubgroup rho) (hN : 0 < N)

include hrho hN

/-- Full growth for any closed matrix embedding supplies the original matrix slice growth. -/
theorem hasPolynomialGrowth_generalLinear_of_adelicModerateGrowth
    (f : FinitePlotSmoothRationalFunctions F GLG)
    (hf : HasAdelicModerateGrowth F GLG rho f.val) :
    Langlands.Automorphic.HasPolynomialGrowth F n (continuousGeneralLinearEquiv F n f.val) := by
  apply (Langlands.Automorphic.mem_polynomialGrowthSubrepresentation F n _).mp
  apply (continuousGeneralLinearEquiv_mem_polynomialGrowth_of_closedImmersion
    F n rho hrho f.val).mpr
  exact (mem_polynomialGrowthSubrepresentation F GLG rho f.val).mpr
    (hf.polynomialGrowth F GLG rho hN)

/-- The exact comparison retains the extra full adelic growth condition. -/
theorem isAdelicAutomorphicForm_iff_generalLinear_and_adelicGrowth
    (f : FinitePlotSmoothRationalFunctions F GLG) :
    IsAdelicAutomorphicForm F GLG (generalLinearStandardInfiniteCompact F n)
        rho hsmooth hcalc f ↔
      Langlands.Automorphic.IsAutomorphicForm F n
        (Langlands.Automorphic.finiteSmoothInclusion F n
          (finitePlotSmoothGeneralLinearEquiv F n f)) ∧
      HasAdelicModerateGrowth F GLG rho f.val := by
  constructor
  · rintro ⟨hk, hc, hg⟩
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hg⟩
    · exact (Langlands.Automorphic.hasFiniteLevel_iff_mem_finiteSmooth F n _).mpr
        (finitePlotSmoothGeneralLinearEquiv F n f).property.2
    · exact (isAdelicInfiniteFinite_iff_generalLinear F n
        (standardInfiniteCompact F n) f).mp hk
    · exact (isAdelicCenterFinite_iff_generalLinear F n hsmooth hcalc f).mp hc
    · exact hasPolynomialGrowth_generalLinear_of_adelicModerateGrowth F n rho hrho hN f hg
  · rintro ⟨hf, hg⟩
    exact ⟨(isAdelicInfiniteFinite_iff_generalLinear F n
        (standardInfiniteCompact F n) f).mpr hf.2.1,
      (isAdelicCenterFinite_iff_generalLinear F n hsmooth hcalc f).mpr hf.2.2.1, hg⟩

/-- The actual manifold-calculus theorem supplies the proof parameter in the comparison. -/
theorem isActualAdelicAutomorphicForm_iff_generalLinear_and_adelicGrowth
    (f : FinitePlotSmoothRationalFunctions F GLG) :
    IsAdelicAutomorphicForm F GLG (generalLinearStandardInfiniteCompact F n)
        rho hsmooth (adelicDifferentialCommutator_of_smooth F GLG hsmooth) f ↔
      Langlands.Automorphic.IsAutomorphicForm F n
        (Langlands.Automorphic.finiteSmoothInclusion F n
          (finitePlotSmoothGeneralLinearEquiv F n f)) ∧
      HasAdelicModerateGrowth F GLG rho f.val :=
  isAdelicAutomorphicForm_iff_generalLinear_and_adelicGrowth F n rho hsmooth
    (adelicDifferentialCommutator_of_smooth F GLG hsmooth) hrho hN f

variable (hG : GroupScheme.IsConnectedReductive
  (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)))

/-- Restrict the unchanged finite-smooth function map to the actual original form spaces. -/
def adelicAutomorphicGeneralLinearMap :
    AdelicAutomorphicForms F GLG (generalLinearStandardInfiniteCompact F n)
        rho hsmooth hcalc hG hrho
        (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN →ₗ[ℂ]
      Langlands.Automorphic.AutomorphicForms F n where
  toFun f := ⟨finitePlotSmoothGeneralLinearEquiv F n f.val,
    (Langlands.Automorphic.mem_automorphicSubrepresentation F n _).mpr
      ((isAdelicAutomorphicForm_iff_generalLinear_and_adelicGrowth F n rho hsmooth
        hcalc hrho hN f.val).mp
          ((mem_adelicAutomorphicSubrepresentation F GLG
            (generalLinearStandardInfiniteCompact F n) rho hsmooth hcalc hG hrho
            (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN f.val).mp
              f.property)).1⟩
  map_add' f g := Subtype.ext (map_add (finitePlotSmoothGeneralLinearEquiv F n) f.val g.val)
  map_smul' z f := Subtype.ext (map_smul (finitePlotSmoothGeneralLinearEquiv F n) z f.val)

theorem adelicAutomorphicGeneralLinearMap_injective :
    Function.Injective (adelicAutomorphicGeneralLinearMap F n rho hsmooth hcalc hrho hN hG) := by
  intro f g h
  apply Subtype.ext
  exact (finitePlotSmoothGeneralLinearEquiv F n).injective (congrArg Subtype.val h)

@[simp]
theorem adelicAutomorphicGeneralLinearMap_val
    (f : AdelicAutomorphicForms F GLG (generalLinearStandardInfiniteCompact F n)
      rho hsmooth hcalc hG hrho
      (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN) :
    (adelicAutomorphicGeneralLinearMap F n rho hsmooth hcalc hrho hN hG f).val =
      finitePlotSmoothGeneralLinearEquiv F n f.val := rfl

/-- Forgetting both form conditions returns the existing continuous-function comparison. -/
theorem adelicAutomorphicGeneralLinearMap_toContinuous
    (f : AdelicAutomorphicForms F GLG (generalLinearStandardInfiniteCompact F n)
      rho hsmooth hcalc hG hrho
      (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN) :
    Langlands.Automorphic.automorphicToContinuous F n
        (adelicAutomorphicGeneralLinearMap F n rho hsmooth hcalc hrho hN hG f) =
      continuousGeneralLinearEquiv F n
        (adelicAutomorphicToContinuous F GLG (generalLinearStandardInfiniteCompact F n)
          rho hsmooth hcalc hG hrho
          (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN f) := rfl

/-- The injection preserves values at corresponding original adelic points. -/
theorem evaluate_adelicAutomorphicGeneralLinearMap
    (f : AdelicAutomorphicForms F GLG (generalLinearStandardInfiniteCompact F n)
      rho hsmooth hcalc hG hrho
      (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN)
    (x : AdelicGroupPoints F GLG) :
    Langlands.Automorphic.ContinuousRationalFunctions.evaluate F n
        (Langlands.Automorphic.automorphicToContinuous F n
          (adelicAutomorphicGeneralLinearMap F n rho hsmooth hcalc hrho hN hG f))
        (GeneralLinearGroupPoints.adelicHomeomorph F n x) =
      evaluate F GLG
        (adelicAutomorphicToContinuous F GLG (generalLinearStandardInfiniteCompact F n)
          rho hsmooth hcalc hG hrho
          (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN f) x :=
  evaluate_continuousGeneralLinearEquiv_at_point F n f.val.val x

/-- The form injection intertwines the original positive finite right translations. -/
theorem adelicAutomorphicGeneralLinearMap_finiteRightAction
    (c : FiniteAdelicGroupPoints F GLG)
    (f : AdelicAutomorphicForms F GLG (generalLinearStandardInfiniteCompact F n)
      rho hsmooth hcalc hG hrho
      (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN) :
    adelicAutomorphicGeneralLinearMap F n rho hsmooth hcalc hrho hN hG
        (adelicAutomorphicFiniteRightAction F GLG (generalLinearStandardInfiniteCompact F n)
          rho hsmooth hcalc hG hrho
          (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN c f) =
      Langlands.Automorphic.automorphicFiniteRightAction F n
        (GeneralLinearGroupPoints.finiteHomeomorph F n c)
        (adelicAutomorphicGeneralLinearMap F n rho hsmooth hcalc hrho hN hG f) := by
  apply Subtype.ext
  apply Subtype.ext
  exact continuousGeneralLinearEquiv_finiteRightAction F n f.val.val c

/-- Bundle the form inclusion for the original finite group acting through its homeomorphism. -/
def adelicAutomorphicGeneralLinearIntertwiner :
    Representation.IntertwiningMap
      (adelicAutomorphicFiniteRightAction F GLG (generalLinearStandardInfiniteCompact F n)
        rho hsmooth hcalc hG hrho
        (generalLinearStandardInfiniteCompact_isMaximalCompact F n) hN)
      ((Langlands.Automorphic.automorphicFiniteRightAction F n).comp
        (GeneralLinearGroupPoints.finiteHomeomorph F n).toMonoidHom) where
  toLinearMap := adelicAutomorphicGeneralLinearMap F n rho hsmooth hcalc hrho hN hG
  isIntertwining' c := by
    apply LinearMap.ext
    intro f
    exact adelicAutomorphicGeneralLinearMap_finiteRightAction F n rho hsmooth hcalc hrho hN hG c f

end Langlands.Automorphic.GroupSchemeFunctions
