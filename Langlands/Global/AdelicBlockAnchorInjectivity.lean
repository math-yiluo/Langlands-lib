import Langlands.Global.AdelicBlockCompactSpecialization
import Langlands.Global.AdelicEisensteinAnchorInjectivity

/-! # Convergence-region injectivity for the smooth block sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme
open Langlands.GeneralLinear (BlockShape)
open Langlands.GroupScheme.GeneralLinear
open EisensteinJet AdelicBlockEisensteinGeometry AdelicGroupPoints GeneralLinearGroupPoints

/-- The two analytic inputs imply the injectivity on all finite ranges used by the
compact specialization of the smooth block sections. -/
def BlockEisensteinInjectivityReduction : Prop :=
  EisensteinMeromorphicContinuationStatement.{u} → EisensteinGenericInjectivityStatement.{u} →
  ∀ (F : Type u) [Field F] [NumberField F] (r : ℕ) (B : BlockShape (r + 1))
    (S : ∀ i : Fin B.length, OperatorRealization F (B.size i)),
    (∀ i, (S i).IsJointlyAdmissible) → BlockEisensteinInjectiveOnFiniteRanges F r B S

variable (F : Type u) [Field F] [NumberField F] (r : ℕ) (B : BlockShape (r + 1))
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local notation "n" => r + 1
local notation "𝕜" => CommRingCat.of F
local notation "GLG" => groupScheme (Fin n) 𝕜
local notation "std" => MatrixRepresentation.standard (Fin n) 𝕜
local notation "wt" => blockShapeWeight B
local notation "P" => blockParabolicScheme (Fin n) 𝕜 wt
local notation "p" => blockParabolicHom (Fin n) 𝕜 wt
local notation "T" => blockRootData F B
local notation "hG" => isConnectedReductive_generalLinear F (Fin n)
local notation "hs" => (hG).smoothDimension_spec
local notation "hc" => adelicDifferentialCommutator_of_smooth F GLG hs
local notation "hK" => isIwasawaCompact_blockParabolic F B
local notation "W" => smoothCompactFiniteSections F B S

local instance blockAnchorGLAffine : IsAffine (GLG).X.left := isAffine_groupScheme (Fin n) 𝕜
local instance blockAnchorParabolicAffine : IsAffine (P).X.left := blockParabolic_isAffine F B
local instance blockAnchorParabolicClosed : IsClosedImmersion (p).hom.hom.left :=
  isClosedSubgroup_blockParabolicHom (Fin n) 𝕜 wt
local instance blockAnchorTorusMono : Mono (T).root.data.i.hom.hom.left := (T).torus_mono
local instance blockAnchorFactorMono : Mono (CommGroupScheme.groupHom (T).root.data.f).hom.hom.left :=
  (T).factor_mono
local instance blockAnchorWeylFinite : Fintype (relativeWeylGroup (T).root.data.i) :=
  @Fintype.ofFinite _ (T).finite_weylGroup
local instance blockAnchorSmoothGroup : AddCommGroup (FiniteSmoothRealizedSections F B S) :=
  Submodule.addCommGroup _
local instance blockAnchorSectionGroup : AddCommGroup W := Submodule.addCommGroup _

set_option maxHeartbeats 850000 in
private theorem blockInjectiveOnFiniteRanges
    (hcont : EisensteinMeromorphicContinuationStatement.{u}) (hGI : EisensteinGenericInjectivityStatement.{u})
    (hS : ∀ i, (S i).IsJointlyAdmissible) : BlockEisensteinInjectiveOnFiniteRanges F r B S := by
  intro π hπ
  let : FiniteDimensional ℂ π.range := hπ
  let j := (smoothSectionOnScheme F B S).comp π.range.subtype
  have hj : Function.Injective j := (smoothSectionOnScheme_injective F B S).comp Subtype.val_injective
  have hstd : IsClosedSubgroup std := by
    change IsClosedImmersion (𝟙 (GLG).X.left)
    infer_instance
  exact eventually_eisensteinSeries_injective_of_genericInjectivity
    (T).root (T).splitComponent (T).splitTorus (hK) std (Nat.succ_pos r) hstd hs hc
    (T).parameterCoordinates hcont hGI (hG)
    (blockUnipotentInclusion_isLeviGeometricUnipotentRadical F B)
    (standardCompactPoints_isMaximalCompact F n) j hj (fun w => by
      simpa only [j, LinearMap.comp_apply, Submodule.subtype_apply,
        standardCompactPoints_comap_ofInfinite] using
        SchemeSection.isAutomorphicFunctionOn F B S (Nat.succ_pos r) hS hs hc w.val)

/-- Apply finite-dimensional continuation and relation detection to each
projection range in the smooth block model. -/
theorem blockEisensteinInjectivityReduction : BlockEisensteinInjectivityReduction.{u} := by
  intro hcont hGI F _ _ r B S hS
  exact blockInjectiveOnFiniteRanges F r B S hcont hGI hS

end Langlands.Global.AdelicBlockScalarSections
