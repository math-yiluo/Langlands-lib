import Langlands.Shimura.PEL.HarrisPolarizedBaseChangeChoice
import Langlands.Shimura.PEL.HarrisTaylorLiePointBaseChange

/-! # Dual-choice independence of actual Harris dimension and positive Lie pullback -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorLieWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  {S T : Scheme.{0}} (b : T ⟶ S)

local notation "PObjS" => PositivePolarizedAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (S := S)

variable [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (t : Spec (.of Ω) ⟶ T)
  (ht : ∀ Y : Cover T, Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T k.val).X.hom]
  [hμetT : ∀ k : Index (fun _ => True), Etale (mu T k.val).X.hom]
  (dualData₁ dualData₂ : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality b X)

variable (L : Type) [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F] (p : S ⟶ Spec (.of F))
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (S := T))

local notation "classesS" => IsoClass D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p compatibility h (t ≫ b) hs htor huS addS
local notation "classesT" => IsoClass D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L (b ≫ p) compatibility h t ht htor huT addT
local notation "pullClass₁" => classBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h t ht hs htor huS huT dualData₁ L p addS addT
local notation "pullClass₂" => classBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h t ht hs htor huS huT dualData₂ L p addS addT

/-- The restricted actual class map is independent of its actual dual-evaluation family. -/
theorem classBaseChange_dualData (U : HarrisLevel D) : pullClass₁ U = pullClass₂ U := by
  funext q
  apply Subtype.ext
  exact congrFun (HarrisPolarizedWeilLevel.ambientClassBaseChange_dualData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality
    dualAbelianBaseChangeNaturality polarizationBaseChange b compatibility h t ht hs htor huS huT
    dualData₁ dualData₂ addS addT U) q.val

local notation "towerS" => isoClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p compatibility h (t ≫ b) hs htor huS addS
local notation "towerT" => isoClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L (b ≫ p) compatibility h t ht htor huT addT
local notation "pullTower₁" => classTowerBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h t ht hs htor huS huT dualData₁ L p addS addT
local notation "pullTower₂" => classTowerBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h t ht hs htor huS huT dualData₂ L p addS addT

/-- Equality holds for natural transformations on the original Harris transporter category. -/
theorem classTowerBaseChange_dualData : pullTower₁ = pullTower₂ := by
  ext U q
  exact congrFun (classBaseChange_dualData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h t ht hs htor huS huT dualData₁ dualData₂ L p addS addT U) q

/-- Canonical restricted pullback from existence of actual constrained dual inputs. -/
def classTowerBaseChangeOfExists
    (dualExists : ∀ X : PObjS,
      Nonempty (PositivePullbackDualData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b X)) : towerS ⟶ towerT :=
  classTowerBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h t ht hs htor huS huT (fun X => Classical.choice (dualExists X)) L p addS addT

/-- Every supplied actual dual family computes the existence-only restricted pullback. -/
theorem classTowerBaseChangeOfExists_eq
    (dualExists : ∀ X : PObjS,
      Nonempty (PositivePullbackDualData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b X)) :
    classTowerBaseChangeOfExists D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h t ht hs htor huS huT L p addS addT dualExists = pullTower₁ :=
  classTowerBaseChange_dualData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h t ht hs htor huS huT
    (fun X => Classical.choice (dualExists X)) dualData₁ L p addS addT

/-- Every component of canonical restricted pullback is computed by any actual family. -/
@[simp] theorem classTowerBaseChangeOfExists_app
    (dualExists : ∀ X : PObjS,
      Nonempty (PositivePullbackDualData D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality b X))
    (U : HarrisLevel D) (q : classesS U) :
    (classTowerBaseChangeOfExists D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality b compatibility h
      t ht hs htor huS huT L p addS addT dualExists).app U q = pullClass₁ U q :=
  congrArg (fun (towerMap : towerS ⟶ towerT) => towerMap.app U q)
    (classTowerBaseChangeOfExists_eq D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality b compatibility h
      t ht hs htor huS huT dualData₁ L p addS addT dualExists)

local notation "includeS" => inclusionNatTrans D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p compatibility h (t ≫ b) hs htor huS addS
local notation "includeT" => inclusionNatTrans D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L (b ≫ p) compatibility h t ht htor huT addT

/-- The canonical restricted pullback is the restriction of the canonical ambient pullback. -/
theorem classTowerBaseChangeOfExists_inclusion
    (dualExists : ∀ X : PObjS,
      Nonempty (PositivePullbackDualData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b X)) :
    letI := auxiliaryStarRing D C
    classTowerBaseChangeOfExists D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h t ht hs htor huS huT L p addS addT dualExists ≫ includeT =
      includeS ≫ HarrisPolarizedWeilLevel.ambientClassTowerBaseChangeOfExists D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality
        dualAbelianBaseChangeNaturality polarizationBaseChange b compatibility h t ht hs htor huS huT addS addT dualExists := by
  let := auxiliaryStarRing D C
  exact classTowerBaseChange_inclusion D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h t ht hs htor huS huT
    (fun X => Classical.choice (dualExists X)) L p addS addT

local notation "forgetS" => forgetDimensionLieActionNatTrans D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
  compatibility h (t ≫ b) hs htor huS addS
local notation "forgetT" => forgetDimensionLieActionNatTrans D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L (b ≫ p)
  compatibility h t ht htor huT addT

/-- The canonical restricted pullback agrees with the existing joint action presheaf map. -/
theorem classTowerBaseChangeOfExists_forgetDimensionLieAction
    (dualExists : ∀ X : PObjS,
      Nonempty (PositivePullbackDualData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b X)) :
    classTowerBaseChangeOfExists D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h t ht hs htor huS huT L p addS addT dualExists ≫ forgetT =
      forgetS ≫ actionClassTowerBaseChange D b L p :=
  classTowerBaseChange_forgetDimensionLieAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h t ht hs htor huS huT
    (fun X => Classical.choice (dualExists X)) L p addS addT

section PointComparison
variable {Ω' : Type} [Field Ω'] {s : Spec (.of Ω') ⟶ T}
  {hsT : ∀ Y : Cover T, Finite (Fiber s Y)}
  (hsS : ∀ Y : Cover S, Finite (Fiber (s ≫ b) Y))

local notation "diagonal₁" => classTowerBaseChangeAlongPath D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  hsS htor huS huT dualData₁ addS addT L p
local notation "diagonal₂" => classTowerBaseChangeAlongPath D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  hsS htor huS huT dualData₂ addS addT L p

/-- The mixed point/base diagonal is independent of its dual-evaluation family. -/
theorem classTowerBaseChangeAlongPath_dualData
    (epath : fiberFunctor s hsT ≅ fiberFunctor t ht) : diagonal₁ epath = diagonal₂ epath := by
  unfold classTowerBaseChangeAlongPath
  rw [classTowerBaseChange_dualData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h s hsT hsS htor huS huT
    dualData₁ dualData₂ L p addS addT]

/-- Both independent choices, path and dual family, leave the entire diagonal unchanged. -/
theorem classTowerBaseChangeAlongPath_choices
    (epath fpath : fiberFunctor s hsT ≅ fiberFunctor t ht) : diagonal₁ epath = diagonal₂ fpath :=
  (classTowerBaseChangeAlongPath_dualData D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h t ht htor huS huT dualData₁ dualData₂ L p addS addT hsS epath).trans
    (classTowerBaseChangeAlongPath_path_independent D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h hsS htor huS huT
      dualData₂ addS addT L p epath fpath)

section Geometric
variable [ConnectedSpace T] [IsLocallyNoetherian T] [IsAlgClosed Ω] [IsAlgClosed Ω']

local notation "geometric₁" => classTowerGeometricBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  hsS htor huS huT dualData₁ addS addT L p (s := s) (t := t) (hs := hsT) (ht := ht)
local notation "geometric₂" => classTowerGeometricBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  hsS htor huS huT dualData₂ addS addT L p (s := s) (t := t) (hs := hsT) (ht := ht)

/-- Canonical geometric pullback is independent of every actual dual-evaluation family. -/
theorem classTowerGeometricBaseChange_dualData : geometric₁ = geometric₂ := by
  unfold classTowerGeometricBaseChange
  exact classTowerBaseChangeAlongPath_dualData D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h t ht htor huS huT dualData₁ dualData₂ L p addS addT hsS _

/-- Any path and any actual dual family compute the same canonical geometric pullback. -/
theorem classTowerGeometricBaseChange_eq_any_choices
    (epath : fiberFunctor s hsT ≅ fiberFunctor t ht) : geometric₁ = diagonal₂ epath :=
  (classTowerGeometricBaseChange_dualData D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h t ht htor huS huT dualData₁ dualData₂ L p addS addT hsS).trans
    (classTowerGeometricBaseChange_eq_path D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h hsS htor huS huT
      dualData₂ addS addT L p epath)

end Geometric
end PointComparison
end Langlands.Shimura.PEL.HarrisTaylorLieWeilLevel
