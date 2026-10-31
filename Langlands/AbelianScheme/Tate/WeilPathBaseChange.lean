import Langlands.AbelianScheme.Tate.PathBaseChange
import Langlands.AbelianScheme.Tate.WeilLevelBaseChange
import Langlands.AbelianScheme.Tate.WeilAdelicLevelTransport
import Langlands.AbelianScheme.Tate.WeilPrimeToAdelicLevelTransport

/-! # Base change and path transport of actual Weil-compatible levels -/

universe u v w
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
noncomputable section

namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme Langlands.Shimura.PEL
open GroupScheme.Tate (Index)

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (A : AbelianScheme S)

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (hA' : HasDualScheme ((baseChange b).obj A))
  (geometryA' : DualSchemeGeometry ((baseChange b).obj A) hA')
  (MA' : LineBundle ((relativeSpace ((baseChange b).obj A).X.hom).obj
    (dualScheme ((baseChange b).obj A) hA')))
  (evaluationA' : tensorObj (poincareFamily ((baseChange b).obj A) hA').obj.carrier
    MA'.obj ≅ structureSheaf ((relativeSpace ((baseChange b).obj A).X.hom).obj
      (dualScheme ((baseChange b).obj A) hA')))

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
set_option quotPrecheck false in
local notation "DAb" => dualAbelianSchemeFromEvaluation ((baseChange b).obj A) hA'
  geometryA' preservation MA' evaluationA' stability composition unitCoherence associativity
  comparison symmetry
local notation "lamBC" => canonicalDualValuedBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA
  evaluationA hA' geometryA' MA' evaluationA'

variable [QuasiSeparatedSpace S] [QuasiSeparatedSpace S']
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (lam : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA evaluationA
    stability composition unitCoherence associativity comparison symmetry)
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  (htor : TorsionFiniteEtaleStatement.{u})
  {Ω Ω' : Type u} [Field Ω] [Field Ω']
  {s : Spec (.of Ω) ⟶ S'} {t : Spec (.of Ω') ⟶ S'}
  {hs : ∀ Y : Cover S', Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S', Finite (Fiber t Y)}
  (hsb : ∀ Y : Cover S, Finite (Fiber (s ≫ b) Y))
  (htb : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))

set_option quotPrecheck false in
local notation "iBC" => (AbelianScheme.rationalBaseChangeEnd b A).comp i
local notation "geo" => rationalWeilGeometricTransport

section Full
variable (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  (hu' : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S', ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom]
  [hμfin' : ∀ n : Index (fun _ => True), IsFinite (mu S' n.val).X.hom]
  [hμet' : ∀ n : Index (fun _ => True), Etale (mu S' n.val).X.hom]

local notation "FrameA" => WeilAdelicFrame preservation composition unitCoherence associativity
  comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ
local notation "Frameb" => WeilAdelicFrame preservation composition unitCoherence associativity
  comparison symmetry stability hA' geometryA' MA' evaluationA' compatibility (lamBC lam) h iBC V ψ
local notation "frameBC" => weilAdelicFrameBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hA'
  geometryA' MA' evaluationA' compatibility lam h i V ψ
local notation "transA" => weilAdelicFrameTransport preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geo hA geometryA MA evaluationA lam
  h i V ψ htor hu (hμfin := hμfin) (hμet := hμet)
local notation "transb" => weilAdelicFrameTransport preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geo hA' geometryA' MA' evaluationA'
  (lamBC lam) h iBC V ψ htor hu' (hμfin := hμfin') (hμet := hμet')

/-- Base change of actual compatible frames commutes with transport along a pushed path. -/
theorem weilAdelicFrameBaseChange_transport
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (eta : Frameb s) :
    frameBC t (transb p eta) =
      transA (pathPushforward b hsb htb p) (frameBC s eta) := by
  apply Subtype.ext
  ext x
  exact rationalBaseChange_transport b hsb htb htor A (fun _ => True) hu hu' p (eta.1 x)

local notation "frameSquare" => weilAdelicFrameBaseChange_transport b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA
  hA' geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb htb hu hu'
  (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')

/-- The inverse frame comparisons give the pullback-oriented path square. -/
theorem weilAdelicFrameBaseChange_symm_transport
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (eta : FrameA (s ≫ b)) :
    (frameBC t).symm (transA (pathPushforward b hsb htb p) eta) =
      transb p ((frameBC s).symm eta) := by
  apply (frameBC t).injective
  rw [Equiv.apply_symm_apply, frameSquare, Equiv.apply_symm_apply]

local notation "frameInvSquare" => weilAdelicFrameBaseChange_symm_transport b A preservation
  composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA
  evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb htb hu hu'
  (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')

/-- Actual compatible-frame comparison along the diagonal: path transport, then base change. -/
def weilAdelicFrameBaseChangeAlongPath (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Frameb s ≃ FrameA (t ≫ b) :=
  (transb p).trans (frameBC t)

/-- The diagonal comparison also equals base change followed by pushed-path transport. -/
theorem weilAdelicFrameBaseChangeAlongPath_apply
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (eta : Frameb s) :
    weilAdelicFrameBaseChangeAlongPath b A preservation composition unitCoherence associativity
        comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA'
        MA' evaluationA' compatibility lam h i V ψ htor hu' p eta =
      transA (pathPushforward b hsb htb p) (frameBC s eta) :=
  frameSquare p eta

local notation "G" => ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ
local notation "rightA" => weilAdelicFrameRightAction preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ
local notation "rightb" => weilAdelicFrameRightAction preservation composition unitCoherence
  associativity comparison symmetry stability hA' geometryA' MA' evaluationA' compatibility
  (lamBC lam) h iBC V ψ
local notation "monA" => weilAdelicFrameMonodromyAction preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geo hA geometryA MA evaluationA lam h i V ψ
local notation "monb" => weilAdelicFrameMonodromyAction preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geo hA' geometryA' MA' evaluationA'
  (lamBC lam) h iBC V ψ
local notation "commA" => weilAdelicFrameActionsComm preservation composition unitCoherence associativity
  comparison symmetry stability compatibility geo hA geometryA MA evaluationA lam h i V ψ
local notation "commb" => weilAdelicFrameActionsComm preservation composition unitCoherence associativity
  comparison symmetry stability compatibility geo hA' geometryA' MA' evaluationA' (lamBC lam) h iBC V ψ
local notation "LevelA" => WeilAdelicLevel preservation composition unitCoherence associativity
  comparison symmetry stability compatibility geo hA geometryA MA evaluationA lam h i V ψ
local notation "Levelb" => WeilAdelicLevel preservation composition unitCoherence associativity
  comparison symmetry stability compatibility geo hA' geometryA' MA' evaluationA' (lamBC lam) h iBC V ψ
local notation "levelBC" => weilAdelicLevelBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA'
  MA' evaluationA' compatibility lam h i V ψ
local notation "levelTransA" => weilAdelicLevelTransport preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geo hA geometryA MA evaluationA lam
  h i V ψ htor hu (hμfin := hμfin) (hμet := hμet)
local notation "levelTransb" => weilAdelicLevelTransport preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geo hA' geometryA' MA' evaluationA'
  (lamBC lam) h iBC V ψ htor hu' (hμfin := hμfin') (hμet := hμet')

/-- The actual fixed-level pullback commutes with path transport; no representative is fixed. -/
theorem weilAdelicLevelBaseChange_transport (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : LevelA (s ≫ b) hsb htor hu (hμfin := hμfin) (hμet := hμet) U) :
    levelBC t ht htb htor hu hu' (hμfin := hμfin) (hμet := hμet)
        (hμfin' := hμfin') (hμet' := hμet') U
        (levelTransA U (pathPushforward b hsb htb p) q) =
      levelTransb U p
        (levelBC s hs hsb htor hu hu' (hμfin := hμfin) (hμet := hμet)
          (hμfin' := hμfin') (hμet' := hμet') U q) := by
  let := rightA (s ≫ b)
  let := rightA (t ≫ b)
  let := rightb s
  let := rightb t
  let := monA (s ≫ b) hsb htor hu (hμfin := hμfin) (hμet := hμet)
  let := monA (t ≫ b) htb htor hu (hμfin := hμfin) (hμet := hμet)
  let := monb s hs htor hu' (hμfin := hμfin') (hμet := hμet')
  let := monb t ht htor hu' (hμfin := hμfin') (hμet := hμet')
  let := commA (s ≫ b) hsb htor hu (hμfin := hμfin) (hμet := hμet)
  let := commA (t ≫ b) htb htor hu (hμfin := hμfin) (hμet := hμet)
  let := commb s hs htor hu' (hμfin := hμfin') (hμet := hμet')
  let := commb t ht htor hu' (hμfin := hμfin') (hμet := hμet')
  apply Subtype.ext
  simp only [weilAdelicLevelBaseChange, InvariantOrbit.pullback, weilAdelicLevelTransport,
    InvariantOrbit.equiv, Equiv.symm, Equiv.coe_fn_mk, InvariantOrbit.map_val]
  induction q.1 using Quotient.inductionOn with
  | h eta => exact congrArg (RightOrbit.mk U) (frameInvSquare p eta)

/-- Diagonal pullback of a fixed compatible level: pointed pullback, then path transport. -/
def weilAdelicLevelBaseChangeAlongPath (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    LevelA (s ≫ b) hsb htor hu (hμfin := hμfin) (hμet := hμet) U →
      Levelb t ht htor hu' (hμfin := hμfin') (hμet := hμet') U :=
  fun q => levelTransb U p
    (levelBC s hs hsb htor hu hu' (hμfin := hμfin) (hμet := hμet)
      (hμfin' := hμfin') (hμet' := hμet') U q)

local notation "levelAlong" => weilAdelicLevelBaseChangeAlongPath b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA
  hA' geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb hu hu'
  (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')

/-- The other route for the diagonal fixed-level pullback uses the pushed path first. -/
theorem weilAdelicLevelBaseChangeAlongPath_apply (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : LevelA (s ≫ b) hsb htor hu (hμfin := hμfin) (hμet := hμet) U) :
    levelAlong U p q =
      levelBC t ht htb htor hu hu' (hμfin := hμfin) (hμet := hμet)
        (hμfin' := hμfin') (hμet' := hμet') U
        (levelTransA U (pathPushforward b hsb htb p) q) :=
  (weilAdelicLevelBaseChange_transport b A preservation composition unitCoherence associativity
    comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA'
    MA' evaluationA' compatibility lam h i V ψ htor hsb htb hu hu'
    (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') U p q).symm

/-- The diagonal fixed-orbit pullback does not depend on the supplied path. -/
theorem weilAdelicLevelBaseChangeAlongPath_path_independent (U : Subgroup G)
    (p q : fiberFunctor s hs ≅ fiberFunctor t ht) :
    levelAlong U p = levelAlong U q := by
  funext x
  exact congrArg (fun e => e
    (levelBC s hs hsb htor hu hu' (hμfin := hμfin) (hμet := hμet)
      (hμfin' := hμfin') (hμet' := hμet') U x))
    (weilAdelicLevelTransport_path_independent preservation composition unitCoherence associativity
      comparison symmetry stability compatibility geo hA' geometryA' MA' evaluationA'
      (lamBC lam) h iBC V ψ htor hu' (hμfin := hμfin') (hμet := hμet') U p q)

/-- The diagonal pullback is injective for an arbitrary map of pointed bases. -/
theorem weilAdelicLevelBaseChangeAlongPath_injective (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Function.Injective (levelAlong U p) :=
  (levelTransb U p).injective.comp
    (weilAdelicLevelBaseChange_injective b A preservation composition unitCoherence associativity
      comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA'
      MA' evaluationA' compatibility lam h i V ψ s hs hsb htor hu hu'
      (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') U)

end Full

section Away
variable {m : ℕ} (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
variable (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  (hu' : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S', ⊤)))
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom]
  [hμfin' : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S' n.val).X.hom]
  [hμet' : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S' n.val).X.hom]

local notation "FrameA" => WeilPrimeToAdelicFrame preservation composition unitCoherence associativity
  comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ
local notation "Frameb" => WeilPrimeToAdelicFrame preservation composition unitCoherence associativity
  comparison symmetry stability hA' geometryA' MA' evaluationA' compatibility (lamBC lam) h iBC V ψ
local notation "frameBC" => weilPrimeToAdelicFrameBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hA'
  geometryA' MA' evaluationA' compatibility lam h i V ψ
local notation "transA" => weilPrimeToAdelicFrameTransport preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geo hA geometryA MA evaluationA lam
  hAway i V ψ htor hu (hμfin := hμfin) (hμet := hμet)
local notation "transb" => weilPrimeToAdelicFrameTransport preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geo hA' geometryA' MA' evaluationA'
  (lamBC lam) hAway iBC V ψ htor hu' (hμfin := hμfin') (hμet := hμet')

/-- Base change of actual away compatible frames commutes with transport along a pushed path. -/
theorem weilPrimeToAdelicFrameBaseChange_transport
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (eta : Frameb s hAway) :
    frameBC t hAway (transb p eta) =
      transA (pathPushforward b hsb htb p) (frameBC s hAway eta) := by
  apply Subtype.ext
  ext x
  exact rationalBaseChange_transport b hsb htb htor A (fun n => Nat.Coprime n m) hu hu' p (eta.1 x)

local notation "frameSquare" => weilPrimeToAdelicFrameBaseChange_transport b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA
  hA' geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb htb hAway hu hu'
  (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')

/-- The inverse frame comparisons give the pullback-oriented path square. -/
theorem weilPrimeToAdelicFrameBaseChange_symm_transport
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (eta : FrameA (s ≫ b) hAway) :
    (frameBC t hAway).symm (transA (pathPushforward b hsb htb p) eta) =
      transb p ((frameBC s hAway).symm eta) := by
  apply (frameBC t hAway).injective
  rw [Equiv.apply_symm_apply, frameSquare, Equiv.apply_symm_apply]

local notation "frameInvSquare" => weilPrimeToAdelicFrameBaseChange_symm_transport b A preservation
  composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA
  evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb htb hAway hu hu'
  (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')

/-- Actual away compatible-frame comparison along the diagonal: path transport, then base change. -/
def weilPrimeToAdelicFrameBaseChangeAlongPath (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Frameb s hAway ≃ FrameA (t ≫ b) hAway :=
  (transb p).trans (frameBC t hAway)

/-- The diagonal comparison also equals base change followed by pushed-path transport. -/
theorem weilPrimeToAdelicFrameBaseChangeAlongPath_apply
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (eta : Frameb s hAway) :
    weilPrimeToAdelicFrameBaseChangeAlongPath b A preservation composition unitCoherence associativity
        comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA'
        MA' evaluationA' compatibility lam h i V ψ htor hAway hu' p eta =
      transA (pathPushforward b hsb htb p) (frameBC s hAway eta) :=
  frameSquare p eta

local notation "G" => ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ
local notation "rightA" => weilPrimeToAdelicFrameRightAction preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ
local notation "rightb" => weilPrimeToAdelicFrameRightAction preservation composition unitCoherence
  associativity comparison symmetry stability hA' geometryA' MA' evaluationA' compatibility
  (lamBC lam) h iBC V ψ
local notation "monA" => weilPrimeToAdelicFrameMonodromyAction preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geo hA geometryA MA evaluationA lam hAway i V ψ
local notation "monb" => weilPrimeToAdelicFrameMonodromyAction preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geo hA' geometryA' MA' evaluationA'
  (lamBC lam) hAway iBC V ψ
local notation "commA" => weilPrimeToAdelicFrameActionsComm preservation composition unitCoherence associativity
  comparison symmetry stability compatibility geo hA geometryA MA evaluationA lam hAway i V ψ
local notation "commb" => weilPrimeToAdelicFrameActionsComm preservation composition unitCoherence associativity
  comparison symmetry stability compatibility geo hA' geometryA' MA' evaluationA' (lamBC lam) hAway iBC V ψ
local notation "LevelA" => WeilPrimeToAdelicLevel preservation composition unitCoherence associativity
  comparison symmetry stability compatibility geo hA geometryA MA evaluationA lam hAway i V ψ
local notation "Levelb" => WeilPrimeToAdelicLevel preservation composition unitCoherence associativity
  comparison symmetry stability compatibility geo hA' geometryA' MA' evaluationA' (lamBC lam) hAway iBC V ψ
local notation "levelBC" => weilPrimeToAdelicLevelBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA'
  MA' evaluationA' compatibility lam h i V ψ
local notation "levelTransA" => weilPrimeToAdelicLevelTransport preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geo hA geometryA MA evaluationA lam
  hAway i V ψ htor hu (hμfin := hμfin) (hμet := hμet)
local notation "levelTransb" => weilPrimeToAdelicLevelTransport preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geo hA' geometryA' MA' evaluationA'
  (lamBC lam) hAway iBC V ψ htor hu' (hμfin := hμfin') (hμet := hμet')

/-- The actual fixed-level pullback commutes with path transport; no representative is fixed. -/
theorem weilPrimeToAdelicLevelBaseChange_transport (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : LevelA (s ≫ b) hsb htor hu (hμfin := hμfin) (hμet := hμet) U) :
    levelBC t ht htb htor hAway hu hu' (hμfin := hμfin) (hμet := hμet)
        (hμfin' := hμfin') (hμet' := hμet') U
        (levelTransA U (pathPushforward b hsb htb p) q) =
      levelTransb U p
        (levelBC s hs hsb htor hAway hu hu' (hμfin := hμfin) (hμet := hμet)
          (hμfin' := hμfin') (hμet' := hμet') U q) := by
  let := rightA (s ≫ b) hAway
  let := rightA (t ≫ b) hAway
  let := rightb s hAway
  let := rightb t hAway
  let := monA (s ≫ b) hsb htor hu (hμfin := hμfin) (hμet := hμet)
  let := monA (t ≫ b) htb htor hu (hμfin := hμfin) (hμet := hμet)
  let := monb s hs htor hu' (hμfin := hμfin') (hμet := hμet')
  let := monb t ht htor hu' (hμfin := hμfin') (hμet := hμet')
  let := commA (s ≫ b) hsb htor hu (hμfin := hμfin) (hμet := hμet)
  let := commA (t ≫ b) htb htor hu (hμfin := hμfin) (hμet := hμet)
  let := commb s hs htor hu' (hμfin := hμfin') (hμet := hμet')
  let := commb t ht htor hu' (hμfin := hμfin') (hμet := hμet')
  apply Subtype.ext
  simp only [weilPrimeToAdelicLevelBaseChange, InvariantOrbit.pullback, weilPrimeToAdelicLevelTransport,
    InvariantOrbit.equiv, Equiv.symm, Equiv.coe_fn_mk, InvariantOrbit.map_val]
  induction q.1 using Quotient.inductionOn with
  | h eta => exact congrArg (RightOrbit.mk U) (frameInvSquare p eta)

/-- Diagonal pullback of a fixed compatible level: pointed pullback, then path transport. -/
def weilPrimeToAdelicLevelBaseChangeAlongPath (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    LevelA (s ≫ b) hsb htor hu (hμfin := hμfin) (hμet := hμet) U →
      Levelb t ht htor hu' (hμfin := hμfin') (hμet := hμet') U :=
  fun q => levelTransb U p
    (levelBC s hs hsb htor hAway hu hu' (hμfin := hμfin) (hμet := hμet)
      (hμfin' := hμfin') (hμet' := hμet') U q)

local notation "levelAlong" => weilPrimeToAdelicLevelBaseChangeAlongPath b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA
  hA' geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb hAway hu hu'
  (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')

/-- The other route for the diagonal fixed-level pullback uses the pushed path first. -/
theorem weilPrimeToAdelicLevelBaseChangeAlongPath_apply (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : LevelA (s ≫ b) hsb htor hu (hμfin := hμfin) (hμet := hμet) U) :
    levelAlong U p q =
      levelBC t ht htb htor hAway hu hu' (hμfin := hμfin) (hμet := hμet)
        (hμfin' := hμfin') (hμet' := hμet') U
        (levelTransA U (pathPushforward b hsb htb p) q) :=
  (weilPrimeToAdelicLevelBaseChange_transport b A preservation composition unitCoherence associativity
    comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA'
    MA' evaluationA' compatibility lam h i V ψ htor hsb htb hAway hu hu'
    (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') U p q).symm

/-- The diagonal fixed-orbit pullback does not depend on the supplied path. -/
theorem weilPrimeToAdelicLevelBaseChangeAlongPath_path_independent (U : Subgroup G)
    (p q : fiberFunctor s hs ≅ fiberFunctor t ht) :
    levelAlong U p = levelAlong U q := by
  funext x
  exact congrArg (fun e => e
    (levelBC s hs hsb htor hAway hu hu' (hμfin := hμfin) (hμet := hμet)
      (hμfin' := hμfin') (hμet' := hμet') U x))
    (weilPrimeToAdelicLevelTransport_path_independent preservation composition unitCoherence associativity
      comparison symmetry stability compatibility geo hA' geometryA' MA' evaluationA'
      (lamBC lam) hAway iBC V ψ htor hu' (hμfin := hμfin') (hμet := hμet') U p q)

/-- The diagonal pullback is injective for an arbitrary map of pointed bases. -/
theorem weilPrimeToAdelicLevelBaseChangeAlongPath_injective (U : Subgroup G)
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Function.Injective (levelAlong U p) :=
  (levelTransb U p).injective.comp
    (weilPrimeToAdelicLevelBaseChange_injective b A preservation composition unitCoherence associativity
      comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA'
      MA' evaluationA' compatibility lam h i V ψ s hs hsb htor hAway hu hu'
      (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') U)

end Away

end Langlands.AbelianScheme.Tate
