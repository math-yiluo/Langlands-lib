import Langlands.AbelianScheme.Tate.WeilPathBaseChange
import Langlands.AbelianScheme.Tate.WeilCompactOpenLevelBaseChange
import Langlands.AbelianScheme.Tate.WeilCompactOpenLevelTransport

/-! # Base change and geometric-point comparison of actual Weil level towers -/

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

local notation "LevelIndex" => FiniteAdelicScalarExtensionLevel D V ψ
local notation "towerA" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence
  associativity comparison symmetry stability compatibility hA geometryA MA evaluationA lam
  h i V ψ
local notation "towerb" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence
  associativity comparison symmetry stability compatibility hA' geometryA' MA' evaluationA'
  (lamBC lam) h iBC V ψ
local notation "TAs" => towerA (s ≫ b) hsb htor hu (hμfin := hμfin) (hμet := hμet)
local notation "TAt" => towerA (t ≫ b) htb htor hu (hμfin := hμfin) (hμet := hμet)
local notation "Tbs" => towerb s hs htor hu' (hμfin := hμfin') (hμet := hμet')
local notation "Tbt" => towerb t ht htor hu' (hμfin := hμfin') (hμet := hμet')
local notation "transA" => weilAdelicCompactOpenLevelTransport preservation composition
  unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA
  evaluationA lam h i V ψ htor hu (hμfin := hμfin) (hμet := hμet)
local notation "transb" => weilAdelicCompactOpenLevelTransport preservation composition
  unitCoherence associativity comparison symmetry stability compatibility hA' geometryA' MA'
  evaluationA' (lamBC lam) h iBC V ψ htor hu' (hμfin := hμfin') (hμet := hμet')
local notation "pull" => weilAdelicCompactOpenLevelBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA
  evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ
local notation "pulls" => pull s hs hsb htor hu hu'
  (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')
local notation "pullt" => pull t ht htb htor hu hu'
  (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')

/-- The actual base-change/path square commutes as an equality of tower morphisms. -/
theorem weilAdelicCompactOpenLevelBaseChange_transport
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (transA (pathPushforward b hsb htb p)).hom ≫ pullt =
      pulls ≫ (transb p).hom := by
  ext K q
  exact weilAdelicLevelBaseChange_transport b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA geometryA MA evaluationA hA'
    geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb htb hu hu'
    (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')
    K.toSubgroup p q

/-- Diagonal pullback of the actual compact-open tower, natural in every transporter. -/
def weilAdelicCompactOpenLevelBaseChangeAlongPath
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) : TAs ⟶ Tbt :=
  pulls ≫ (transb p).hom

local notation "diagonal" => weilAdelicCompactOpenLevelBaseChangeAlongPath b A preservation
  composition unitCoherence associativity comparison symmetry stability universality hA geometryA
  MA evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb hu hu'
  (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')

/-- Each component is the constructed diagonal pullback of fixed compatible levels. -/
@[simp] theorem weilAdelicCompactOpenLevelBaseChangeAlongPath_app
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (K : LevelIndex) (q : (TAs).obj K) :
    (diagonal p).app K q =
      weilAdelicLevelBaseChangeAlongPath b A preservation composition unitCoherence associativity
        comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA'
        MA' evaluationA' compatibility lam h i V ψ htor hsb hu hu'
        (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')
        K.toSubgroup p q := rfl

/-- The alternate route transports along the pushed path before pointed pullback. -/
theorem weilAdelicCompactOpenLevelBaseChangeAlongPath_eq
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    diagonal p = (transA (pathPushforward b hsb htb p)).hom ≫ pullt :=
  (weilAdelicCompactOpenLevelBaseChange_transport b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA geometryA MA evaluationA hA'
    geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb htb hu hu'
    (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') p).symm

/-- Path independence is equality of the entire natural transformation. -/
theorem weilAdelicCompactOpenLevelBaseChangeAlongPath_path_independent
    (p q : fiberFunctor s hs ≅ fiberFunctor t ht) :
    diagonal p = diagonal q := by
  ext K x
  exact congrArg (fun f => f x)
    (weilAdelicLevelBaseChangeAlongPath_path_independent b A preservation composition unitCoherence
      associativity comparison symmetry stability universality hA geometryA MA evaluationA hA'
      geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb hu hu'
      (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') K.toSubgroup p q)

/-- Every diagonal component is injective. -/
theorem weilAdelicCompactOpenLevelBaseChangeAlongPath_injective
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (K : LevelIndex) :
    Function.Injective ((diagonal p).app K) :=
  weilAdelicLevelBaseChangeAlongPath_injective b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA geometryA MA evaluationA hA'
    geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb hu hu'
    (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') K.toSubgroup p

/-- Inclusions and both compact-open Hecke legs are covered by this transporter square. -/
theorem weilAdelicCompactOpenLevelBaseChangeAlongPath_arrow
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) {K L : LevelIndex} (f : K ⟶ L)
    (q : (TAs).obj K) :
    (diagonal p).app L ((TAs).map f q) = (Tbt).map f ((diagonal p).app K q) :=
  (diagonal p).naturality_apply f q

section Geometric
variable [ConnectedSpace S'] [IsLocallyNoetherian S']
  [IsAlgClosed Ω] [IsAlgClosed Ω']

/-- Canonical pullback between arbitrary geometric-point presentations of the two towers. -/
def weilAdelicCompactOpenLevelGeometricBaseChange : TAs ⟶ Tbt :=
  diagonal (Classical.choice (geometricPathExists s t hs ht))

local notation "geometricPull" => weilAdelicCompactOpenLevelGeometricBaseChange b A preservation
  composition unitCoherence associativity comparison symmetry stability universality hA geometryA
  MA evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb hu hu'
  (s := s) (t := t) (hs := hs) (ht := ht)
  (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')

/-- Any supplied path computes the same canonical tower pullback. -/
theorem weilAdelicCompactOpenLevelGeometricBaseChange_eq_path
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    geometricPull = diagonal p :=
  weilAdelicCompactOpenLevelBaseChangeAlongPath_path_independent b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA geometryA MA
    evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb hu hu'
    (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') _ p

/-- Canonical pullback is pointed pullback followed by canonical new-base point comparison. -/
theorem weilAdelicCompactOpenLevelGeometricBaseChange_eq_transport :
    geometricPull = pulls ≫
      (weilAdelicCompactOpenLevelGeometricTransport preservation composition unitCoherence associativity
        comparison symmetry stability compatibility hA' geometryA' MA' evaluationA' (lamBC lam)
        h iBC V ψ htor hu' (hμfin := hμfin') (hμet := hμet') s t hs ht).hom := rfl

/-- Canonical tower pullback has injective components. -/
theorem weilAdelicCompactOpenLevelGeometricBaseChange_injective (K : LevelIndex) :
    Function.Injective ((geometricPull).app K) :=
  weilAdelicCompactOpenLevelBaseChangeAlongPath_injective b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA geometryA MA
    evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb hu hu'
    (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') _ K

variable [ConnectedSpace S] [IsLocallyNoetherian S]

/-- Pointed pullback commutes with the canonical comparisons of geometric points. -/
theorem weilAdelicCompactOpenLevelGeometricBaseChange_eq_pushed_transport :
    geometricPull =
      (weilAdelicCompactOpenLevelGeometricTransport preservation composition unitCoherence associativity
        comparison symmetry stability compatibility hA geometryA MA evaluationA lam h i V ψ
        htor hu (hμfin := hμfin) (hμet := hμet) (s ≫ b) (t ≫ b) hsb htb).hom ≫ pullt := by
  let p := Classical.choice (geometricPathExists s t hs ht)
  rw [weilAdelicCompactOpenLevelGeometricBaseChange_eq_path b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA geometryA MA
    evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb hu hu'
    (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') p]
  rw [weilAdelicCompactOpenLevelBaseChangeAlongPath_eq b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA geometryA MA
    evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb htb hu hu'
    (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') p]
  rw [weilAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence
    associativity comparison symmetry stability compatibility hA geometryA MA evaluationA lam
    h i V ψ htor hu (hμfin := hμfin) (hμet := hμet) (pathPushforward b hsb htb p)]

end Geometric
end Full

section Away
variable {m : ℕ} (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

variable (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  (hu' : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S', ⊤)))
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom]
  [hμfin' : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S' n.val).X.hom]
  [hμet' : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S' n.val).X.hom]

local notation "LevelIndex" => PrimeToScalarExtensionLevel D V ψ m
local notation "towerA" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence
  associativity comparison symmetry stability compatibility hA geometryA MA evaluationA lam
  hAway i V ψ
local notation "towerb" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence
  associativity comparison symmetry stability compatibility hA' geometryA' MA' evaluationA'
  (lamBC lam) hAway iBC V ψ
local notation "TAs" => towerA (s ≫ b) hsb htor hu (hμfin := hμfin) (hμet := hμet)
local notation "TAt" => towerA (t ≫ b) htb htor hu (hμfin := hμfin) (hμet := hμet)
local notation "Tbs" => towerb s hs htor hu' (hμfin := hμfin') (hμet := hμet')
local notation "Tbt" => towerb t ht htor hu' (hμfin := hμfin') (hμet := hμet')
local notation "transA" => weilPrimeToAdelicCompactOpenLevelTransport preservation composition
  unitCoherence associativity comparison symmetry stability compatibility hA geometryA MA
  evaluationA lam hAway i V ψ htor hu (hμfin := hμfin) (hμet := hμet)
local notation "transb" => weilPrimeToAdelicCompactOpenLevelTransport preservation composition
  unitCoherence associativity comparison symmetry stability compatibility hA' geometryA' MA'
  evaluationA' (lamBC lam) hAway iBC V ψ htor hu' (hμfin := hμfin') (hμet := hμet')
local notation "pull" => weilPrimeToAdelicCompactOpenLevelBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA
  evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ
local notation "pulls" => pull s hs hsb htor hAway hu hu'
  (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')
local notation "pullt" => pull t ht htb htor hAway hu hu'
  (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')

/-- The actual base-change/path square commutes as an equality of tower morphisms. -/
theorem weilPrimeToAdelicCompactOpenLevelBaseChange_transport
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    (transA (pathPushforward b hsb htb p)).hom ≫ pullt =
      pulls ≫ (transb p).hom := by
  ext K q
  exact weilPrimeToAdelicLevelBaseChange_transport b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA geometryA MA evaluationA hA'
    geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb htb hAway hu hu'
    (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')
    K.toSubgroup p q

/-- Diagonal pullback of the actual compact-open tower, natural in every transporter. -/
def weilPrimeToAdelicCompactOpenLevelBaseChangeAlongPath
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) : TAs ⟶ Tbt :=
  pulls ≫ (transb p).hom

local notation "diagonal" => weilPrimeToAdelicCompactOpenLevelBaseChangeAlongPath b A preservation
  composition unitCoherence associativity comparison symmetry stability universality hA geometryA
  MA evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb hAway hu hu'
  (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')

/-- Each component is the constructed diagonal pullback of fixed compatible levels. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelBaseChangeAlongPath_app
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (K : LevelIndex) (q : (TAs).obj K) :
    (diagonal p).app K q =
      weilPrimeToAdelicLevelBaseChangeAlongPath b A preservation composition unitCoherence associativity
        comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA'
        MA' evaluationA' compatibility lam h i V ψ htor hsb hAway hu hu'
        (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')
        K.toSubgroup p q := rfl

/-- The alternate route transports along the pushed path before pointed pullback. -/
theorem weilPrimeToAdelicCompactOpenLevelBaseChangeAlongPath_eq
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    diagonal p = (transA (pathPushforward b hsb htb p)).hom ≫ pullt :=
  (weilPrimeToAdelicCompactOpenLevelBaseChange_transport b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA geometryA MA evaluationA hA'
    geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb htb hAway hu hu'
    (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') p).symm

/-- Path independence is equality of the entire natural transformation. -/
theorem weilPrimeToAdelicCompactOpenLevelBaseChangeAlongPath_path_independent
    (p q : fiberFunctor s hs ≅ fiberFunctor t ht) :
    diagonal p = diagonal q := by
  ext K x
  exact congrArg (fun f => f x)
    (weilPrimeToAdelicLevelBaseChangeAlongPath_path_independent b A preservation composition unitCoherence
      associativity comparison symmetry stability universality hA geometryA MA evaluationA hA'
      geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb hAway hu hu'
      (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') K.toSubgroup p q)

/-- Every diagonal component is injective. -/
theorem weilPrimeToAdelicCompactOpenLevelBaseChangeAlongPath_injective
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (K : LevelIndex) :
    Function.Injective ((diagonal p).app K) :=
  weilPrimeToAdelicLevelBaseChangeAlongPath_injective b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA geometryA MA evaluationA hA'
    geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb hAway hu hu'
    (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') K.toSubgroup p

/-- Inclusions and both compact-open Hecke legs are covered by this transporter square. -/
theorem weilPrimeToAdelicCompactOpenLevelBaseChangeAlongPath_arrow
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) {K L : LevelIndex} (f : K ⟶ L)
    (q : (TAs).obj K) :
    (diagonal p).app L ((TAs).map f q) = (Tbt).map f ((diagonal p).app K q) :=
  (diagonal p).naturality_apply f q

section Geometric
variable [ConnectedSpace S'] [IsLocallyNoetherian S']
  [IsAlgClosed Ω] [IsAlgClosed Ω']

/-- Canonical pullback between arbitrary geometric-point presentations of the two towers. -/
def weilPrimeToAdelicCompactOpenLevelGeometricBaseChange : TAs ⟶ Tbt :=
  diagonal (Classical.choice (geometricPathExists s t hs ht))

local notation "geometricPull" => weilPrimeToAdelicCompactOpenLevelGeometricBaseChange b A preservation
  composition unitCoherence associativity comparison symmetry stability universality hA geometryA
  MA evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb hAway hu hu'
  (s := s) (t := t) (hs := hs) (ht := ht)
  (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')

/-- Any supplied path computes the same canonical tower pullback. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricBaseChange_eq_path
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    geometricPull = diagonal p :=
  weilPrimeToAdelicCompactOpenLevelBaseChangeAlongPath_path_independent b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA geometryA MA
    evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb hAway hu hu'
    (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') _ p

/-- Canonical pullback is pointed pullback followed by canonical new-base point comparison. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricBaseChange_eq_transport :
    geometricPull = pulls ≫
      (weilPrimeToAdelicCompactOpenLevelGeometricTransport preservation composition unitCoherence associativity
        comparison symmetry stability compatibility hA' geometryA' MA' evaluationA' (lamBC lam)
        hAway iBC V ψ htor hu' (hμfin := hμfin') (hμet := hμet') s t hs ht).hom := rfl

/-- Canonical tower pullback has injective components. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricBaseChange_injective (K : LevelIndex) :
    Function.Injective ((geometricPull).app K) :=
  weilPrimeToAdelicCompactOpenLevelBaseChangeAlongPath_injective b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA geometryA MA
    evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb hAway hu hu'
    (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') _ K

variable [ConnectedSpace S] [IsLocallyNoetherian S]

/-- Pointed pullback commutes with the canonical comparisons of geometric points. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricBaseChange_eq_pushed_transport :
    geometricPull =
      (weilPrimeToAdelicCompactOpenLevelGeometricTransport preservation composition unitCoherence associativity
        comparison symmetry stability compatibility hA geometryA MA evaluationA lam hAway i V ψ
        htor hu (hμfin := hμfin) (hμet := hμet) (s ≫ b) (t ≫ b) hsb htb).hom ≫ pullt := by
  let p := Classical.choice (geometricPathExists s t hs ht)
  rw [weilPrimeToAdelicCompactOpenLevelGeometricBaseChange_eq_path b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA geometryA MA
    evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb hAway hu hu'
    (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') p]
  rw [weilPrimeToAdelicCompactOpenLevelBaseChangeAlongPath_eq b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA geometryA MA
    evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ htor hsb htb hAway hu hu'
    (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') p]
  rw [weilPrimeToAdelicCompactOpenLevelGeometricTransport_eq_path preservation composition unitCoherence
    associativity comparison symmetry stability compatibility hA geometryA MA evaluationA lam
    hAway i V ψ htor hu (hμfin := hμfin) (hμet := hμet) (pathPushforward b hsb htb p)]

end Geometric
end Away

end Langlands.AbelianScheme.Tate
