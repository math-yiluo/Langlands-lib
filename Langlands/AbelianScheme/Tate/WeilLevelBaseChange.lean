import Langlands.AbelianScheme.Tate.WeilFrameBaseChange
import Langlands.AbelianScheme.Tate.WeilFrameMonodromy
import Langlands.AbelianScheme.Tate.WeilPrimeToFrameMonodromy
import Langlands.AbelianScheme.Tate.WeilGeometricTransportProof
import Langlands.AbelianScheme.Tate.PointedMonodromyBaseChangeProof
import Langlands.AbelianScheme.Tate.PointedFrameOrbitPullback

/-! # Pointed pullback of actual Weil-compatible fixed level orbits -/

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
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S')

set_option quotPrecheck false in
local notation "iBC" => (AbelianScheme.rationalBaseChangeEnd b A).comp i


variable (ht : ∀ Y : Cover S', Finite (Fiber s Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (s ≫ b) Y))
  (htor : TorsionFiniteEtaleStatement.{u})

local notation "geo" => rationalWeilGeometricTransport
local notation "alpha" => fundamentalGroupMap b s (s ≫ b) rfl ht hs

section Full
variable (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  (hu' : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S', ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom]
  [hμfin' : ∀ n : Index (fun _ => True), IsFinite (mu S' n.val).X.hom]
  [hμet' : ∀ n : Index (fun _ => True), Etale (mu S' n.val).X.hom]
local notation "FrameA" => WeilAdelicFrame preservation composition unitCoherence associativity
  comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ (s ≫ b)
local notation "Frameb" => WeilAdelicFrame preservation composition unitCoherence associativity
  comparison symmetry stability hA' geometryA' MA' evaluationA' compatibility (lamBC lam) h
  iBC V ψ s
local notation "rightA" => weilAdelicFrameRightAction preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h
  i V ψ (s ≫ b)
local notation "rightb" => weilAdelicFrameRightAction preservation composition unitCoherence
  associativity comparison symmetry stability hA' geometryA' MA' evaluationA' compatibility
  (lamBC lam) h iBC V ψ s

local notation "frameBC" => weilAdelicFrameBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA' MA'
  evaluationA' compatibility lam h i V ψ s
local notation "frameRight" => weilAdelicFrameBaseChange_right b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA' MA'
  evaluationA' compatibility lam h i V ψ s
local notation "orbitBC" => weilAdelicFrameRightOrbitBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA hA'
  geometryA' MA' evaluationA' compatibility lam h i V ψ s
local notation "monA" => weilAdelicFrameMonodromyAction preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geo hA geometryA MA evaluationA lam h i V ψ
  (s ≫ b) hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "commA" => weilAdelicFrameActionsComm preservation composition unitCoherence associativity
  comparison symmetry stability compatibility geo hA geometryA MA evaluationA lam h i V ψ (s ≫ b) hs htor
  hu (hμfin := hμfin) (hμet := hμet)
local notation "LevelA" => WeilAdelicLevel preservation composition unitCoherence associativity
  comparison symmetry stability compatibility geo hA geometryA MA evaluationA lam h i V ψ (s ≫ b) hs htor
  hu (hμfin := hμfin) (hμet := hμet)
local notation "monb" => weilAdelicFrameMonodromyAction preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geo hA' geometryA' MA' evaluationA' (lamBC
  lam) h iBC V ψ s ht htor hu' (hμfin := hμfin') (hμet := hμet')
local notation "commb" => weilAdelicFrameActionsComm preservation composition unitCoherence associativity
  comparison symmetry stability compatibility geo hA' geometryA' MA' evaluationA' (lamBC lam) h iBC V ψ s
  ht htor hu' (hμfin := hμfin') (hμet := hμet')
local notation "Levelb" => WeilAdelicLevel preservation composition unitCoherence associativity
  comparison symmetry stability compatibility geo hA' geometryA' MA' evaluationA' (lamBC lam) h iBC V ψ s
  ht htor hu' (hμfin := hμfin') (hμet := hμet')

/-- The compatible-frame comparison intertwines actual monodromy by the
fundamental-group map of pointed ground base change. -/
theorem weilAdelicFrameBaseChange_monodromy :
    letI := monb
    letI := monA
    ∀ (g : FundamentalGroup s ht) (eta : Frameb),
      frameBC (g • eta) = alpha g • frameBC eta := by
  intro g eta
  apply Subtype.ext
  ext x
  exact rationalBaseChange_monodromy b s ht hs htor A (fun _ => True) hu hu' g (eta.1 x)

local notation "frameMon" => weilAdelicFrameBaseChange_monodromy b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA hA'
  geometryA' MA' evaluationA' compatibility lam h i V ψ s ht hs htor hu hu' (hμfin := hμfin) (hμet :=
  hμet) (hμfin' := hμfin') (hμet' := hμet')

/-- Pull back geometrically fixed right orbits of actual compatible frames.
Fixedness is imposed on orbit classes, not representatives. -/
def weilAdelicLevelBaseChange
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)) :
    LevelA U → Levelb U := by
  let := rightb
  let := rightA
  let := monb
  let := monA
  let := commb
  let := commA
  exact InvariantOrbit.pullback U alpha frameBC frameRight frameMon

local notation "levelBC" => weilAdelicLevelBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA' MA'
  evaluationA' compatibility lam h i V ψ s ht hs htor hu hu' (hμfin := hμfin) (hμet := hμet) (hμfin' :=
  hμfin') (hμet' := hμet')

/-- On underlying classes, pointed level pullback is the inverse frame-orbit comparison. -/
@[simp] theorem weilAdelicLevelBaseChange_val
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)) (q : LevelA U) :
    (levelBC U q).1 = (orbitBC U).symm q.1 := rfl

/-- Pullback is injective without surjectivity of the map on fundamental groups. -/
theorem weilAdelicLevelBaseChange_injective
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)) :
    Function.Injective (levelBC U) := by
  intro q r heq
  apply Subtype.ext
  exact (orbitBC U).symm.injective (congrArg Subtype.val heq)

/-- Pointed level pullback commutes with every allowed Hecke translation. -/
theorem weilAdelicLevelBaseChange_translate
    {U U' : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)}
    (g : ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') (q : LevelA U) :
    letI := rightb
    letI := rightA
    letI := monb
    letI := monA
    letI := commb
    letI := commA
    levelBC U' (InvariantOrbit.translate g hg q) =
      InvariantOrbit.translate g hg (levelBC U q) := by
  let := rightb
  let := rightA
  let := monb
  let := monA
  let := commb
  let := commA
  exact InvariantOrbit.pullback_translate alpha frameBC frameRight frameMon g hg q

/-- Forgetting finer level structure commutes with pointed pullback. -/
theorem weilAdelicLevelBaseChange_forget
    {U U' : Subgroup (ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ)} (hU : U ≤ U')
    (q : LevelA U) :
    letI := rightb
    letI := rightA
    letI := monb
    letI := monA
    letI := commb
    letI := commA
    levelBC U' (InvariantOrbit.forget hU q) = InvariantOrbit.forget hU (levelBC U q) := by
  exact weilAdelicLevelBaseChange_translate b A preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ s ht hs htor hu hu' (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') 1 _ q

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
  comparison symmetry stability hA geometryA MA evaluationA compatibility lam h i V ψ (s ≫ b) hAway
local notation "Frameb" => WeilPrimeToAdelicFrame preservation composition unitCoherence associativity
  comparison symmetry stability hA' geometryA' MA' evaluationA' compatibility (lamBC lam) h
  iBC V ψ s hAway
local notation "rightA" => weilPrimeToAdelicFrameRightAction preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility lam h
  i V ψ (s ≫ b) hAway
local notation "rightb" => weilPrimeToAdelicFrameRightAction preservation composition unitCoherence
  associativity comparison symmetry stability hA' geometryA' MA' evaluationA' compatibility
  (lamBC lam) h iBC V ψ s hAway

local notation "frameBC" => weilPrimeToAdelicFrameBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA' MA'
  evaluationA' compatibility lam h i V ψ s hAway
local notation "frameRight" => weilPrimeToAdelicFrameBaseChange_right b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA hA'
  geometryA' MA' evaluationA' compatibility lam h i V ψ s hAway
local notation "orbitBC" => weilPrimeToAdelicFrameRightOrbitBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA hA'
  geometryA' MA' evaluationA' compatibility lam h i V ψ s hAway
local notation "monA" => weilPrimeToAdelicFrameMonodromyAction preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geo hA geometryA MA evaluationA lam hAway i V
  ψ (s ≫ b) hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "commA" => weilPrimeToAdelicFrameActionsComm preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geo hA geometryA MA evaluationA lam hAway i V
  ψ (s ≫ b) hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "LevelA" => WeilPrimeToAdelicLevel preservation composition unitCoherence associativity
  comparison symmetry stability compatibility geo hA geometryA MA evaluationA lam hAway i V ψ (s ≫ b) hs
  htor hu (hμfin := hμfin) (hμet := hμet)
local notation "monb" => weilPrimeToAdelicFrameMonodromyAction preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geo hA' geometryA' MA' evaluationA' (lamBC
  lam) hAway iBC V ψ s ht htor hu' (hμfin := hμfin') (hμet := hμet')
local notation "commb" => weilPrimeToAdelicFrameActionsComm preservation composition unitCoherence
  associativity comparison symmetry stability compatibility geo hA' geometryA' MA' evaluationA' (lamBC
  lam) hAway iBC V ψ s ht htor hu' (hμfin := hμfin') (hμet := hμet')
local notation "Levelb" => WeilPrimeToAdelicLevel preservation composition unitCoherence associativity
  comparison symmetry stability compatibility geo hA' geometryA' MA' evaluationA' (lamBC lam) hAway iBC V
  ψ s ht htor hu' (hμfin := hμfin') (hμet := hμet')

/-- The compatible-frame comparison intertwines actual monodromy by the
fundamental-group map of pointed ground base change. -/
theorem weilPrimeToAdelicFrameBaseChange_monodromy :
    letI := monb
    letI := monA
    ∀ (g : FundamentalGroup s ht) (eta : Frameb),
      frameBC (g • eta) = alpha g • frameBC eta := by
  intro g eta
  apply Subtype.ext
  ext x
  exact rationalBaseChange_monodromy b s ht hs htor A (fun n => Nat.Coprime n m) hu hu' g (eta.1 x)

local notation "frameMon" => weilPrimeToAdelicFrameBaseChange_monodromy b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA hA'
  geometryA' MA' evaluationA' compatibility lam h i V ψ s ht hs htor hAway hu hu' (hμfin := hμfin) (hμet
  := hμet) (hμfin' := hμfin') (hμet' := hμet')

/-- Pull back geometrically fixed right orbits of actual compatible frames.
Fixedness is imposed on orbit classes, not representatives. -/
def weilPrimeToAdelicLevelBaseChange
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)) :
    LevelA U → Levelb U := by
  let := rightb
  let := rightA
  let := monb
  let := monA
  let := commb
  let := commA
  exact InvariantOrbit.pullback U alpha frameBC frameRight frameMon

local notation "levelBC" => weilPrimeToAdelicLevelBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA' MA'
  evaluationA' compatibility lam h i V ψ s ht hs htor hAway hu hu' (hμfin := hμfin) (hμet := hμet)
  (hμfin' := hμfin') (hμet' := hμet')

/-- On underlying classes, pointed level pullback is the inverse frame-orbit comparison. -/
@[simp] theorem weilPrimeToAdelicLevelBaseChange_val
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)) (q : LevelA U) :
    (levelBC U q).1 = (orbitBC U).symm q.1 := rfl

/-- Pullback is injective without surjectivity of the map on fundamental groups. -/
theorem weilPrimeToAdelicLevelBaseChange_injective
    (U : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)) :
    Function.Injective (levelBC U) := by
  intro q r heq
  apply Subtype.ext
  exact (orbitBC U).symm.injective (congrArg Subtype.val heq)

/-- Pointed level pullback commutes with every allowed Hecke translation. -/
theorem weilPrimeToAdelicLevelBaseChange_translate
    {U U' : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)}
    (g : ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)
    (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') (q : LevelA U) :
    letI := rightb
    letI := rightA
    letI := monb
    letI := monA
    letI := commb
    letI := commA
    levelBC U' (InvariantOrbit.translate g hg q) =
      InvariantOrbit.translate g hg (levelBC U q) := by
  let := rightb
  let := rightA
  let := monb
  let := monA
  let := commb
  let := commA
  exact InvariantOrbit.pullback_translate alpha frameBC frameRight frameMon g hg q

/-- Forgetting finer level structure commutes with pointed pullback. -/
theorem weilPrimeToAdelicLevelBaseChange_forget
    {U U' : Subgroup (ScalarExtensionSimilitudes D V (Global.PrimeToFiniteAdeles m) ψ)} (hU : U ≤ U')
    (q : LevelA U) :
    letI := rightb
    letI := rightA
    letI := monb
    letI := monA
    letI := commb
    letI := commA
    levelBC U' (InvariantOrbit.forget hU q) = InvariantOrbit.forget hU (levelBC U q) := by
  exact weilPrimeToAdelicLevelBaseChange_translate b A preservation composition unitCoherence associativity comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ s ht hs htor hAway hu hu' (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') 1 _ q

end Away

end Langlands.AbelianScheme.Tate
