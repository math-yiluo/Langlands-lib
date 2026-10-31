import Langlands.AbelianScheme.Tate.WeilCompactOpenLevels
import Langlands.AbelianScheme.Tate.WeilLevelBaseChange
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

local notation "LevelIndex" => FiniteAdelicScalarExtensionLevel D V ψ
local notation "TowerA" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity
  comparison symmetry stability compatibility hA geometryA MA evaluationA lam h
  i V ψ (s ≫ b) hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "Towerb" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity
  comparison symmetry stability compatibility hA' geometryA' MA' evaluationA' (lamBC lam)
  h iBC V ψ s ht htor hu' (hμfin := hμfin') (hμet := hμet')
local notation "levelBC" => weilAdelicLevelBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA
  hA' geometryA' MA' evaluationA' compatibility lam h i V ψ s ht hs htor  hu hu'
  (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')

/-- Pointed pullback of actual Weil-compatible levels is natural in every
compact-open transporter arrow. -/
def weilAdelicCompactOpenLevelBaseChange : TowerA ⟶ Towerb where
  app K := TypeCat.ofHom (levelBC K.toSubgroup)
  naturality {K L} f := by
    ext q
    exact weilAdelicLevelBaseChange_translate b A preservation composition unitCoherence associativity
      comparison symmetry stability universality hA geometryA MA evaluationA hA'
      geometryA' MA' evaluationA' compatibility lam h i V ψ s ht hs htor  hu hu'
      (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')
      f.element f.respects q

local notation "Pullback" => weilAdelicCompactOpenLevelBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA
  hA' geometryA' MA' evaluationA' compatibility lam h i V ψ s ht hs htor  hu hu'
  (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')

/-- Each component is the existing actual pointed fixed-level pullback. -/
@[simp] theorem weilAdelicCompactOpenLevelBaseChange_app (K : LevelIndex) (q : (TowerA).obj K) :
    (Pullback).app K q = levelBC K.toSubgroup q := rfl

/-- Every component is injective; no surjectivity of the fundamental-group map
is assumed. -/
theorem weilAdelicCompactOpenLevelBaseChange_injective (K : LevelIndex) :
    Function.Injective ((Pullback).app K) :=
  weilAdelicLevelBaseChange_injective b A preservation composition unitCoherence associativity
    comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA'
    MA' evaluationA' compatibility lam h i V ψ s ht hs htor  hu hu'
    (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') K.toSubgroup

/-- On orbit values, pullback uses the inverse compatible-frame comparison. -/
@[simp] theorem weilAdelicCompactOpenLevelBaseChange_val (K : LevelIndex) (q : (TowerA).obj K) :
    ((Pullback).app K q).val =
      (weilAdelicFrameRightOrbitBaseChange b A preservation composition unitCoherence associativity comparison symmetry
        stability universality hA geometryA MA evaluationA hA' geometryA' MA' evaluationA'
        compatibility lam h i V ψ s  K.toSubgroup).symm q.val := rfl

/-- The naturality square also holds on each individual level class. -/
theorem weilAdelicCompactOpenLevelBaseChange_arrow {K L : LevelIndex} (f : K ⟶ L) (q : (TowerA).obj K) :
    (Pullback).app L ((TowerA).map f q) =
      (Towerb).map f ((Pullback).app K q) :=
  (Pullback).naturality_apply f q

section Hecke
variable [Module.Finite ℚ V]

/-- The first compact-open Hecke leg commutes with pointed pullback. -/
theorem weilAdelicCompactOpenLevelBaseChange_heckeLeft (K L : LevelIndex)
    (g : ScalarExtensionSimilitudePoints D V (Global.FiniteAdeles ℚ) ψ) (q : (TowerA).obj (Langlands.Shimura.CompactOpenLevel.heckeLevel K L g)) :
    (Pullback).app K ((TowerA).map (Langlands.Shimura.CompactOpenLevel.heckeLeft K L g) q) =
      (Towerb).map (Langlands.Shimura.CompactOpenLevel.heckeLeft K L g)
        ((Pullback).app (Langlands.Shimura.CompactOpenLevel.heckeLevel K L g) q) :=
  (Pullback).naturality_apply _ q

/-- The second compact-open Hecke leg commutes with pointed pullback. -/
theorem weilAdelicCompactOpenLevelBaseChange_heckeRight (K L : LevelIndex)
    (g : ScalarExtensionSimilitudePoints D V (Global.FiniteAdeles ℚ) ψ) (q : (TowerA).obj (Langlands.Shimura.CompactOpenLevel.heckeLevel K L g)) :
    (Pullback).app L ((TowerA).map (Langlands.Shimura.CompactOpenLevel.heckeRight K L g) q) =
      (Towerb).map (Langlands.Shimura.CompactOpenLevel.heckeRight K L g)
        ((Pullback).app (Langlands.Shimura.CompactOpenLevel.heckeLevel K L g) q) :=
  (Pullback).naturality_apply _ q

end Hecke

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
local notation "TowerA" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence associativity
  comparison symmetry stability compatibility hA geometryA MA evaluationA lam hAway
  i V ψ (s ≫ b) hs htor hu (hμfin := hμfin) (hμet := hμet)
local notation "Towerb" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence associativity
  comparison symmetry stability compatibility hA' geometryA' MA' evaluationA' (lamBC lam)
  hAway iBC V ψ s ht htor hu' (hμfin := hμfin') (hμet := hμet')
local notation "levelBC" => weilPrimeToAdelicLevelBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA
  hA' geometryA' MA' evaluationA' compatibility lam h i V ψ s ht hs htor hAway hu hu'
  (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')

/-- Pointed pullback of actual Weil-compatible levels is natural in every
compact-open transporter arrow. -/
def weilPrimeToAdelicCompactOpenLevelBaseChange : TowerA ⟶ Towerb where
  app K := TypeCat.ofHom (levelBC K.toSubgroup)
  naturality {K L} f := by
    ext q
    exact weilPrimeToAdelicLevelBaseChange_translate b A preservation composition unitCoherence associativity
      comparison symmetry stability universality hA geometryA MA evaluationA hA'
      geometryA' MA' evaluationA' compatibility lam h i V ψ s ht hs htor hAway hu hu'
      (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')
      f.element f.respects q

local notation "Pullback" => weilPrimeToAdelicCompactOpenLevelBaseChange b A preservation composition unitCoherence
  associativity comparison symmetry stability universality hA geometryA MA evaluationA
  hA' geometryA' MA' evaluationA' compatibility lam h i V ψ s ht hs htor hAway hu hu'
  (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet')

/-- Each component is the existing actual pointed fixed-level pullback. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelBaseChange_app (K : LevelIndex) (q : (TowerA).obj K) :
    (Pullback).app K q = levelBC K.toSubgroup q := rfl

/-- Every component is injective; no surjectivity of the fundamental-group map
is assumed. -/
theorem weilPrimeToAdelicCompactOpenLevelBaseChange_injective (K : LevelIndex) :
    Function.Injective ((Pullback).app K) :=
  weilPrimeToAdelicLevelBaseChange_injective b A preservation composition unitCoherence associativity
    comparison symmetry stability universality hA geometryA MA evaluationA hA' geometryA'
    MA' evaluationA' compatibility lam h i V ψ s ht hs htor hAway hu hu'
    (hμfin := hμfin) (hμet := hμet) (hμfin' := hμfin') (hμet' := hμet') K.toSubgroup

/-- On orbit values, pullback uses the inverse compatible-frame comparison. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelBaseChange_val (K : LevelIndex) (q : (TowerA).obj K) :
    ((Pullback).app K q).val =
      (weilPrimeToAdelicFrameRightOrbitBaseChange b A preservation composition unitCoherence associativity comparison symmetry
        stability universality hA geometryA MA evaluationA hA' geometryA' MA' evaluationA'
        compatibility lam h i V ψ s hAway K.toSubgroup).symm q.val := rfl

/-- The naturality square also holds on each individual level class. -/
theorem weilPrimeToAdelicCompactOpenLevelBaseChange_arrow {K L : LevelIndex} (f : K ⟶ L) (q : (TowerA).obj K) :
    (Pullback).app L ((TowerA).map f q) =
      (Towerb).map f ((Pullback).app K q) :=
  (Pullback).naturality_apply f q

section Hecke
variable [Module.Finite ℚ V]

/-- The first compact-open Hecke leg commutes with pointed pullback. -/
theorem weilPrimeToAdelicCompactOpenLevelBaseChange_heckeLeft (K L : LevelIndex)
    (g : ScalarExtensionSimilitudePoints D V (Global.PrimeToFiniteAdeles m) ψ) (q : (TowerA).obj (Langlands.Shimura.CompactOpenLevel.heckeLevel K L g)) :
    (Pullback).app K ((TowerA).map (Langlands.Shimura.CompactOpenLevel.heckeLeft K L g) q) =
      (Towerb).map (Langlands.Shimura.CompactOpenLevel.heckeLeft K L g)
        ((Pullback).app (Langlands.Shimura.CompactOpenLevel.heckeLevel K L g) q) :=
  (Pullback).naturality_apply _ q

/-- The second compact-open Hecke leg commutes with pointed pullback. -/
theorem weilPrimeToAdelicCompactOpenLevelBaseChange_heckeRight (K L : LevelIndex)
    (g : ScalarExtensionSimilitudePoints D V (Global.PrimeToFiniteAdeles m) ψ) (q : (TowerA).obj (Langlands.Shimura.CompactOpenLevel.heckeLevel K L g)) :
    (Pullback).app L ((TowerA).map (Langlands.Shimura.CompactOpenLevel.heckeRight K L g) q) =
      (Towerb).map (Langlands.Shimura.CompactOpenLevel.heckeRight K L g)
        ((Pullback).app (Langlands.Shimura.CompactOpenLevel.heckeLevel K L g) q) :=
  (Pullback).naturality_apply _ q

end Hecke

end Away

end Langlands.AbelianScheme.Tate
