import Langlands.AbelianScheme.Tate.GeometricWeilCompactOpenLevels
import Langlands.AbelianScheme.Tate.WeilCompactOpenLevelPathBaseChange

/-! # Base change of actual geometric Weil-compatible level towers -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.AbelianScheme.Tate.Geometric

universe u v w
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme Langlands.Shimura Langlands.Shimura.PEL
open GroupScheme.Tate (Index)

variable {S S' : Scheme.{u}} [QuasiSeparatedSpace S] [QuasiSeparatedSpace S']
  (b : S' ⟶ S) (A : AbelianScheme S)
  (preservation : pullbackTensorComparisonIsIsoStatement.{u})
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
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  (lam : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA evaluationA
    stability composition unitCoherence associativity comparison symmetry)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)

local notation "lamBC" => canonicalDualValuedBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA
  evaluationA hA' geometryA' MA' evaluationA'
set_option quotPrecheck false in
local notation "iBC" => (AbelianScheme.rationalBaseChangeEnd b A).comp i

section Full
variable (h : Global.RationalProfiniteIntegerAdeleComparison)
  (hunit : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S')

set_option quotPrecheck false in
local notation "hunitb" => fun n => TateTwist.Geometry.InvertibleOrders.pullbackUnit b n.val (hunit n)
local notation "μfin" => TateTwist.Geometry.InvertibleOrders.selectedFinite S (fun _ => True) hunit
local notation "μet" => TateTwist.Geometry.InvertibleOrders.selectedEtale S (fun _ => True) hunit
local notation "μfinb" => TateTwist.Geometry.InvertibleOrders.selectedFinite S' (fun _ => True) hunitb
local notation "μetb" => TateTwist.Geometry.InvertibleOrders.selectedEtale S' (fun _ => True) hunitb
local notation "LevelIndex" => FiniteAdelicScalarExtensionLevel D V ψ
local notation "G" => ScalarExtensionSimilitudePoints D V (Global.FiniteAdeles ℚ) ψ
local notation "towerA" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence
  associativity comparison symmetry stability compatibility hA geometryA MA evaluationA lam i V ψ h hunit
local notation "towerb" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence
  associativity comparison symmetry stability compatibility hA' geometryA' MA' evaluationA'
  (lamBC lam) iBC V ψ h hunitb
local notation "levelBC" => Tate.weilAdelicLevelBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA
  evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ

/-- Pointed full pullback, with geometric proofs and all new-base units supplied. -/
def weilAdelicCompactOpenLevelBaseChange : towerA (s ≫ b) ⟶ towerb s :=
  Tate.weilAdelicCompactOpenLevelBaseChange b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA geometryA MA evaluationA
    hA' geometryA' MA' evaluationA' compatibility lam h i V ψ s
    (geometricFiberFinite s) (geometricFiberFinite (s ≫ b)) torsionFiniteEtale hunit hunitb
    (hμfin := μfin) (hμet := μet) (hμfin' := μfinb) (hμet' := μetb)

local notation "pull" => weilAdelicCompactOpenLevelBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA
  evaluationA hA' geometryA' MA' evaluationA' compatibility lam i V ψ h hunit

/-- Every component is the published actual pointed fixed-orbit map. -/
@[simp] theorem weilAdelicCompactOpenLevelBaseChange_app
    (K : LevelIndex) (q : (towerA (s ≫ b)).obj K) :
    (pull s).app K q =
      levelBC s (geometricFiberFinite s) (geometricFiberFinite (s ≫ b))
        torsionFiniteEtale hunit hunitb
        (hμfin := μfin) (hμet := μet) (hμfin' := μfinb) (hμet' := μetb)
        K.toSubgroup q := rfl

/-- Pointed full pullback has injective components. -/
theorem weilAdelicCompactOpenLevelBaseChange_injective (K : LevelIndex) :
    Function.Injective ((pull s).app K) :=
  Tate.weilAdelicCompactOpenLevelBaseChange_injective b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA geometryA MA
    evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ s
    (geometricFiberFinite s) (geometricFiberFinite (s ≫ b)) torsionFiniteEtale hunit hunitb
    (hμfin := μfin) (hμet := μet) (hμfin' := μfinb) (hμet' := μetb) K

/-- The underlying full orbit is pulled back by the inverse actual frame comparison. -/
@[simp] theorem weilAdelicCompactOpenLevelBaseChange_val
    (K : LevelIndex) (q : (towerA (s ≫ b)).obj K) :
    ((pull s).app K q).val =
      (Tate.weilAdelicFrameRightOrbitBaseChange b A preservation composition unitCoherence
        associativity comparison symmetry stability universality hA geometryA MA evaluationA
        hA' geometryA' MA' evaluationA' compatibility lam h i V ψ s K.toSubgroup).symm q.val := rfl

/-- Every full transporter square commutes, including the level-forgetting squares. -/
theorem weilAdelicCompactOpenLevelBaseChange_arrow
    {K L : LevelIndex} (f : K ⟶ L) (q : (towerA (s ≫ b)).obj K) :
    (pull s).app L ((towerA (s ≫ b)).map f q) =
      (towerb s).map f ((pull s).app K q) :=
  (pull s).naturality_apply f q

section Hecke
variable [Module.Finite ℚ V]

/-- Pointed full pullback commutes with the first actual compact-open Hecke leg. -/
theorem weilAdelicCompactOpenLevelBaseChange_heckeLeft
    (K L : LevelIndex) (g : G)
    (q : (towerA (s ≫ b)).obj (CompactOpenLevel.heckeLevel K L g)) :
    (pull s).app K ((towerA (s ≫ b)).map (CompactOpenLevel.heckeLeft K L g) q) =
      (towerb s).map (CompactOpenLevel.heckeLeft K L g)
        ((pull s).app (CompactOpenLevel.heckeLevel K L g) q) :=
  (pull s).naturality_apply _ q

/-- Pointed full pullback commutes with the second actual compact-open Hecke leg. -/
theorem weilAdelicCompactOpenLevelBaseChange_heckeRight
    (K L : LevelIndex) (g : G)
    (q : (towerA (s ≫ b)).obj (CompactOpenLevel.heckeLevel K L g)) :
    (pull s).app L ((towerA (s ≫ b)).map (CompactOpenLevel.heckeRight K L g) q) =
      (towerb s).map (CompactOpenLevel.heckeRight K L g)
        ((pull s).app (CompactOpenLevel.heckeLevel K L g) q) :=
  (pull s).naturality_apply _ q

end Hecke

section Canonical
variable [ConnectedSpace S'] [IsLocallyNoetherian S']
  {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω'] (t : Spec (.of Ω') ⟶ S')

/-- Canonical full pullback between arbitrary geometric-point presentations. -/
def weilAdelicCompactOpenLevelGeometricBaseChange : towerA (s ≫ b) ⟶ towerb t :=
  Tate.weilAdelicCompactOpenLevelGeometricBaseChange b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA geometryA MA evaluationA
    hA' geometryA' MA' evaluationA' compatibility lam h i V ψ torsionFiniteEtale
    (geometricFiberFinite (s ≫ b)) hunit hunitb
    (s := s) (t := t) (hs := geometricFiberFinite s) (ht := geometricFiberFinite t)
    (hμfin := μfin) (hμet := μet) (hμfin' := μfinb) (hμet' := μetb)

local notation "geometricPull" => weilAdelicCompactOpenLevelGeometricBaseChange b A preservation
  composition unitCoherence associativity comparison symmetry stability universality hA geometryA
  MA evaluationA hA' geometryA' MA' evaluationA' compatibility lam i V ψ h hunit s t
local notation "transportb" => weilAdelicCompactOpenLevelGeometricTransport preservation
  composition unitCoherence associativity comparison symmetry stability compatibility
  hA' geometryA' MA' evaluationA' (lamBC lam) iBC V ψ h hunitb

/-- Every actual etale path computes the canonical full pullback. -/
theorem weilAdelicCompactOpenLevelGeometricBaseChange_eq_path
    (p : fiberFunctor s (geometricFiberFinite s) ≅ fiberFunctor t (geometricFiberFinite t)) :
    geometricPull =
      Tate.weilAdelicCompactOpenLevelBaseChangeAlongPath b A preservation composition
        unitCoherence associativity comparison symmetry stability universality hA geometryA MA
        evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ torsionFiniteEtale
        (geometricFiberFinite (s ≫ b)) hunit hunitb
        (hμfin := μfin) (hμet := μet) (hμfin' := μfinb) (hμet' := μetb) p :=
  Tate.weilAdelicCompactOpenLevelGeometricBaseChange_eq_path b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA geometryA MA
    evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ torsionFiniteEtale
    (geometricFiberFinite (s ≫ b)) hunit hunitb
    (hμfin := μfin) (hμet := μet) (hμfin' := μfinb) (hμet' := μetb) p

/-- Canonical full pullback is pointed pullback followed by canonical new-base transport. -/
theorem weilAdelicCompactOpenLevelGeometricBaseChange_eq_transport :
    geometricPull = pull s ≫ (transportb s t).hom := rfl

/-- Canonical full pullback has injective components. -/
theorem weilAdelicCompactOpenLevelGeometricBaseChange_injective (K : LevelIndex) :
    Function.Injective ((geometricPull).app K) :=
  Tate.weilAdelicCompactOpenLevelGeometricBaseChange_injective b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA geometryA MA
    evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ torsionFiniteEtale
    (geometricFiberFinite (s ≫ b)) hunit hunitb
    (s := s) (t := t) (hs := geometricFiberFinite s) (ht := geometricFiberFinite t)
    (hμfin := μfin) (hμet := μet) (hμfin' := μfinb) (hμet' := μetb) K

/-- Canonical full pullback commutes with every transporter and hence with both Hecke legs. -/
theorem weilAdelicCompactOpenLevelGeometricBaseChange_arrow
    {K L : LevelIndex} (f : K ⟶ L) (q : (towerA (s ≫ b)).obj K) :
    (geometricPull).app L ((towerA (s ≫ b)).map f q) =
      (towerb t).map f ((geometricPull).app K q) :=
  (geometricPull).naturality_apply f q

variable [ConnectedSpace S] [IsLocallyNoetherian S]

/-- Canonical full pullback also transports on the old base before pointed pullback. -/
theorem weilAdelicCompactOpenLevelGeometricBaseChange_eq_pushed_transport :
    geometricPull =
      (weilAdelicCompactOpenLevelGeometricTransport preservation composition unitCoherence
        associativity comparison symmetry stability compatibility hA geometryA MA evaluationA
        lam i V ψ h hunit (s ≫ b) (t ≫ b)).hom ≫ pull t :=
  Tate.weilAdelicCompactOpenLevelGeometricBaseChange_eq_pushed_transport b A preservation
    composition unitCoherence associativity comparison symmetry stability universality hA geometryA
    MA evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ torsionFiniteEtale
    (geometricFiberFinite (s ≫ b)) (geometricFiberFinite (t ≫ b)) hunit hunitb
    (s := s) (t := t) (hs := geometricFiberFinite s) (ht := geometricFiberFinite t)
    (hμfin := μfin) (hμet := μet) (hμfin' := μfinb) (hμet' := μetb)

end Canonical
end Full

section Away
variable {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  (hunit : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S')

set_option quotPrecheck false in
local notation "hunitb" => fun n => TateTwist.Geometry.InvertibleOrders.pullbackUnit b n.val (hunit n)
local notation "μfin" => TateTwist.Geometry.InvertibleOrders.selectedFinite S (fun n => Nat.Coprime n m) hunit
local notation "μet" => TateTwist.Geometry.InvertibleOrders.selectedEtale S (fun n => Nat.Coprime n m) hunit
local notation "μfinb" => TateTwist.Geometry.InvertibleOrders.selectedFinite S' (fun n => Nat.Coprime n m) hunitb
local notation "μetb" => TateTwist.Geometry.InvertibleOrders.selectedEtale S' (fun n => Nat.Coprime n m) hunitb
local notation "LevelIndex" => PrimeToScalarExtensionLevel D V ψ m
local notation "G" => ScalarExtensionSimilitudePoints D V (Global.PrimeToFiniteAdeles m) ψ
local notation "towerA" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence
  associativity comparison symmetry stability compatibility hA geometryA MA evaluationA lam
  i V ψ (m := m) hAway hunit
local notation "towerb" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence
  associativity comparison symmetry stability compatibility hA' geometryA' MA' evaluationA'
  (lamBC lam) iBC V ψ (m := m) hAway hunitb
local notation "levelBC" => Tate.weilPrimeToAdelicLevelBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA
  evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ

/-- Pointed away pullback, with geometric proofs and all new-base units supplied. -/
def weilPrimeToAdelicCompactOpenLevelBaseChange : towerA (s ≫ b) ⟶ towerb s :=
  Tate.weilPrimeToAdelicCompactOpenLevelBaseChange b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA geometryA MA evaluationA
    hA' geometryA' MA' evaluationA' compatibility lam h i V ψ s
    (geometricFiberFinite s) (geometricFiberFinite (s ≫ b)) torsionFiniteEtale hAway hunit hunitb
    (hμfin := μfin) (hμet := μet) (hμfin' := μfinb) (hμet' := μetb)

local notation "pull" => weilPrimeToAdelicCompactOpenLevelBaseChange b A preservation composition
  unitCoherence associativity comparison symmetry stability universality hA geometryA MA
  evaluationA hA' geometryA' MA' evaluationA' compatibility lam i V ψ hAway hunit

/-- Every component is the published actual pointed away fixed-orbit map. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelBaseChange_app
    (K : LevelIndex) (q : (towerA (s ≫ b)).obj K) :
    (pull s).app K q =
      levelBC s (geometricFiberFinite s) (geometricFiberFinite (s ≫ b))
        torsionFiniteEtale hAway hunit hunitb
        (hμfin := μfin) (hμet := μet) (hμfin' := μfinb) (hμet' := μetb)
        K.toSubgroup q := rfl

/-- Pointed away pullback has injective components. -/
theorem weilPrimeToAdelicCompactOpenLevelBaseChange_injective (K : LevelIndex) :
    Function.Injective ((pull s).app K) :=
  Tate.weilPrimeToAdelicCompactOpenLevelBaseChange_injective b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA geometryA MA
    evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ s
    (geometricFiberFinite s) (geometricFiberFinite (s ≫ b)) torsionFiniteEtale hAway hunit hunitb
    (hμfin := μfin) (hμet := μet) (hμfin' := μfinb) (hμet' := μetb) K

/-- The underlying away orbit is pulled back by the inverse actual frame comparison. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelBaseChange_val
    (K : LevelIndex) (q : (towerA (s ≫ b)).obj K) :
    ((pull s).app K q).val =
      (Tate.weilPrimeToAdelicFrameRightOrbitBaseChange b A preservation composition unitCoherence
        associativity comparison symmetry stability universality hA geometryA MA evaluationA
        hA' geometryA' MA' evaluationA' compatibility lam h i V ψ s hAway K.toSubgroup).symm q.val := rfl

/-- Every away transporter square commutes, including the level-forgetting squares. -/
theorem weilPrimeToAdelicCompactOpenLevelBaseChange_arrow
    {K L : LevelIndex} (f : K ⟶ L) (q : (towerA (s ≫ b)).obj K) :
    (pull s).app L ((towerA (s ≫ b)).map f q) =
      (towerb s).map f ((pull s).app K q) :=
  (pull s).naturality_apply f q

section Hecke
variable [Module.Finite ℚ V]

/-- Pointed away pullback commutes with the first actual compact-open Hecke leg. -/
theorem weilPrimeToAdelicCompactOpenLevelBaseChange_heckeLeft
    (K L : LevelIndex) (g : G)
    (q : (towerA (s ≫ b)).obj (CompactOpenLevel.heckeLevel K L g)) :
    (pull s).app K ((towerA (s ≫ b)).map (CompactOpenLevel.heckeLeft K L g) q) =
      (towerb s).map (CompactOpenLevel.heckeLeft K L g)
        ((pull s).app (CompactOpenLevel.heckeLevel K L g) q) :=
  (pull s).naturality_apply _ q

/-- Pointed away pullback commutes with the second actual compact-open Hecke leg. -/
theorem weilPrimeToAdelicCompactOpenLevelBaseChange_heckeRight
    (K L : LevelIndex) (g : G)
    (q : (towerA (s ≫ b)).obj (CompactOpenLevel.heckeLevel K L g)) :
    (pull s).app L ((towerA (s ≫ b)).map (CompactOpenLevel.heckeRight K L g) q) =
      (towerb s).map (CompactOpenLevel.heckeRight K L g)
        ((pull s).app (CompactOpenLevel.heckeLevel K L g) q) :=
  (pull s).naturality_apply _ q

end Hecke

section Canonical
variable [ConnectedSpace S'] [IsLocallyNoetherian S']
  {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω'] (t : Spec (.of Ω') ⟶ S')

/-- Canonical away pullback between arbitrary geometric-point presentations. -/
def weilPrimeToAdelicCompactOpenLevelGeometricBaseChange : towerA (s ≫ b) ⟶ towerb t :=
  Tate.weilPrimeToAdelicCompactOpenLevelGeometricBaseChange b A preservation composition unitCoherence
    associativity comparison symmetry stability universality hA geometryA MA evaluationA
    hA' geometryA' MA' evaluationA' compatibility lam h i V ψ torsionFiniteEtale
    (geometricFiberFinite (s ≫ b)) hAway hunit hunitb
    (s := s) (t := t) (hs := geometricFiberFinite s) (ht := geometricFiberFinite t)
    (hμfin := μfin) (hμet := μet) (hμfin' := μfinb) (hμet' := μetb)

local notation "geometricPull" => weilPrimeToAdelicCompactOpenLevelGeometricBaseChange b A preservation
  composition unitCoherence associativity comparison symmetry stability universality hA geometryA
  MA evaluationA hA' geometryA' MA' evaluationA' compatibility lam i V ψ hAway hunit s t
local notation "transportb" => weilPrimeToAdelicCompactOpenLevelGeometricTransport preservation
  composition unitCoherence associativity comparison symmetry stability compatibility
  hA' geometryA' MA' evaluationA' (lamBC lam) iBC V ψ (m := m) hAway hunitb

/-- Every actual etale path computes the canonical away pullback. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricBaseChange_eq_path
    (p : fiberFunctor s (geometricFiberFinite s) ≅ fiberFunctor t (geometricFiberFinite t)) :
    geometricPull =
      Tate.weilPrimeToAdelicCompactOpenLevelBaseChangeAlongPath b A preservation composition
        unitCoherence associativity comparison symmetry stability universality hA geometryA MA
        evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ torsionFiniteEtale
        (geometricFiberFinite (s ≫ b)) hAway hunit hunitb
        (hμfin := μfin) (hμet := μet) (hμfin' := μfinb) (hμet' := μetb) p :=
  Tate.weilPrimeToAdelicCompactOpenLevelGeometricBaseChange_eq_path b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA geometryA MA
    evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ torsionFiniteEtale
    (geometricFiberFinite (s ≫ b)) hAway hunit hunitb
    (hμfin := μfin) (hμet := μet) (hμfin' := μfinb) (hμet' := μetb) p

/-- Canonical away pullback is pointed pullback followed by canonical new-base transport. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricBaseChange_eq_transport :
    geometricPull = pull s ≫ (transportb s t).hom := rfl

/-- Canonical away pullback has injective components. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricBaseChange_injective (K : LevelIndex) :
    Function.Injective ((geometricPull).app K) :=
  Tate.weilPrimeToAdelicCompactOpenLevelGeometricBaseChange_injective b A preservation composition
    unitCoherence associativity comparison symmetry stability universality hA geometryA MA
    evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ torsionFiniteEtale
    (geometricFiberFinite (s ≫ b)) hAway hunit hunitb
    (s := s) (t := t) (hs := geometricFiberFinite s) (ht := geometricFiberFinite t)
    (hμfin := μfin) (hμet := μet) (hμfin' := μfinb) (hμet' := μetb) K

/-- Canonical away pullback commutes with every transporter and hence with both Hecke legs. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricBaseChange_arrow
    {K L : LevelIndex} (f : K ⟶ L) (q : (towerA (s ≫ b)).obj K) :
    (geometricPull).app L ((towerA (s ≫ b)).map f q) =
      (towerb t).map f ((geometricPull).app K q) :=
  (geometricPull).naturality_apply f q

variable [ConnectedSpace S] [IsLocallyNoetherian S]

/-- Canonical away pullback also transports on the old base before pointed pullback. -/
theorem weilPrimeToAdelicCompactOpenLevelGeometricBaseChange_eq_pushed_transport :
    geometricPull =
      (weilPrimeToAdelicCompactOpenLevelGeometricTransport preservation composition unitCoherence
        associativity comparison symmetry stability compatibility hA geometryA MA evaluationA
        lam i V ψ (m := m) hAway hunit (s ≫ b) (t ≫ b)).hom ≫ pull t :=
  Tate.weilPrimeToAdelicCompactOpenLevelGeometricBaseChange_eq_pushed_transport b A preservation
    composition unitCoherence associativity comparison symmetry stability universality hA geometryA
    MA evaluationA hA' geometryA' MA' evaluationA' compatibility lam h i V ψ torsionFiniteEtale
    (geometricFiberFinite (s ≫ b)) (geometricFiberFinite (t ≫ b)) hAway hunit hunitb
    (s := s) (t := t) (hs := geometricFiberFinite s) (ht := geometricFiberFinite t)
    (hμfin := μfin) (hμet := μet) (hμfin' := μfinb) (hμet' := μetb)

end Canonical
end Away

end Langlands.AbelianScheme.Tate.Geometric
