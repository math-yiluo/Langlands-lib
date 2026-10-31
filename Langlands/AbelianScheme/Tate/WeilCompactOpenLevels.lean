import Langlands.Shimura.PEL.ScalarExtensionTopology
import Langlands.AbelianScheme.Tate.WeilAdelicLevelTransport
import Langlands.AbelianScheme.Tate.WeilPrimeToAdelicLevelTransport
import Langlands.AbelianScheme.Tate.WeilGeometricTransportProof

/-! # Compact-open towers of actual Weil-compatible Tate levels -/

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
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
open Langlands.GroupScheme Langlands.Shimura Langlands.Shimura.PEL
open GroupScheme.Tate (Index)

section Full

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (polarizationMap : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
    evaluationA stability composition unitCoherence associativity comparison symmetry)
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun _ => True), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun _ => True), Etale (mu S n.val).X.hom]

local notation "Frame" => WeilAdelicFrame preservation composition unitCoherence associativity
  comparison symmetry stability hA geometryA MA evaluationA compatibility
  polarizationMap h i V ψ s

local notation "G" => ScalarExtensionSimilitudePoints D V (Global.FiniteAdeles ℚ) ψ
local notation "LevelIndex" => FiniteAdelicScalarExtensionLevel D V ψ

local notation "rightAction" => weilAdelicFrameRightAction preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
  polarizationMap h i V ψ s
local notation "monodromyAction" => weilAdelicFrameMonodromyAction preservation composition unitCoherence
  associativity comparison symmetry stability compatibility rationalWeilGeometricTransport
  hA geometryA MA evaluationA polarizationMap h i V ψ s hs htor hu
  (hμfin := hμfin) (hμet := hμet)
local notation "actionsComm" => weilAdelicFrameActionsComm preservation composition unitCoherence
  associativity comparison symmetry stability compatibility rationalWeilGeometricTransport
  hA geometryA MA evaluationA polarizationMap h i V ψ s hs htor hu
  (hμfin := hμfin) (hμet := hμet)
local notation "Level" => WeilAdelicLevel preservation composition unitCoherence associativity
  comparison symmetry stability compatibility rationalWeilGeometricTransport
  hA geometryA MA evaluationA polarizationMap h i V ψ s hs htor hu
  (hμfin := hμfin) (hμet := hμet)
local notation "levelTranslate" => weilAdelicLevelTranslate preservation composition unitCoherence
  associativity comparison symmetry stability compatibility rationalWeilGeometricTransport
  hA geometryA MA evaluationA polarizationMap h i V ψ htor hu
  (s := s) (hs := hs) (hμfin := hμfin) (hμet := hμet)
local notation "levelForget" => weilAdelicLevelForget preservation composition unitCoherence
  associativity comparison symmetry stability compatibility rationalWeilGeometricTransport
  hA geometryA MA evaluationA polarizationMap h i V ψ htor hu
  (s := s) (hs := hs) (hμfin := hμfin) (hμet := hμet)

/-- Actual monodromy-fixed right orbits at a compact open full adelic similitude level. -/
abbrev WeilAdelicCompactOpenLevel (K : LevelIndex) := Level K.toSubgroup

local notation "CompactLevel" => WeilAdelicCompactOpenLevel preservation composition unitCoherence
  associativity comparison symmetry stability compatibility hA geometryA MA evaluationA
  polarizationMap h i V ψ s hs htor hu
  (hμfin := hμfin) (hμet := hμet)

/-- The actual full adelic fixed-level tower on compact-open transporter arrows.
Geometric pairing transport uses its published proof. -/
def weilAdelicCompactOpenLevelTower : LevelIndex ⥤ Type (max u w) := by
  letI : MulAction Gᵐᵒᵖ Frame := rightAction
  letI : MulAction (FundamentalGroup s hs) Frame := monodromyAction
  letI : SMulCommClass (FundamentalGroup s hs) Gᵐᵒᵖ Frame := actionsComm
  exact InvariantOrbit.tower («G» := G) (X := Frame) (Γ := FundamentalGroup s hs)

local notation "Tower" => weilAdelicCompactOpenLevelTower preservation composition unitCoherence associativity
  comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
  h i V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)

/-- The tower object is the existing actual Weil-compatible fixed-orbit set. -/
@[simp] theorem weilAdelicCompactOpenLevelTower_obj (K : LevelIndex) :
    (Tower).obj K = CompactLevel K := rfl

/-- Every transporter arrow is the already constructed actual right translation. -/
@[simp] theorem weilAdelicCompactOpenLevelTower_map {K L : LevelIndex} (f : K ⟶ L) (q : CompactLevel K) :
    (Tower).map f q = levelTranslate f.element f.respects q := rfl

/-- On the underlying orbit, an arrow sends the frame class of eta to that of eta composed
with its similitude element. -/
theorem weilAdelicCompactOpenLevelTower_map_val {K L : LevelIndex} (f : K ⟶ L) (q : CompactLevel K) :
    letI : MulAction Gᵐᵒᵖ Frame := rightAction
    ((Tower).map f q).val = RightOrbit.translate f.element f.respects q.val := rfl

/-- Inclusion arrows are the actual forgetful maps of Weil-compatible fixed levels. -/
@[simp] theorem weilAdelicCompactOpenLevelTower_inclusion {K L : LevelIndex}
    (hK : K.toSubgroup ≤ L.toSubgroup) (q : CompactLevel K) :
    (Tower).map (CompactOpenLevel.inclusion hK) q = levelForget hK q := rfl

section Hecke

variable [Module.Finite ℚ V]

/-- The first leg at K intersect g L g inverse forgets the intermediate level. -/
def weilAdelicCompactOpenHeckeLeft (K L : LevelIndex) (g : G) :
    CompactLevel (CompactOpenLevel.heckeLevel K L g) → CompactLevel K :=
  (Tower).map (CompactOpenLevel.heckeLeft K L g)

/-- The second leg of the compact-open Hecke correspondence composes frames with g. -/
def weilAdelicCompactOpenHeckeRight (K L : LevelIndex) (g : G) :
    CompactLevel (CompactOpenLevel.heckeLevel K L g) → CompactLevel L :=
  (Tower).map (CompactOpenLevel.heckeRight K L g)

/-- The first Hecke leg is the established fixed-level forgetting map. -/
@[simp] theorem weilAdelicCompactOpenHeckeLeft_eq (K L : LevelIndex) (g : G)
    (q : CompactLevel (CompactOpenLevel.heckeLevel K L g)) :
    weilAdelicCompactOpenHeckeLeft preservation composition unitCoherence associativity comparison symmetry
      stability compatibility hA geometryA MA evaluationA polarizationMap h i V ψ
      s hs htor hu K L g q =
      levelForget
        (show (CompactOpenLevel.heckeLevel K L g).subgroup ≤ K.toSubgroup from
          fun _ hk => hk.1) q := rfl

/-- The second Hecke leg is the established fixed-level translation by g. -/
@[simp] theorem weilAdelicCompactOpenHeckeRight_eq (K L : LevelIndex) (g : G)
    (q : CompactLevel (CompactOpenLevel.heckeLevel K L g)) :
    weilAdelicCompactOpenHeckeRight preservation composition unitCoherence associativity comparison symmetry
      stability compatibility hA geometryA MA evaluationA polarizationMap h i V ψ
      s hs htor hu K L g q =
      levelTranslate g (CompactOpenLevel.heckeRight K L g).respects q := rfl

end Hecke

end Full

section Away

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (compatibility : RelativeFiniteWeilTransitionStatement.{u})
  {S : Scheme.{u}} [QuasiSeparatedSpace S] {A : AbelianScheme S}
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (polarizationMap : A ⟶ dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
    evaluationA stability composition unitCoherence associativity comparison symmetry)
  {h : Global.RationalProfiniteIntegerAdeleComparison} {m : ℕ}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] Rationalization.End A)
  (V : Type w) [AddCommGroup V] [Module ℚ V] [Module D V] [IsScalarTower ℚ D V]
  (ψ : LinearMap.BilinForm ℚ V)
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  [hμfin : ∀ n : Index (fun n => Nat.Coprime n m), IsFinite (mu S n.val).X.hom]
  [hμet : ∀ n : Index (fun n => Nat.Coprime n m), Etale (mu S n.val).X.hom]

local notation "Frame" => WeilPrimeToAdelicFrame preservation composition unitCoherence associativity
  comparison symmetry stability hA geometryA MA evaluationA compatibility
  polarizationMap h i V ψ s hAway

local notation "G" => ScalarExtensionSimilitudePoints D V (Global.PrimeToFiniteAdeles m) ψ
local notation "LevelIndex" => PrimeToScalarExtensionLevel D V ψ m

local notation "rightAction" => weilPrimeToAdelicFrameRightAction preservation composition unitCoherence
  associativity comparison symmetry stability hA geometryA MA evaluationA compatibility
  polarizationMap h i V ψ s hAway
local notation "monodromyAction" => weilPrimeToAdelicFrameMonodromyAction preservation composition unitCoherence
  associativity comparison symmetry stability compatibility rationalWeilGeometricTransport
  hA geometryA MA evaluationA polarizationMap hAway i V ψ s hs htor hu
  (hμfin := hμfin) (hμet := hμet)
local notation "actionsComm" => weilPrimeToAdelicFrameActionsComm preservation composition unitCoherence
  associativity comparison symmetry stability compatibility rationalWeilGeometricTransport
  hA geometryA MA evaluationA polarizationMap hAway i V ψ s hs htor hu
  (hμfin := hμfin) (hμet := hμet)
local notation "Level" => WeilPrimeToAdelicLevel preservation composition unitCoherence associativity
  comparison symmetry stability compatibility rationalWeilGeometricTransport
  hA geometryA MA evaluationA polarizationMap hAway i V ψ s hs htor hu
  (hμfin := hμfin) (hμet := hμet)
local notation "levelTranslate" => weilPrimeToAdelicLevelTranslate preservation composition unitCoherence
  associativity comparison symmetry stability compatibility rationalWeilGeometricTransport
  hA geometryA MA evaluationA polarizationMap hAway i V ψ htor hu
  (s := s) (hs := hs) (hμfin := hμfin) (hμet := hμet)
local notation "levelForget" => weilPrimeToAdelicLevelForget preservation composition unitCoherence
  associativity comparison symmetry stability compatibility rationalWeilGeometricTransport
  hA geometryA MA evaluationA polarizationMap hAway i V ψ htor hu
  (s := s) (hs := hs) (hμfin := hμfin) (hμet := hμet)

/-- Actual monodromy-fixed right orbits at a compact open prime-to-modulus similitude level. -/
abbrev WeilPrimeToAdelicCompactOpenLevel (K : LevelIndex) := Level K.toSubgroup

local notation "CompactLevel" => WeilPrimeToAdelicCompactOpenLevel preservation composition unitCoherence
  associativity comparison symmetry stability compatibility hA geometryA MA evaluationA
  polarizationMap hAway i V ψ s hs htor hu
  (hμfin := hμfin) (hμet := hμet)

/-- The actual prime-to-modulus fixed-level tower on compact-open transporter arrows.
Geometric pairing transport uses its published proof. -/
def weilPrimeToAdelicCompactOpenLevelTower : LevelIndex ⥤ Type (max u w) := by
  letI : MulAction Gᵐᵒᵖ Frame := rightAction
  letI : MulAction (FundamentalGroup s hs) Frame := monodromyAction
  letI : SMulCommClass (FundamentalGroup s hs) Gᵐᵒᵖ Frame := actionsComm
  exact InvariantOrbit.tower («G» := G) (X := Frame) (Γ := FundamentalGroup s hs)

local notation "Tower" => weilPrimeToAdelicCompactOpenLevelTower preservation composition unitCoherence associativity
  comparison symmetry stability compatibility hA geometryA MA evaluationA polarizationMap
  hAway i V ψ s hs htor hu (hμfin := hμfin) (hμet := hμet)

/-- The tower object is the existing actual Weil-compatible fixed-orbit set. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelTower_obj (K : LevelIndex) :
    (Tower).obj K = CompactLevel K := rfl

/-- Every transporter arrow is the already constructed actual right translation. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelTower_map {K L : LevelIndex} (f : K ⟶ L) (q : CompactLevel K) :
    (Tower).map f q = levelTranslate f.element f.respects q := rfl

/-- On the underlying orbit, an arrow sends the frame class of eta to that of eta composed
with its similitude element. -/
theorem weilPrimeToAdelicCompactOpenLevelTower_map_val {K L : LevelIndex} (f : K ⟶ L) (q : CompactLevel K) :
    letI : MulAction Gᵐᵒᵖ Frame := rightAction
    ((Tower).map f q).val = RightOrbit.translate f.element f.respects q.val := rfl

/-- Inclusion arrows are the actual forgetful maps of Weil-compatible fixed levels. -/
@[simp] theorem weilPrimeToAdelicCompactOpenLevelTower_inclusion {K L : LevelIndex}
    (hK : K.toSubgroup ≤ L.toSubgroup) (q : CompactLevel K) :
    (Tower).map (CompactOpenLevel.inclusion hK) q = levelForget hK q := rfl

section Hecke

variable [Module.Finite ℚ V]

/-- The first leg at K intersect g L g inverse forgets the intermediate level. -/
def weilPrimeToAdelicCompactOpenHeckeLeft (K L : LevelIndex) (g : G) :
    CompactLevel (CompactOpenLevel.heckeLevel K L g) → CompactLevel K :=
  (Tower).map (CompactOpenLevel.heckeLeft K L g)

/-- The second leg of the compact-open Hecke correspondence composes frames with g. -/
def weilPrimeToAdelicCompactOpenHeckeRight (K L : LevelIndex) (g : G) :
    CompactLevel (CompactOpenLevel.heckeLevel K L g) → CompactLevel L :=
  (Tower).map (CompactOpenLevel.heckeRight K L g)

/-- The first Hecke leg is the established fixed-level forgetting map. -/
@[simp] theorem weilPrimeToAdelicCompactOpenHeckeLeft_eq (K L : LevelIndex) (g : G)
    (q : CompactLevel (CompactOpenLevel.heckeLevel K L g)) :
    weilPrimeToAdelicCompactOpenHeckeLeft preservation composition unitCoherence associativity comparison symmetry
      stability compatibility hA geometryA MA evaluationA polarizationMap hAway i V ψ
      s hs htor hu K L g q =
      levelForget
        (show (CompactOpenLevel.heckeLevel K L g).subgroup ≤ K.toSubgroup from
          fun _ hk => hk.1) q := rfl

/-- The second Hecke leg is the established fixed-level translation by g. -/
@[simp] theorem weilPrimeToAdelicCompactOpenHeckeRight_eq (K L : LevelIndex) (g : G)
    (q : CompactLevel (CompactOpenLevel.heckeLevel K L g)) :
    weilPrimeToAdelicCompactOpenHeckeRight preservation composition unitCoherence associativity comparison symmetry
      stability compatibility hA geometryA MA evaluationA polarizationMap hAway i V ψ
      s hs htor hu K L g q =
      levelTranslate g (CompactOpenLevel.heckeRight K L g).respects q := rfl

end Hecke

end Away

end Langlands.AbelianScheme.Tate
