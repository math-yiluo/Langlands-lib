import Langlands.Shimura.PEL.HarrisPolarizedWeilClasses
import Langlands.AbelianScheme.Tate.HarrisWeilLevels

/-! # Polarized determinant classes indexed by the original Harris group -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
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

/-- Compact-open transporter indices for the opposite original Harris group. -/
abbrev HarrisLevel :=
  CompactOpenLevel D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ

local notation "OriginalLevel" => HarrisLevel D
local notation "OriginalGroup" =>
  D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ
local notation "ScalarLevel" =>
  FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)
local notation "scalarEquiv" =>
  D.harrisFiniteAdelicScalarExtensionContinuousEquiv
    (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C)

/-- The level transport uses the identical whole Hodge-positive unit as the form. -/
def hodgeLevelFunctor : OriginalLevel ⥤ ScalarLevel :=
  D.harrisWeilFiniteAdelicLevelFunctor
    (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C)

local notation "indexFunctor" => hodgeLevelFunctor D C

/-- The regular source satisfies the actual rational PEL conditions. -/
theorem hodgeRationalPELConditions :
    RationalPELConditions
      (D.harrisHodgePELAlgebra C).toSecondKindInvolution.rationalInvolution
      (D.harrisHodgePELForm C) :=
  D.harrisRationalPELConditions
    (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C)

@[simp] theorem hodgeLevelFunctor_obj_mem (U : OriginalLevel) (g : OriginalGroup) :
    scalarEquiv g ∈ ((indexFunctor).obj U).toSubgroup ↔ g ∈ U.subgroup :=
  D.harrisWeilFiniteAdelicLevelFunctor_obj_mem
    (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C) U g

@[simp] theorem hodgeLevelFunctor_map_element {U V : OriginalLevel} (f : U ⟶ V) :
    ((indexFunctor).map f).element = scalarEquiv f.element := rfl

/-- Original subgroup inclusions become actual transported inclusions. -/
theorem hodgeLevelFunctor_inclusion {U V : OriginalLevel} (hU : U.subgroup ≤ V.subgroup) :
    (indexFunctor).map (CompactOpenLevel.inclusion hU) =
      CompactOpenLevel.inclusion
        (show ((indexFunctor).obj U).toSubgroup ≤ ((indexFunctor).obj V).toSubgroup
          from fun _ hg => hU hg) :=
  D.harrisWeilFiniteAdelicLevelFunctor_inclusion
    (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C) hU

include D C in
private theorem hodgeRationalFinite : Module.Finite ℚ A :=
  (hodgeRationalPELConditions D C).finite_module

/-- Transport preserves the actual intermediate compact-open Hecke subgroup. -/
theorem hodgeLevelFunctor_heckeLevel (U V : OriginalLevel) (g : OriginalGroup) :
    letI := hodgeRationalFinite D C
    (indexFunctor).obj (CompactOpenLevel.heckeLevel U V g) =
      CompactOpenLevel.heckeLevel ((indexFunctor).obj U) ((indexFunctor).obj V)
        (scalarEquiv g) := by
  let := hodgeRationalFinite D C
  exact D.harrisWeilFiniteAdelicLevelFunctor_heckeLevel
    (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C) U V g

variable [IsScalarTower ℚ F A]
  (hΦ : IsCMSection E F Φ)
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  {S : Scheme.{0}}
  (b : S ⟶ Spec (.of (D.kottwitzCocharacterReflexField C)))
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [QuasiSeparatedSpace S]
  (additivity : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

local notation "positiveTower" => positiveIsoClassTower D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality b
  compatibility h s hs htor hu additivity
local notation "PositiveData" => PositiveLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu
local notation "Good" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality b
local notation "positiveMk" => positiveClassOf D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  s hs htor hu additivity

/-- Actual polarized determinant classes at a transported original Harris level. -/
abbrev HarrisIsoClass (U : OriginalLevel) :=
  (positiveTower).obj ((indexFunctor).obj U)

/-- Actual representatives retain their monodromy-fixed compatible level orbit. -/
abbrev HarrisLevelData (U : OriginalLevel) := PositiveData ((indexFunctor).obj U)

local notation "Classes" => HarrisIsoClass D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  s hs htor hu additivity
local notation "Data" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu

/-- The original-Harris-indexed tower of actual polarized determinant classes. -/
def harrisIsoClassTower : OriginalLevel ⥤ Type 1 :=
  indexFunctor ⋙ positiveTower

local notation "harrisTower" => harrisIsoClassTower D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality b
  compatibility h s hs htor hu additivity

@[simp] theorem harrisIsoClassTower_obj (U : OriginalLevel) :
    (harrisTower).obj U = Classes U := rfl

/-- The class of an actual representative satisfying the determinant condition. -/
def harrisClassOf {U : OriginalLevel} (x : Data U) (hx : Good x.1) : Classes U :=
  positiveMk x hx

local notation "mkClass" => harrisClassOf D C hΦ preservation composition unitCoherence
  associativity comparison symmetry stability square universality b compatibility h
  s hs htor hu additivity

/-- Every existing class has an actual determinant-compatible polarized representative. -/
theorem harrisClassOf_surjective {U : OriginalLevel} (q : Classes U) :
    ∃ (x : Data U) (hx : Good x.1), mkClass x hx = q :=
  positiveClassOf_surjective D C hΦ preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h
    s hs htor hu additivity q

/-- Equality is exactly the actual rational-isogeny and polarization-multiplier relation. -/
theorem harrisClassOf_eq_iff {U : OriginalLevel} (x y : Data U)
    (hx : Good x.1) (hy : Good y.1) :
    letI := auxiliaryStarRing D C
    mkClass x hx = mkClass y hy ↔
      ∃ q : ℚˣ, ∃ e : x.1.actionObj ≅ y.1.actionObj,
        ∃ he : PolarizedWeilLevel.Multiple preservation composition unitCoherence
          associativity comparison symmetry stability square universality additivity x.1 y.1 q e,
        PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
          comparison symmetry stability square universality compatibility h
          A (D.harrisHodgePELForm C) s hs htor hu additivity x.1 y.1
          ((indexFunctor).obj U) q e he x.2 = y.2 := by
  let := auxiliaryStarRing D C
  exact positiveClassOf_eq_iff D C hΦ preservation composition unitCoherence
    associativity comparison symmetry stability square universality b compatibility h
    s hs htor hu additivity x y hx hy

/-- Every original transporter acts through its actual regular-source image. -/
@[simp] theorem harrisIsoClassTower_map_classOf {U V : OriginalLevel} (f : U ⟶ V)
    (x : Data U) (hx : Good x.1) :
    letI := auxiliaryStarRing D C
    (harrisTower).map f (mkClass x hx) =
      mkClass (PolarizedWeilLevel.mapData preservation composition unitCoherence
        associativity comparison symmetry stability square universality compatibility h
        A (D.harrisHodgePELForm C) s hs htor hu ((indexFunctor).map f) x) hx := rfl

/-- Naturally forget polarization and the level while retaining the determinant action class. -/
def harrisForgetDeterminantActionNatTrans :
    harrisTower ⟶
      (Functor.const OriginalLevel).obj (D.HarrisRationalLieDeterminantClass C hΦ b) :=
  Functor.whiskerLeft indexFunctor
    (positiveForgetDeterminantActionNatTrans D C hΦ preservation composition unitCoherence
      associativity comparison symmetry stability square universality b compatibility h
      s hs htor hu additivity)

/-- Natural inclusion into the transported actual ambient polarized tower. -/
def harrisInclusionNatTrans :
    letI := auxiliaryStarRing D C
    harrisTower ⟶ indexFunctor ⋙
      PolarizedWeilLevel.isoClassTower preservation composition unitCoherence
        associativity comparison symmetry stability square universality compatibility h
        A (D.harrisHodgePELForm C) s hs htor hu additivity := by
  letI := auxiliaryStarRing D C
  exact Functor.whiskerLeft indexFunctor
    (positiveInclusionNatTrans D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality b compatibility h
      s hs htor hu additivity)

/-- Forgetting an original compact-open subgroup changes only the compatible orbit. -/
def harrisForgetLevel {U V : OriginalLevel} (hU : U.subgroup ≤ V.subgroup) :
    Classes U → Classes V :=
  (harrisTower).map (CompactOpenLevel.inclusion hU)

/-- Original subgroup forgetting is the actual forgetting at the transported subgroups. -/
theorem harrisForgetLevel_eq {U V : OriginalLevel} (hU : U.subgroup ≤ V.subgroup) :
    harrisForgetLevel D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality b compatibility h
      s hs htor hu additivity hU =
    positiveForgetLevel D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality b compatibility h
      s hs htor hu additivity
      (show ((indexFunctor).obj U).toSubgroup ≤ ((indexFunctor).obj V).toSubgroup
        from fun _ hg => hU hg) := by
  funext q
  change (positiveTower).map ((indexFunctor).map (CompactOpenLevel.inclusion hU)) q = _
  rw [hodgeLevelFunctor_inclusion]
  rfl

/-- The inclusion leg at the actual original-Harris Hecke intersection. -/
def harrisHeckeLeft (U V : OriginalLevel) (g : OriginalGroup) :
    letI := hodgeRationalFinite D C
    Classes (CompactOpenLevel.heckeLevel U V g) → Classes U := by
  letI := hodgeRationalFinite D C
  exact fun q => (harrisTower).map (CompactOpenLevel.heckeLeft U V g) q

/-- The right-translation leg at the same original-Harris Hecke intersection. -/
def harrisHeckeRight (U V : OriginalLevel) (g : OriginalGroup) :
    letI := hodgeRationalFinite D C
    Classes (CompactOpenLevel.heckeLevel U V g) → Classes V := by
  letI := hodgeRationalFinite D C
  exact fun q => (harrisTower).map (CompactOpenLevel.heckeRight U V g) q

/-- The original left Hecke leg acts by its transported actual representative map. -/
@[simp] theorem harrisHeckeLeft_classOf (U V : OriginalLevel) (g : OriginalGroup)
    (x : letI := hodgeRationalFinite D C
      Data (CompactOpenLevel.heckeLevel U V g)) (hx : Good x.1) :
    letI := hodgeRationalFinite D C
    letI := auxiliaryStarRing D C
    harrisHeckeLeft D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality b compatibility h
      s hs htor hu additivity U V g (mkClass x hx) =
      mkClass (PolarizedWeilLevel.mapData preservation composition unitCoherence
        associativity comparison symmetry stability square universality compatibility h
        A (D.harrisHodgePELForm C) s hs htor hu
        ((indexFunctor).map (CompactOpenLevel.heckeLeft U V g)) x) hx := rfl

/-- The original right Hecke leg uses the transported original element with its multiplier. -/
@[simp] theorem harrisHeckeRight_classOf (U V : OriginalLevel) (g : OriginalGroup)
    (x : letI := hodgeRationalFinite D C
      Data (CompactOpenLevel.heckeLevel U V g)) (hx : Good x.1) :
    letI := hodgeRationalFinite D C
    letI := auxiliaryStarRing D C
    harrisHeckeRight D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality b compatibility h
      s hs htor hu additivity U V g (mkClass x hx) =
      mkClass (PolarizedWeilLevel.mapData preservation composition unitCoherence
        associativity comparison symmetry stability square universality compatibility h
        A (D.harrisHodgePELForm C) s hs htor hu
        ((indexFunctor).map (CompactOpenLevel.heckeRight U V g)) x) hx := rfl

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
