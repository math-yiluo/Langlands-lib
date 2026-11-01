import Langlands.Shimura.PEL.HarrisTaylorLiePolarizedClasses

/-! # The actual Harris positive Lie and dimension level tower -/

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
  (L : Type) [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  (p : S ⟶ Spec (.of F))

variable
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

local notation "Level" => HarrisLevel D
local notation "OriginalGroup" =>
  D.toSecondKindInvolution.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ
local notation "indexFunctor" => hodgeLevelFunctor D C
local notation "Data" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu
local notation "Good" => ObjectCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
local notation "Ambient" => AmbientClass D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu additivity
local notation "ambientMk" => ambientClassOf D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu additivity
local notation "forget" => forgetAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu additivity
local notation "LieCondition" => LieClassCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
  compatibility h s hs htor hu additivity
local notation "Condition" => ClassCondition D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
  compatibility h s hs htor hu additivity
local notation "Classes" => IsoClass D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
  compatibility h s hs htor hu additivity
local notation "mkClass" => classOf D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
  compatibility h s hs htor hu additivity
local notation "forgetJoint" => forgetDimensionLieAction D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality L p
  compatibility h s hs htor hu additivity

/-- The actual raw polarized tower, reindexed by the original opposite Harris group. -/
def ambientTower : Level ⥤ Type 1 :=
  letI := auxiliaryStarRing D C
  indexFunctor ⋙ PolarizedWeilLevel.isoClassTower preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) s hs htor hu additivity

local notation "rawTower" => ambientTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu additivity

@[simp] theorem ambientTower_obj (U : Level) : (rawTower).obj U = Ambient U := rfl

/-- Apply the actual transported original-group arrow to the compatible orbit. -/
def mapRepresentative {U V : Level} (f : U ⟶ V) (x : Data U) : Data V := by
  letI := auxiliaryStarRing D C
  exact PolarizedWeilLevel.mapData preservation composition unitCoherence associativity
    comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) s hs htor hu ((indexFunctor).map f) x

local notation "mapRep" => mapRepresentative D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s hs htor hu

/-- Level transport retains the identical positive polarized abelian object. -/
@[simp] theorem mapRepresentative_fst {U V : Level} (f : U ⟶ V) (x : Data U) :
    (mapRep f x).1 = x.1 := rfl

/-- The actual same-representative dimension and positive Lie test is unchanged. -/
@[simp] theorem objectCondition_mapRepresentative_iff {U V : Level}
    (f : U ⟶ V) (x : Data U) : Good (mapRep f x).1 ↔ Good x.1 := Iff.rfl

@[simp] theorem ambientTower_map_ambientClassOf {U V : Level} (f : U ⟶ V) (x : Data U) :
    (rawTower).map f (ambientMk x) = ambientMk (mapRep f x) := rfl

/-- Forgetting the actual action class commutes with every original level arrow. -/
@[simp] theorem forgetAction_ambientTower_map {U V : Level} (f : U ⟶ V) (q : Ambient U) :
    forget ((rawTower).map f q) = forget q := by
  let := auxiliaryStarRing D C
  exact PolarizedWeilLevel.forgetAction_classMap preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h
    A (D.harrisHodgePELForm C) s hs htor hu additivity ((indexFunctor).map f) q

/-- Positive Lie compatibility is preserved and reflected by all level maps. -/
theorem lieClassCondition_ambientTower_map_iff {U V : Level} (f : U ⟶ V) (q : Ambient U) :
    LieCondition ((rawTower).map f q) ↔ LieCondition q := by
  change HarrisTaylor.LieCompatibilityClassCondition L E p n
    (forget ((rawTower).map f q)) ↔ _
  rw [forgetAction_ambientTower_map]
  rfl

/-- Map the single actual representative witnessing both dimension and positive Lie compatibility. -/
theorem classCondition_map {U V : Level} (f : U ⟶ V) (q : Ambient U)
    (hq : Condition q) : Condition ((rawTower).map f q) := by
  obtain ⟨x, hx, hgood⟩ := hq
  refine ⟨mapRep f x, ?_, hgood⟩
  rw [← hx]
  rfl

/-- Restrict actual transporter maps to the joint dimension-and-Lie image. -/
def classMap {U V : Level} (f : U ⟶ V) (q : Classes U) : Classes V :=
  ⟨(rawTower).map f q.val,
    classCondition_map D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality L p compatibility h
      s hs htor hu additivity f q.val q.property⟩

local notation "mapClass" => classMap D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
  compatibility h s hs htor hu additivity

@[simp] theorem classMap_val {U V : Level} (f : U ⟶ V) (q : Classes U) :
    (mapClass f q).val = (rawTower).map f q.val := rfl

@[simp] theorem classMap_classOf {U V : Level} (f : U ⟶ V)
    (x : Data U) (hx : Good x.1) :
    mapClass f (mkClass x hx) = mkClass (mapRep f x) hx := rfl

/-- The actual positive polarized dimension-and-Lie tower at original Harris levels. -/
def isoClassTower : Level ⥤ Type 1 where
  obj U := Classes U
  map f := ↾(mapClass f)
  map_id U := by
    ext q
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((rawTower).map_id U) q.val
  map_comp f g := by
    ext q
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((rawTower).map_comp f g) q.val

local notation "tower" => isoClassTower D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality L p
  compatibility h s hs htor hu additivity

@[simp] theorem isoClassTower_obj (U : Level) : (tower).obj U = Classes U := rfl

/-- The joint image includes naturally into the actual raw polarized tower. -/
def inclusionNatTrans : tower ⟶ rawTower where
  app _ := ↾Subtype.val
  naturality {_U _V} _f := rfl

/-- Level maps retain the same joint dimension-and-Lie action class. -/
@[simp] theorem forgetDimensionLieAction_classMap {U V : Level} (f : U ⟶ V) (q : Classes U) :
    forgetJoint (mapClass f q) = forgetJoint q := by
  obtain ⟨x, hx, hq⟩ := classOf_surjective D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality L p
    compatibility h s hs htor hu additivity q
  rw [← hq]
  rfl

/-- Forgetting polarization and levels is natural into the constant joint action-class image. -/
def forgetDimensionLieActionNatTrans :
    tower ⟶ (Functor.const Level).obj
      (HarrisTaylor.DimensionLieActionClass L E p n (A := A)) where
  app _ := ↾forgetJoint
  naturality {U V} f := by
    ext q
    exact forgetDimensionLieAction_classMap D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality L p
      compatibility h s hs htor hu additivity f q

/-- Forget an original subgroup through its actual inclusion arrow. -/
def forgetLevel {U V : Level} (hU : U.subgroup ≤ V.subgroup) :
    Classes U → Classes V := mapClass (CompactOpenLevel.inclusion hU)

@[simp] theorem forgetLevel_classOf {U V : Level} (hU : U.subgroup ≤ V.subgroup)
    (x : Data U) (hx : Good x.1) :
    forgetLevel D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality L p compatibility h
      s hs htor hu additivity hU (mkClass x hx) =
      mkClass (mapRep (CompactOpenLevel.inclusion hU) x) hx := rfl

@[simp] theorem forgetDimensionLieAction_forgetLevel {U V : Level}
    (hU : U.subgroup ≤ V.subgroup) (q : Classes U) :
    forgetJoint (forgetLevel D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality L p compatibility h
      s hs htor hu additivity hU q) = forgetJoint q :=
  forgetDimensionLieAction_classMap D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality L p
    compatibility h s hs htor hu additivity (CompactOpenLevel.inclusion hU) q

include D C in
private theorem rationalFinite : Module.Finite ℚ A :=
  (hodgeRationalPELConditions D C).finite_module

/-- The inclusion leg from the actual original-Harris Hecke intersection. -/
def heckeLeft (U V : Level) (g : OriginalGroup) :
    letI := rationalFinite D C
    Classes (CompactOpenLevel.heckeLevel U V g) → Classes U := by
  letI := rationalFinite D C
  exact fun q => mapClass (CompactOpenLevel.heckeLeft U V g) q

/-- The right-translation leg from the same original-Harris Hecke intersection. -/
def heckeRight (U V : Level) (g : OriginalGroup) :
    letI := rationalFinite D C
    Classes (CompactOpenLevel.heckeLevel U V g) → Classes V := by
  letI := rationalFinite D C
  exact fun q => mapClass (CompactOpenLevel.heckeRight U V g) q

@[simp] theorem heckeLeft_classOf (U V : Level) (g : OriginalGroup)
    (x : letI := rationalFinite D C
      Data (CompactOpenLevel.heckeLevel U V g)) (hx : Good x.1) :
    letI := rationalFinite D C
    heckeLeft D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality L p compatibility h
      s hs htor hu additivity U V g (mkClass x hx) =
      mkClass (mapRep (CompactOpenLevel.heckeLeft U V g) x) hx := rfl

@[simp] theorem heckeRight_classOf (U V : Level) (g : OriginalGroup)
    (x : letI := rationalFinite D C
      Data (CompactOpenLevel.heckeLevel U V g)) (hx : Good x.1) :
    letI := rationalFinite D C
    heckeRight D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality L p compatibility h
      s hs htor hu additivity U V g (mkClass x hx) =
      mkClass (mapRep (CompactOpenLevel.heckeRight U V g) x) hx := rfl

/-- Both Hecke legs have the same actual joint dimension-and-Lie action class. -/
theorem forgetDimensionLieAction_heckeLeft (U V : Level) (g : OriginalGroup)
    (q : letI := rationalFinite D C
      Classes (CompactOpenLevel.heckeLevel U V g)) :
    letI := rationalFinite D C
    forgetJoint (heckeLeft D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality L p compatibility h
      s hs htor hu additivity U V g q) = forgetJoint q := by
  let := rationalFinite D C
  exact forgetDimensionLieAction_classMap D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality L p
    compatibility h s hs htor hu additivity (CompactOpenLevel.heckeLeft U V g) q

/-- The right Hecke leg also forgets to the identical joint action class. -/
theorem forgetDimensionLieAction_heckeRight (U V : Level) (g : OriginalGroup)
    (q : letI := rationalFinite D C
      Classes (CompactOpenLevel.heckeLevel U V g)) :
    letI := rationalFinite D C
    forgetJoint (heckeRight D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality L p compatibility h
      s hs htor hu additivity U V g q) = forgetJoint q := by
  let := rationalFinite D C
  exact forgetDimensionLieAction_classMap D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality L p
    compatibility h s hs htor hu additivity (CompactOpenLevel.heckeRight U V g) q

end Langlands.Shimura.PEL.HarrisTaylorLieWeilLevel
