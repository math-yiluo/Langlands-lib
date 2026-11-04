import Langlands.Shimura.PEL.HarrisIntegralCMLevelFamilyBaseChange
import Langlands.Shimura.PEL.HarrisTaylorCMIntegralUnpointedImage

/-! # The normalized class image of one actual integral Harris family -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.AbelianScheme Langlands.AlgebraicGeometry.Picard
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.GroupScheme.Tate (Index)

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra
open HarrisTaylorCMWeilLevel

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
    {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L] [Algebra L F]
    {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀))
    (P : Prerequisites.{0})
    {S : Scheme.{0}} (p : S ⟶ Spec (.of F))

/-- Tests over the fixed family base whose CM-field structure is admissible. -/
abbrev HarrisIntegralCMTestCategory :=
  ObjectProperty.FullSubcategory (fun T : Over S =>
    AdmissibleCMBase D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      ((Over.map p).obj T))

local notation "Tests" => HarrisIntegralCMTestCategory D C P p

/-- Forget the map to the fixed family base, retaining its actual CM structure. -/
def harrisIntegralCMTestToCMBase :
    Tests ⥤ AdmissibleCMBaseCategory D C P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      P.square P.universality where
  obj T := ⟨(Over.map p).obj T.obj, T.property⟩
  map f := ObjectProperty.homMk ((Over.map p).map f.hom)
  map_id T := by
    apply ObjectProperty.hom_ext
    exact (Over.map p).map_id T.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (Over.map p).map_comp f.hom g.hom

local notation "toCM" => harrisIntegralCMTestToCMBase D C P p

instance harrisIntegralCMTestConnected (T : Tests) : ConnectedSpace T.obj.left :=
  T.property.connected

instance harrisIntegralCMTestLocallyNoetherian (T : Tests) :
    IsLocallyNoetherian T.obj.left := T.property.locallyNoetherian

instance harrisIntegralCMTestQuasiSeparated (T : Tests) :
    QuasiSeparatedSpace T.obj.left := T.property.quasiSeparated

instance harrisIntegralCMTestMuFinite (T : Tests) (k : Index (fun _ => True)) :
    IsFinite (mu T.obj.left k.val).X.hom := T.property.muFinite k

instance harrisIntegralCMTestMuEtale (T : Tests) (k : Index (fun _ => True)) :
    Etale (mu T.obj.left k.val).X.hom := T.property.muEtale k

variable (B : Langlands.AbelianScheme S) (W : DualWitness B)
    (lam : B ⟶ W.dual P) (hLam : W.IsPolarization P lam)
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n)
    (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (htor : TorsionFiniteEtaleStatement.{0})
    (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})

local notation "family" => unpointedClassTower D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality compatibility h htor
local notation "pull" => unpointedClassTowerPullback D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality dualityNaturality P.polarizationBaseChange compatibility h htor
local notation "ambient" => (toCM).op ⋙ unpointedClassTowerPresheaf
  D C P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability P.square P.universality dualityNaturality
  P.polarizationBaseChange compatibility h htor
local notation "rawAt[" T "," a "," v "]" => harrisIntegralCMFullActionLevelTower
  D C P B W lam (T).obj a compatibility h (v).hom (v).finiteFibers
  htor (T).property.torsionUnits
local notation "toFamily[" T "," a "," ha "," v "]" => harrisIntegralCMFullActionLevelFamilyNatTrans
  D C P p B W lam hLam (T).obj a ha compatibility h htor
  (T).property.torsionUnits (T).property.pairAdditivity hdim v

/-- One actual integral action on the direct family gives the entire normalized
family, using its actual fixed orbits at every geometric point. -/
def HarrisIntegralCMLevelFamilyCondition (T : Tests) {U : HarrisLevel D}
    (x : (family ((toCM).obj T)).obj U) : Prop :=
  ∃ (a : D.harrisHodgePELIntegralOrder C →+*
      CategoryTheory.End ((AbelianScheme.baseChange T.obj.hom).obj B))
    (ha : harrisIntegralCMFullActionCondition D C P p B W lam T.obj a),
    ∀ v : HarrisGeometricPoint T.obj.left,
      ∃ q : (rawAt[T, a, v]).obj U, (toFamily[T, a, ha, v]).app U (ULift.up q) = x

local notation "condition" => HarrisIntegralCMLevelFamilyCondition
  D C P p B W lam hLam hdim compatibility h htor

/-- An orbit at one point supplies the same actual action and orbits at all points. -/
theorem harrisIntegralCMLevelFamilyCondition_of_orbit (T : Tests)
    (a : D.harrisHodgePELIntegralOrder C →+*
      CategoryTheory.End ((AbelianScheme.baseChange T.obj.hom).obj B))
    (ha : harrisIntegralCMFullActionCondition D C P p B W lam T.obj a)
    (v : HarrisGeometricPoint T.obj.left) {U : HarrisLevel D}
    (q : (rawAt[T, a, v]).obj U) :
    condition T ((toFamily[T, a, ha, v]).app U (ULift.up q)) := by
  refine ⟨a, ha, fun w => ?_⟩
  let path := Classical.choice
    (geometricPathExists v.hom w.hom v.finiteFibers w.finiteFibers)
  refine ⟨(harrisIntegralCMFullActionLevelPointIso D C P B W lam T.obj a
    compatibility h htor T.property.torsionUnits path).hom.app U q, ?_⟩
  exact congrArg (fun k => k.app U (ULift.up q))
    (harrisIntegralCMFullActionLevelFamilyNatTrans_pointMap D C P p B W lam
      hLam T.obj a ha compatibility h htor T.property.torsionUnits
      T.property.pairAdditivity hdim v w)

/-- Every original Harris transporter preserves this fixed-family image. -/
theorem harrisIntegralCMLevelFamilyCondition_map (T : Tests)
    {U V : HarrisLevel D} (f : U ⟶ V)
    (x : (family ((toCM).obj T)).obj U) (hx : condition T x) :
    condition T ((family ((toCM).obj T)).map f x) := by
  obtain ⟨a, ha, hq⟩ := hx
  refine ⟨a, ha, fun v => ?_⟩
  obtain ⟨q, hq⟩ := hq v
  refine ⟨(rawAt[T, a, v]).map f q, ?_⟩
  exact (CategoryTheory.types_congr_hom ((toFamily[T, a, ha, v]).naturality f)
    (ULift.up.{1} q)).trans (congrArg ((family ((toCM).obj T)).map f) hq)

/-- Actual base pullback preserves the same fixed-family image. The target
action is the literal restriction of the source action. -/
theorem harrisIntegralCMLevelFamilyCondition_pullback {T T' : Tests} (f : T' ⟶ T)
    {U : HarrisLevel D} (x : (family ((toCM).obj T)).obj U) (hx : condition T x) :
    condition T' ((pull ((toCM).map f)).app U x) := by
  obtain ⟨a, ha, hq⟩ := hx
  let a' := (relativeEndRestrict B f.hom).comp a
  have ha' := harrisIntegralCMFullActionCondition_restrict
    D C P p B W lam f.hom a ha
  refine ⟨a', ha', fun v => ?_⟩
  obtain ⟨q, hq⟩ := hq (v.comp f.hom.left)
  refine ⟨(harrisIntegralCMFullActionLevelRestriction D C P B W lam f.hom a
    compatibility h v.hom v.finiteFibers (v.comp f.hom.left).finiteFibers
    htor T.property.torsionUnits T'.property.torsionUnits).app U q, ?_⟩
  have square := harrisIntegralCMFullActionLevelFamilyNatTrans_baseChange
    D C P B W lam f.hom a compatibility h htor T.property.torsionUnits
    T'.property.torsionUnits p hLam ha dualityNaturality T.property.lieNaturality
    T.property.pairAdditivity T'.property.pairAdditivity
    (unpointedPullbackDualData D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square
      P.universality ((toCM).map f)) hdim v
  exact (congrArg (fun k => k.app U (ULift.up q)) square).trans
    (congrArg ((pull ((toCM).map f)).app U) hq)

/-- The fixed polarized family's exact image as a tower of original classes. -/
def harrisIntegralCMLevelFamilyImageTower (T : Tests) : HarrisLevel D ⥤ Type 1 where
  obj U := {x : (family ((toCM).obj T)).obj U // condition T x}
  map f := ↾(fun x => ⟨(family ((toCM).obj T)).map f x.val,
    harrisIntegralCMLevelFamilyCondition_map D C P p B W lam hLam hdim
      compatibility h htor T f x.val x.property⟩)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((family ((toCM).obj T)).map_id U) x.val
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((family ((toCM).obj T)).map_comp f g) x.val

local notation "imageTower" => harrisIntegralCMLevelFamilyImageTower
  D C P p B W lam hLam hdim compatibility h htor

/-- Restrict the actual normalized pullback to the fixed-family image. -/
def harrisIntegralCMLevelFamilyImagePullback {T T' : Tests} (f : T' ⟶ T) :
    imageTower T ⟶ imageTower T' where
  app U := ↾(fun x => ⟨(pull ((toCM).map f)).app U x.val,
    harrisIntegralCMLevelFamilyCondition_pullback D C P p B W lam hLam hdim
      compatibility h htor dualityNaturality f x.val x.property⟩)
  naturality {U V} g := by
    ext x
    apply Subtype.ext
    exact (pull ((toCM).map f)).naturality_apply g x.val

/-- The actual fixed-family image is a presheaf, with its laws inherited from
the unchanged normalized CM presheaf. -/
def harrisIntegralCMLevelFamilyImagePresheaf :
    Testsᵒᵖ ⥤ (HarrisLevel D ⥤ Type 1) where
  obj T := imageTower T.unop
  map f := harrisIntegralCMLevelFamilyImagePullback D C P p B W lam hLam hdim
    compatibility h htor dualityNaturality f.unop
  map_id T := by
    ext U x
    apply Subtype.ext
    exact congrArg (fun k => k.app U x.val) ((ambient).map_id T)
  map_comp f g := by
    ext U x
    apply Subtype.ext
    exact congrArg (fun k => k.app U x.val) ((ambient).map_comp f g)

local notation "imagePresheaf" => harrisIntegralCMLevelFamilyImagePresheaf
  D C P p B W lam hLam hdim compatibility h htor dualityNaturality

/-- Forget the image witness, naturally in every test map and Harris transporter. -/
def harrisIntegralCMLevelFamilyImageInclusion : imagePresheaf ⟶ ambient where
  app _ := {
    app _ := ↾Subtype.val
    naturality _ _ _ := rfl }
  naturality _ _ _ := rfl

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
