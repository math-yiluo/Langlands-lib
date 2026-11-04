import Langlands.Shimura.PEL.HarrisIntegralCMLevelClass
import Langlands.Shimura.PEL.HarrisTaylorCMIntegralPointComparison
import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedGeometricFamilies

/-! # Point independence of actual integral Harris Weil-level classes -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
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
    (B : Langlands.AbelianScheme S) (W : DualWitness B)
    (lam : B ⟶ W.dual P) (hLam : W.IsPolarization P lam)
    (T : Over S) [QuasiSeparatedSpace T.left]
    (a : D.harrisHodgePELIntegralOrder C →+*
      CategoryTheory.End ((AbelianScheme.baseChange T.hom).obj B))
    (ha : harrisIntegralCMFullActionCondition D C P p B W lam T a)
    (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    {Ω Ω' : Type} [Field Ω] [Field Ω']
    {s : Spec (.of Ω) ⟶ T.left} {t : Spec (.of Ω') ⟶ T.left}
    {hs : ∀ Y : Cover T.left, Finite (Fiber s Y)}
    {ht : ∀ Y : Cover T.left, Finite (Fiber t Y)}
    (htor : TorsionFiniteEtaleStatement.{0})
    (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T.left, ⊤)))
    [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom]
    [hμet : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom]

local notation "BT" => (AbelianScheme.baseChange T.hom).obj B
local notation "WT" => W.pullback P T.hom
local notation "lamT" => W.pullbackMap P T.hom WT lam
local notation "iT" => D.harrisHodgePELRationalAction C BT a

local notation "rawAt" => harrisIntegralCMFullActionLevelTower
  D C P B W lam T a compatibility h
local notation "representativeAt" => harrisIntegralCMFullActionLevelRepresentative
  D C P p B W lam hLam T a ha compatibility h

/-- Compare the original-index raw level towers using actual fixed-orbit transport. -/
def harrisIntegralCMFullActionLevelPointIso
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) :
    rawAt s hs htor hu ≅ rawAt t ht htor hu :=
  Functor.isoWhiskerLeft (hodgeLevelFunctor D C)
    (Tate.weilAdelicCompactOpenLevelTransport P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      compatibility (WT).hasDual (WT).geometry (WT).inverseBundle (WT).evaluation
      lamT h iT A (D.harrisHodgePELForm C) htor hu path)

local notation "rawPoint" => harrisIntegralCMFullActionLevelPointIso
  D C P B W lam T a compatibility h htor hu

/-- No auxiliary fibre-functor path is remembered by this raw tower comparison. -/
theorem harrisIntegralCMFullActionLevelPointIso_path_independent
    (path path' : fiberFunctor s hs ≅ fiberFunctor t ht) :
    rawPoint path = rawPoint path' :=
  congrArg (Functor.isoWhiskerLeft (hodgeLevelFunctor D C))
    (Tate.weilAdelicCompactOpenLevelTransport_path_independent P.preservation
      P.composition P.unitCoherence P.associativity P.comparison P.symmetry
      P.stability compatibility (WT).hasDual (WT).geometry (WT).inverseBundle
      (WT).evaluation lamT h iT A (D.harrisHodgePELForm C) htor hu path path')

/-- Point transport changes only the orbit in the actual integral representative. -/
theorem harrisIntegralCMFullActionLevelRepresentative_pointMap
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n)
    (path : fiberFunctor s hs ≅ fiberFunctor t ht)
    (U : HarrisLevel D) (q : (rawAt s hs htor hu).obj U) :
    representativeAt t ht htor hu hdim ((rawPoint path).hom.app U q) =
      HarrisTaylorCMWeilLevel.integralCMRepresentativePointMap D C P.preservation
        P.composition P.unitCoherence P.associativity P.comparison P.symmetry
        P.stability P.square P.universality (T.hom ≫ p) compatibility h htor hu
        path U (representativeAt s hs htor hu hdim q) := rfl

variable
    (additivity : PositivePairAdditivity D C P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      P.square P.universality (S := T.left))

local notation "originalAt" => HarrisNumericalWeilLevel.isoClassTower D C
  (isCMSection_harrisCMSection E (algebraMap L F) τ₀) P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality (D.harrisTaylorReflexStructure C (T.hom ≫ p)) compatibility h
local notation "repClassAt" => HarrisTaylorCMWeilLevel.integralCMRepresentativeClass
  D C P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability P.square P.universality (T.hom ≫ p) compatibility h
local notation "classPoint" => HarrisTaylorCMWeilLevel.classPointTowerIso D C
  P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability P.square P.universality (T.hom ≫ p) compatibility h
  htor hu additivity

/-- Forget the supplied integral action into the unchanged original normalized CM tower. -/
def harrisIntegralCMFullActionLevelOriginalClassNatTrans
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n)
    (s : Spec (.of Ω) ⟶ T.left) (hs : ∀ Y : Cover T.left, Finite (Fiber s Y)) :
    rawAt s hs htor hu ⋙ uliftFunctor.{1} ⟶
      originalAt s hs htor hu additivity L (T.hom ≫ p) where
  app _ := ↾(fun q => repClassAt s hs htor hu additivity
    (representativeAt s hs htor hu hdim q.down))
  naturality := by
    intro U V f
    ext q
    rfl

local notation "toOriginal" => harrisIntegralCMFullActionLevelOriginalClassNatTrans
  D C P p B W lam hLam T a ha compatibility h htor hu additivity

/-- The raw-orbit class construction commutes with every actual point path. -/
theorem harrisIntegralCMFullActionLevelOriginalClassNatTrans_pointMap
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n)
    (path : fiberFunctor s hs ≅ fiberFunctor t ht) :
    Functor.whiskerRight (rawPoint path).hom uliftFunctor.{1} ≫ toOriginal hdim t ht =
      toOriginal hdim s hs ≫ (classPoint path).hom := by
  ext U q
  rfl

section Geometric

variable [ConnectedSpace T.left] [IsLocallyNoetherian T.left]

local notation "Point" => HarrisTaylorCMWeilLevel.HarrisGeometricPoint T.left
local notation "familyTower" => HarrisTaylorCMWeilLevel.compatibleGeometricFamilyTower
  D C P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability P.square P.universality (T.hom ≫ p) compatibility h htor
  hu additivity
local notation "evaluate" => HarrisTaylorCMWeilLevel.geometricFamilyEvaluationIso
  D C P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability P.square P.universality (T.hom ≫ p) compatibility h htor
  hu additivity
local notation "comparison" => HarrisTaylorCMWeilLevel.geometricClassComparison
  D C P.preservation P.composition P.unitCoherence P.associativity P.comparison
  P.symmetry P.stability P.square P.universality (T.hom ≫ p) compatibility h htor
  hu additivity

/-- An actual orbit at one geometric point gives the existing compatible family
of normalized classes at every actual geometric point. -/
def harrisIntegralCMFullActionLevelFamilyNatTrans
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n) (v : Point) :
    rawAt v.hom v.finiteFibers htor hu ⋙ uliftFunctor.{1} ⟶ familyTower :=
  toOriginal hdim v.hom v.finiteFibers ≫ (evaluate v).inv

local notation "toFamily" => harrisIntegralCMFullActionLevelFamilyNatTrans
  D C P p B W lam hLam T a ha compatibility h htor hu additivity

/-- Evaluation at the starting point returns the unchanged normalized class. -/
theorem harrisIntegralCMFullActionLevelFamilyNatTrans_evaluate
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n) (v : Point) :
    toFamily hdim v ≫ (evaluate v).hom = toOriginal hdim v.hom v.finiteFibers := by
  simp only [harrisIntegralCMFullActionLevelFamilyNatTrans, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Changing the starting geometric point and its orbit gives the same actual family. -/
theorem harrisIntegralCMFullActionLevelFamilyNatTrans_pointMap
    (hdim : HarrisTaylor.PrescribedRelativeDimension E B n) (v w : Point) :
    Functor.whiskerRight
      (rawPoint (Classical.choice (geometricPathExists v.hom w.hom
        v.finiteFibers w.finiteFibers))).hom uliftFunctor.{1} ≫ toFamily hdim w =
      toFamily hdim v := by
  apply (cancel_mono (evaluate w).hom).1
  rw [Category.assoc, harrisIntegralCMFullActionLevelFamilyNatTrans_evaluate]
  rw [harrisIntegralCMFullActionLevelOriginalClassNatTrans_pointMap]
  have hcomp := HarrisTaylorCMWeilLevel.geometricFamilyEvaluationIso_comparison
    D C P.preservation P.composition P.unitCoherence P.associativity P.comparison
    P.symmetry P.stability P.square P.universality (T.hom ≫ p) compatibility h htor
    hu additivity v w
  have hhom : (evaluate v).hom ≫ (comparison v w).hom = (evaluate w).hom :=
    congrArg Iso.hom hcomp
  change toOriginal hdim v.hom v.finiteFibers ≫ (comparison v w).hom =
    (toOriginal hdim v.hom v.finiteFibers ≫ (evaluate v).inv) ≫ (evaluate w).hom
  rw [← hhom, Category.assoc, ← Category.assoc (evaluate v).inv,
    Iso.inv_hom_id, Category.id_comp]

end Geometric
end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
