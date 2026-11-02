import Langlands.Shimura.PEL.HarrisIntegralRestrictionBaseChange
import Langlands.Shimura.PEL.HarrisIntegralOrderActions

/-! # Fixed rational-isomorphism orbit comparison under actual Harris pullback -/

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
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
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
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  {S T : Scheme.{0}} (b : T ⟶ S)

local notation "PObjS" => PositivePolarizedAction D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality (S := S)

variable [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (t : Spec (.of Ω) ⟶ T)
  (ht : ∀ Y : Cover T, Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T k.val).X.hom]
  [hμetT : ∀ k : Index (fun _ => True), Etale (mu T k.val).X.hom]
  (dualData : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality b X)

local notation "DataS" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  (t ≫ b) hs htor huS
local notation "DataT" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  t ht htor huT
local notation "indexFunctor" => hodgeLevelFunctor D C

local notation "pullData" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData


local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "Restriction" => PolarizedWeilLevel.IntegralActionRestriction preservation
  composition unitCoherence associativity comparison symmetry stability square universality
local notation "IntegralMult" => PolarizedWeilLevel.IntegralPolarizedMultiple preservation
  composition unitCoherence associativity comparison symmetry stability square universality

local notation "pullRestriction" => levelDataIntegralRestrictionBaseChange D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData

variable
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))

local notation "MultS" => PolarizedWeilLevel.Multiple preservation composition unitCoherence
  associativity comparison symmetry stability square universality addS
local notation "MultT" => PolarizedWeilLevel.Multiple preservation composition unitCoherence
  associativity comparison symmetry stability square universality addT
local notation "transportS" => PolarizedWeilLevel.levelIso preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C) (t ≫ b) hs htor huS addS
local notation "transportT" => PolarizedWeilLevel.levelIso preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C) t ht htor huT addT

set_option maxHeartbeats 2400000 in
/-- For the same rational isomorphism and multiplier, the actual fixed-orbit equation
holds before pointed pullback exactly when it holds afterwards. -/
theorem levelDataBaseChange_levelIso_iff {U : HarrisLevel D} (x y : DataS U) :
    letI := auxiliaryStarRing D C
    ∀ (q : ℚˣ) (e : x.1.actionObj ≅ y.1.actionObj)
      (he : MultS x.1 y.1 q e)
      (heb : MultT (pullData U x).1 (pullData U y).1 q
        ((RationalAlgebraAction.pullback b).mapIso e)),
    transportS x.1 y.1 ((indexFunctor).obj U) q e he x.2 = y.2 ↔
      transportT (pullData U x).1 (pullData U y).1 ((indexFunctor).obj U) q
        ((RationalAlgebraAction.pullback b).mapIso e) heb (pullData U x).2 =
          (pullData U y).2 := by
  let := auxiliaryStarRing D C
  intro q e he heb
  let Wx := dualData x.1
  let Wy := dualData y.1
  let xb := pullData U x
  let yb := pullData U y
  have hcanonical := IsRationalDualPullbackMultiple.integral_baseChange_of_naturality
      preservation stability composition unitCoherence associativity comparison symmetry
      universality dualAbelianBaseChange b x.1.actionObj.abelianScheme y.1.actionObj.abelianScheme
      x.1.hasDual x.1.geometry x.1.inversePoincare x.1.evaluation
      y.1.hasDual y.1.geometry y.1.inversePoincare y.1.evaluation
      Wx.hasDual Wx.geometry Wx.inversePoincare Wx.evaluation
      Wy.hasDual Wy.geometry Wy.inversePoincare Wy.evaluation
      (addS x.1 y.1) (addT xb.1 yb.1) dualityNaturality (q : ℚ)
      (RationalAlgebraAction.underlyingIso e).hom x.1.polarization y.1.polarization he
  have squareAt := Tate.weilAdelicLevelIsogeny_baseChange
    (A := x.1.actionObj.abelianScheme) (B := y.1.actionObj.abelianScheme) (D := A)
    b preservation composition
    unitCoherence associativity comparison symmetry stability universality
    x.1.hasDual x.1.geometry x.1.inversePoincare x.1.evaluation x.1.polarization
    y.1.hasDual y.1.geometry y.1.inversePoincare y.1.evaluation y.1.polarization
    Wx.hasDual Wx.geometry Wx.inversePoincare Wx.evaluation
    Wy.hasDual Wy.geometry Wy.inversePoincare Wy.evaluation
    (addS x.1 y.1) (addT xb.1 yb.1) compatibility h
    x.1.actionObj.action y.1.actionObj.action A (D.harrisHodgePELForm C) t
    (hμfin := hμfinS) (hμet := hμetS) (hμfinb := hμfinT) (hμetb := hμetT)
  have hsquare := squareAt q (RationalAlgebraAction.underlyingIso e)
    (RationalAlgebraAction.intertwines e.hom) he
    (by simpa only [canonicalDualValuedBaseChange, rationalBaseChangeIso_hom, homToHom0]
      using hcanonical) ht hs htor huS huT ((indexFunctor).obj U).toSubgroup x.2
  let pullY := Tate.weilAdelicLevelBaseChange b y.1.actionObj.abelianScheme
    preservation composition unitCoherence associativity comparison symmetry stability
    universality y.1.hasDual y.1.geometry y.1.inversePoincare y.1.evaluation
    Wy.hasDual Wy.geometry Wy.inversePoincare Wy.evaluation compatibility y.1.polarization
    h y.1.actionObj.action A (D.harrisHodgePELForm C) t ht hs htor huS huT
    ((indexFunctor).obj U).toSubgroup
  have hsquareAligned :
      pullY (transportS x.1 y.1 ((indexFunctor).obj U) q e he x.2) =
        transportT (pullData U x).1 (pullData U y).1 ((indexFunctor).obj U) q
          ((RationalAlgebraAction.pullback b).mapIso e) heb (pullData U x).2 :=
    hsquare
  have hinj : Function.Injective pullY :=
    Tate.weilAdelicLevelBaseChange_injective b y.1.actionObj.abelianScheme
      preservation composition unitCoherence associativity comparison symmetry stability
      universality y.1.hasDual y.1.geometry y.1.inversePoincare y.1.evaluation
      Wy.hasDual Wy.geometry Wy.inversePoincare Wy.evaluation compatibility y.1.polarization
      h y.1.actionObj.action A (D.harrisHodgePELForm C) t ht hs htor huS huT
      ((indexFunctor).obj U).toSubgroup
  constructor
  · intro hxy
    exact hsquareAligned.symm.trans (congrArg pullY hxy)
  · intro hxy
    exact hinj (hsquareAligned.trans hxy)

local notation "basisO" => D.harrisHodgePELIntegralBasis C
local notation "restoreS" => PolarizedWeilLevel.multiple_iff_integralPolarizedMultiple
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality basisO addS
local notation "restoreT" => PolarizedWeilLevel.multiple_iff_integralPolarizedMultiple
  preservation composition unitCoherence associativity comparison symmetry stability
  square universality basisO addT
local notation "pullIntegral" => levelDataIntegralPolarizedMultiple_baseChange D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  dualityNaturality polarizationStability b compatibility h t ht hs htor huS huT dualData

/-- The fixed-isomorphism orbit criterion uses the transported supplied integral
witnesses and exactly the original multiplier on both sides. -/
theorem levelDataIntegralPolarizedMultiple_levelIso_baseChange_iff
    {U : HarrisLevel D} (x y : DataS U) :
    letI := auxiliaryStarRing D C
    ∀ (a : Restriction O x.1) (a' : Restriction O y.1)
      (q : ℚˣ) (e : x.1.actionObj ≅ y.1.actionObj)
      (hd : IntegralMult x.1 y.1 a a' q e),
    transportS x.1 y.1 ((indexFunctor).obj U) q e
        ((restoreS x.1 y.1 a a' q e).mpr hd) x.2 = y.2 ↔
      transportT (pullData U x).1 (pullData U y).1 ((indexFunctor).obj U) q
        ((RationalAlgebraAction.pullback b).mapIso e)
        ((restoreT (pullData U x).1 (pullData U y).1
          (pullRestriction x a) (pullRestriction y a') q
          ((RationalAlgebraAction.pullback b).mapIso e)).mpr
            (pullIntegral x y a a' q e hd))
        (pullData U x).2 = (pullData U y).2 := by
  let := auxiliaryStarRing D C
  intro a a' q e hd
  exact levelDataBaseChange_levelIso_iff D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h t ht hs htor huS huT dualData addS addT x y
    q e _ _

/-- Pointed pullback gives an equivalence of integral orbit-witness pairs.
Its underlying map and inverse retain the original multiplier and isomorphism. -/
def integralPolarizedLevelWitnessBaseChangeEquiv {U : HarrisLevel D} (x y : DataS U) :
    letI := auxiliaryStarRing D C
    ∀ (a : Restriction O x.1) (a' : Restriction O y.1),
    {z : ℚˣ × (x.1.actionObj ≅ y.1.actionObj) //
      ∃ hd : IntegralMult x.1 y.1 a a' z.1 z.2,
        transportS x.1 y.1 ((indexFunctor).obj U) z.1 z.2
          ((restoreS x.1 y.1 a a' z.1 z.2).mpr hd) x.2 = y.2} ≃
    {z : ℚˣ × (x.1.actionObj ≅ y.1.actionObj) //
      ∃ hd : IntegralMult x.1 y.1 a a' z.1 z.2,
        transportT (pullData U x).1 (pullData U y).1 ((indexFunctor).obj U) z.1
          ((RationalAlgebraAction.pullback b).mapIso z.2)
          ((restoreT (pullData U x).1 (pullData U y).1
            (pullRestriction x a) (pullRestriction y a') z.1
            ((RationalAlgebraAction.pullback b).mapIso z.2)).mpr
              (pullIntegral x y a a' z.1 z.2 hd))
          (pullData U x).2 = (pullData U y).2} := by
  let := auxiliaryStarRing D C
  intro a a'
  refine Equiv.subtypeEquivRight ?_
  intro z
  exact exists_congr fun hd =>
    levelDataIntegralPolarizedMultiple_levelIso_baseChange_iff D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability b compatibility h t ht hs htor
      huS huT dualData addS addT x y a a' z.1 z.2 hd

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
