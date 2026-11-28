import Langlands.Shimura.PEL.HarrisPolarizedClassBaseChange
import Langlands.AlgebraicGeometry.Picard.RationalDualPullbackReflection

/-! # Explicit pulled-back witnesses of the Harris polarized isogeny relation -/

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

variable
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))

local notation "relS" => PolarizedWeilLevel.isogenySetoid preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C) (t ≫ b) hs htor huS addS
local notation "relT" => PolarizedWeilLevel.isogenySetoid preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C) t ht htor huT addT


set_option maxHeartbeats 2400000 in
/-- The pullback of an actual witness of the polarized isogeny relation along an
actual base map is a witness for the pulled-back representatives: the multiplier
is unchanged and the rational isomorphism is the pulled-back one. -/
theorem levelDataBaseChange_witness {U : HarrisLevel D} (x y : DataS U) :
    letI := auxiliaryStarRing D C
    ∀ (q : ℚˣ) (e : x.1.actionObj ≅ y.1.actionObj)
      (he : PolarizedWeilLevel.Multiple preservation composition unitCoherence
        associativity comparison symmetry stability square universality addS x.1 y.1 q e),
      PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
          comparison symmetry stability square universality compatibility h A
          (D.harrisHodgePELForm C) (t ≫ b) hs htor huS addS x.1 y.1
          ((indexFunctor).obj U) q e he x.2 = y.2 →
      ∃ heb : PolarizedWeilLevel.Multiple preservation composition unitCoherence
          associativity comparison symmetry stability square universality addT
          (pullData U x).1 (pullData U y).1 q ((RationalAlgebraAction.pullback b).mapIso e),
        PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
          comparison symmetry stability square universality compatibility h A
          (D.harrisHodgePELForm C) t ht htor huT addT (pullData U x).1 (pullData U y).1
          ((indexFunctor).obj U) q ((RationalAlgebraAction.pullback b).mapIso e) heb
          (pullData U x).2 = (pullData U y).2 := by
  let := auxiliaryStarRing D C
  intro q e he hxy
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
  have heb : PolarizedWeilLevel.Multiple preservation composition unitCoherence
      associativity comparison symmetry stability square universality addT xb.1 yb.1 q
      ((RationalAlgebraAction.pullback b).mapIso e) :=
    hcanonical
  refine ⟨heb, ?_⟩
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
  have squareFor := squareAt q (RationalAlgebraAction.underlyingIso e)
  have squareIntertwines := squareFor (RationalAlgebraAction.intertwines e.hom)
  have squareSource := squareIntertwines he
  have hsquare := squareSource
    (by simpa only [canonicalDualValuedBaseChange, rationalBaseChangeIso_hom, homToHom0]
      using hcanonical) ht hs htor huS huT
    ((indexFunctor).obj U).toSubgroup x.2
  have hxyb := congrArg
    (Tate.weilAdelicLevelBaseChange b y.1.actionObj.abelianScheme preservation composition
      unitCoherence associativity comparison symmetry stability universality
      y.1.hasDual y.1.geometry y.1.inversePoincare y.1.evaluation
      Wy.hasDual Wy.geometry Wy.inversePoincare Wy.evaluation compatibility
      y.1.polarization h y.1.actionObj.action A (D.harrisHodgePELForm C) t
      ht hs htor huS huT ((indexFunctor).obj U).toSubgroup) hxy
  exact hsquare.symm.trans hxyb

set_option maxHeartbeats 2400000 in
/-- Reflection of the level condition along an actual base map: if the pulled-back
rational isomorphism transports the pulled-back orbit, then the original rational
isomorphism transports the original orbit. This uses injectivity of pointed
pullback of fixed orbits. -/
theorem levelDataBaseChange_reflect {U : HarrisLevel D} (x y : DataS U) :
    letI := auxiliaryStarRing D C
    ∀ (q : ℚˣ) (e : x.1.actionObj ≅ y.1.actionObj)
      (he : PolarizedWeilLevel.Multiple preservation composition unitCoherence
        associativity comparison symmetry stability square universality addS x.1 y.1 q e)
      (heb : PolarizedWeilLevel.Multiple preservation composition unitCoherence
          associativity comparison symmetry stability square universality addT
          (pullData U x).1 (pullData U y).1 q ((RationalAlgebraAction.pullback b).mapIso e)),
      PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
          comparison symmetry stability square universality compatibility h A
          (D.harrisHodgePELForm C) t ht htor huT addT (pullData U x).1 (pullData U y).1
          ((indexFunctor).obj U) q ((RationalAlgebraAction.pullback b).mapIso e) heb
          (pullData U x).2 = (pullData U y).2 →
      PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
          comparison symmetry stability square universality compatibility h A
          (D.harrisHodgePELForm C) (t ≫ b) hs htor huS addS x.1 y.1
          ((indexFunctor).obj U) q e he x.2 = y.2 := by
  let := auxiliaryStarRing D C
  intro q e he heb hT
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
  have squareFor := squareAt q (RationalAlgebraAction.underlyingIso e)
  have squareIntertwines := squareFor (RationalAlgebraAction.intertwines e.hom)
  have squareSource := squareIntertwines he
  have hsquare := squareSource
    (by simpa only [canonicalDualValuedBaseChange, rationalBaseChangeIso_hom, homToHom0]
      using hcanonical) ht hs htor huS huT
    ((indexFunctor).obj U).toSubgroup x.2
  apply Tate.weilAdelicLevelBaseChange_injective b y.1.actionObj.abelianScheme preservation
    composition unitCoherence associativity comparison symmetry stability universality
    y.1.hasDual y.1.geometry y.1.inversePoincare y.1.evaluation
    Wy.hasDual Wy.geometry Wy.inversePoincare Wy.evaluation compatibility
    y.1.polarization h y.1.actionObj.action A (D.harrisHodgePELForm C) t
    ht hs htor huS huT ((indexFunctor).obj U).toSubgroup
  exact hsquare.trans hT

/-- Reflection of the polarization condition along an actual base map along which
rational pullback is injective: if the pulled-back rational isomorphism multiplies
the pulled-back polarizations by `q`, so does the original one. -/
theorem levelDataBaseChange_multiple_reflect
    (hinj : ∀ (B B' : AbelianScheme S) (r : Hom0 B B'), rationalBaseChangeHom b r = 0 → r = 0)
    {U : HarrisLevel D} (x y : DataS U) :
    letI := auxiliaryStarRing D C
    ∀ (q : ℚˣ) (e : x.1.actionObj ≅ y.1.actionObj),
      PolarizedWeilLevel.Multiple preservation composition unitCoherence associativity
          comparison symmetry stability square universality addT
          (pullData U x).1 (pullData U y).1 q ((RationalAlgebraAction.pullback b).mapIso e) →
      PolarizedWeilLevel.Multiple preservation composition unitCoherence associativity
        comparison symmetry stability square universality addS x.1 y.1 q e := by
  let := auxiliaryStarRing D C
  intro q e heb
  let Wx := dualData x.1
  let Wy := dualData y.1
  exact IsRationalDualPullbackMultiple.integral_of_baseChange_of_naturality preservation
    stability composition unitCoherence associativity comparison symmetry universality
    dualAbelianBaseChange b x.1.actionObj.abelianScheme y.1.actionObj.abelianScheme
    x.1.hasDual x.1.geometry x.1.inversePoincare x.1.evaluation
    y.1.hasDual y.1.geometry y.1.inversePoincare y.1.evaluation
    Wx.hasDual Wx.geometry Wx.inversePoincare Wx.evaluation
    Wy.hasDual Wy.geometry Wy.inversePoincare Wy.evaluation
    (addS x.1 y.1) (addT (pullData U x).1 (pullData U y).1) dualityNaturality (hinj _ _)
    (q : ℚ) (RationalAlgebraAction.underlyingIso e).hom x.1.polarization y.1.polarization heb

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
