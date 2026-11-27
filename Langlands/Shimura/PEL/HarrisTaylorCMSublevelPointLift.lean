import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedAlignedBaseChange
import Langlands.AbelianScheme.Tate.WeilLevelBaseChange

/-! # Pointed lifting of pulled normalized CM classes to a smaller level -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

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
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω]
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀

variable {S T : Scheme.{0}} [QuasiSeparatedSpace S] [QuasiSeparatedSpace T]
  (b : T ⟶ S) (p : S ⟶ Spec (.of F)) (q : T ⟶ Spec (.of F))
  (t : Spec (.of Ω) ⟶ T) (hp : b ≫ p = q)
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (ht : ∀ Y : Cover T, Finite (Fiber t Y))
  (lieS : LieBaseChangeNaturalityStatement S)
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [hμfinT : ∀ k : Index (fun _ => True), IsFinite (mu T k.val).X.hom]
  [hμetT : ∀ k : Index (fun _ => True), Etale (mu T k.val).X.hom]
  (dualData : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality b X)
  (addS : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))
  (addT : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := T))

local notation "towerS" => HarrisNumericalWeilLevel.isoClassTower D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  (D.harrisTaylorReflexStructure C p) compatibility h (t ≫ b) hs htor huS addS L p
local notation "towerT" => HarrisNumericalWeilLevel.isoClassTower D C hΦ preservation
  composition unitCoherence associativity comparison symmetry stability square universality
  (D.harrisTaylorReflexStructure C q) compatibility h t ht htor huT addT L q
local notation "DataS" => HarrisLevelData D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h
  (t ≫ b) hs htor huS
local notation "GoodS" => PositiveObjectCondition D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  (D.harrisTaylorReflexStructure C p)
local notation "NumS" => HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality L p
local notation "mkS" => HarrisNumericalWeilLevel.classOf D C hΦ preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  (D.harrisTaylorReflexStructure C p) compatibility h (t ≫ b) hs htor huS addS L p
local notation "levelSubgroup" U => ((hodgeLevelFunctor D C).obj U).toSubgroup
local notation "Hsim" =>
  ScalarExtensionSimilitudes A A (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)

/-- Equal representatives give equal normalized classes, whatever the condition proofs. -/
theorem numericalClassOf_congr {U : HarrisLevel D}
    {x y : HarrisLevelData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h t ht htor huT U}
    (hxy : x = y)
    (hx : PositiveObjectCondition D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality (D.harrisTaylorReflexStructure C q) x.1)
    (hy : PositiveObjectCondition D C hΦ preservation composition unitCoherence associativity
      comparison symmetry stability square universality (D.harrisTaylorReflexStructure C q) y.1)
    (hnx : HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality L q x.1)
    (hny : HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality L q y.1) :
    HarrisNumericalWeilLevel.classOf D C hΦ preservation composition unitCoherence
        associativity comparison symmetry stability square universality
        (D.harrisTaylorReflexStructure C q) compatibility h t ht htor huT addT L q x hx hnx =
      HarrisNumericalWeilLevel.classOf D C hΦ preservation composition unitCoherence
        associativity comparison symmetry stability square universality
        (D.harrisTaylorReflexStructure C q) compatibility h t ht htor huT addT L q y hy hny := by
  subst hxy
  rfl

local notation "geo" => rationalWeilGeometricTransport

local notation "FrameA" X:max => Tate.WeilAdelicFrame preservation composition unitCoherence
  associativity comparison symmetry stability (X).hasDual (X).geometry (X).inversePoincare
  (X).evaluation compatibility (X).polarization h (X).actionObj.action A
  (D.harrisHodgePELForm C) (t ≫ b)
local notation "rightA" X:max => Tate.weilAdelicFrameRightAction preservation composition
  unitCoherence associativity comparison symmetry stability (X).hasDual (X).geometry
  (X).inversePoincare (X).evaluation compatibility (X).polarization h (X).actionObj.action A
  (D.harrisHodgePELForm C) (t ≫ b)
local notation "monA" X:max => Tate.weilAdelicFrameMonodromyAction preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  geo (X).hasDual (X).geometry (X).inversePoincare
  (X).evaluation (X).polarization h (X).actionObj.action A (D.harrisHodgePELForm C)
  (t ≫ b) hs htor huS (hμfin := hμfinS) (hμet := hμetS)
local notation "commA" X:max => Tate.weilAdelicFrameActionsComm preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  geo (X).hasDual (X).geometry (X).inversePoincare
  (X).evaluation (X).polarization h (X).actionObj.action A (D.harrisHodgePELForm C)
  (t ≫ b) hs htor huS (hμfin := hμfinS) (hμet := hμetS)
local notation "lamBC" X:max W:max => canonicalDualValuedBaseChange b (X).actionObj.abelianScheme
  preservation composition unitCoherence associativity comparison symmetry stability
  universality (X).hasDual (X).geometry (X).inversePoincare (X).evaluation (W).hasDual
  (W).geometry (W).inversePoincare (W).evaluation (X).polarization
local notation "iBC" X:max => (rationalBaseChangeEnd b (X).actionObj.abelianScheme).comp
  (X).actionObj.action
local notation "Frameb" X:max W:max => Tate.WeilAdelicFrame preservation composition
  unitCoherence associativity comparison symmetry stability (W).hasDual (W).geometry
  (W).inversePoincare (W).evaluation compatibility (lamBC X W) h (iBC X) A
  (D.harrisHodgePELForm C) t
local notation "rightb" X:max W:max => Tate.weilAdelicFrameRightAction preservation
  composition unitCoherence associativity comparison symmetry stability (W).hasDual
  (W).geometry (W).inversePoincare (W).evaluation compatibility (lamBC X W) h (iBC X) A
  (D.harrisHodgePELForm C) t
local notation "monb" X:max W:max => Tate.weilAdelicFrameMonodromyAction preservation
  composition unitCoherence associativity comparison symmetry stability compatibility
  geo (W).hasDual (W).geometry (W).inversePoincare (W).evaluation (lamBC X W) h (iBC X) A
  (D.harrisHodgePELForm C) t ht htor huT (hμfin := hμfinT) (hμet := hμetT)
local notation "commb" X:max W:max => Tate.weilAdelicFrameActionsComm preservation
  composition unitCoherence associativity comparison symmetry stability compatibility
  geo (W).hasDual (W).geometry (W).inversePoincare (W).evaluation (lamBC X W) h (iBC X) A
  (D.harrisHodgePELForm C) t ht htor huT (hμfin := hμfinT) (hμet := hμetT)
local notation "frameBC" X:max W:max => Tate.weilAdelicFrameBaseChange b (X).actionObj.abelianScheme
  preservation composition unitCoherence associativity comparison symmetry stability
  universality (X).hasDual (X).geometry (X).inversePoincare (X).evaluation (W).hasDual
  (W).geometry (W).inversePoincare (W).evaluation compatibility (X).polarization h
  (X).actionObj.action A (D.harrisHodgePELForm C) t
local notation "frameRight" X:max W:max => Tate.weilAdelicFrameBaseChange_right b
  (X).actionObj.abelianScheme preservation composition unitCoherence associativity comparison
  symmetry stability universality (X).hasDual (X).geometry (X).inversePoincare (X).evaluation
  (W).hasDual (W).geometry (W).inversePoincare (W).evaluation compatibility (X).polarization h
  (X).actionObj.action A (D.harrisHodgePELForm C) t
local notation "frameMon" X:max W:max => Tate.weilAdelicFrameBaseChange_monodromy b
  (X).actionObj.abelianScheme preservation composition unitCoherence associativity comparison
  symmetry stability universality (X).hasDual (X).geometry (X).inversePoincare (X).evaluation
  (W).hasDual (W).geometry (W).inversePoincare (W).evaluation compatibility (X).polarization h
  (X).actionObj.action A (D.harrisHodgePELForm C) t ht hs htor huS huT
  (hμfin := hμfinS) (hμet := hμetS) (hμfin' := hμfinT) (hμet' := hμetT)
local notation "orbitBC" X:max W:max => Tate.weilAdelicFrameRightOrbitBaseChange b
  (X).actionObj.abelianScheme preservation composition unitCoherence associativity comparison
  symmetry stability universality (X).hasDual (X).geometry (X).inversePoincare (X).evaluation
  (W).hasDual (W).geometry (W).inversePoincare (W).evaluation compatibility (X).polarization h
  (X).actionObj.action A (D.harrisHodgePELForm C) t
local notation "pullData" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability b compatibility h t ht hs htor huS huT dualData

include lieS in
/-- Pointed sublevel lifting. Let `x` be a representative at level `U` over the point
`t ≫ b`, and let `eta` be a frame in its level orbit. If the image of `π₁(T, t)` fixes
the raw orbit of `eta` at the smaller level `U'`, then the aligned pullback of the class
of `x` is the image of a class at level `U'` under the forgetting transition. -/
theorem classTowerBaseChangeAlong_exists_sublevel
    {U U' : HarrisLevel D} (hle : U'.subgroup ≤ U.subgroup) (x : DataS U)
    (hx : GoodS x.1) (hn : NumS x.1) :
    letI := auxiliaryStarRing D C
    letI : MulAction Hsimᵐᵒᵖ (FrameA x.1) := rightA x.1
    letI : MulAction (FundamentalGroup (t ≫ b) hs) (FrameA x.1) := monA x.1
    letI : SMulCommClass (FundamentalGroup (t ≫ b) hs) Hsimᵐᵒᵖ (FrameA x.1) := commA x.1
    ∀ eta : FrameA x.1, RightOrbit.mk (levelSubgroup U) eta = x.2.val →
      (∀ σ : FundamentalGroup t ht,
        fundamentalGroupMap b t (t ≫ b) rfl ht hs σ • RightOrbit.mk (levelSubgroup U') eta =
          RightOrbit.mk (levelSubgroup U') eta) →
      ∃ z : (towerT).obj U',
        (towerT).map (CompactOpenLevel.inclusion hle) z =
          (classTowerBaseChangeAlong D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality dualityNaturality
            polarizationStability compatibility h htor b p q (t ≫ b) t hp rfl hs ht lieS
            huS huT dualData addS addT).app U (mkS x hx hn) := by
  subst hp
  let := auxiliaryStarRing D C
  intro eta heta hfix
  let W := dualData x.1
  let Y := (pullData U x).1
  let := rightb x.1 W
  let := rightA x.1
  let := monb x.1 W
  let := monA x.1
  let := commb x.1 W
  let := commA x.1
  let q' : RightOrbit (Frameb x.1 W) (levelSubgroup U') :=
    ((orbitBC x.1 W) (levelSubgroup U')).symm (RightOrbit.mk (levelSubgroup U') eta)
  have hq' : q' ∈ MulAction.fixedPoints (FundamentalGroup t ht)
      (RightOrbit (Frameb x.1 W) (levelSubgroup U')) := by
    intro σ
    apply ((orbitBC x.1 W) (levelSubgroup U')).injective
    have key := RightOrbit.map_smul (levelSubgroup U')
      (fundamentalGroupMap b t (t ≫ b) rfl ht hs) (frameBC x.1 W) (frameRight x.1 W)
      (frameMon x.1 W) σ q'
    change RightOrbit.map (levelSubgroup U') (frameBC x.1 W) (frameRight x.1 W) (σ • q') =
      ((orbitBC x.1 W) (levelSubgroup U')) q'
    rw [key]
    change fundamentalGroupMap b t (t ≫ b) rfl ht hs σ •
        ((orbitBC x.1 W) (levelSubgroup U')) q' = ((orbitBC x.1 W) (levelSubgroup U')) q'
    rw [Equiv.apply_symm_apply]
    exact hfix σ
  let O' : (PolarizedWeilLevel.levelTower preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h A
      (D.harrisHodgePELForm C) t ht htor huT Y).obj ((hodgeLevelFunctor D C).obj U') :=
    ⟨q', hq'⟩
  have hgood := levelDataBaseChange_objectCondition D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability b compatibility h t ht hs htor huS huT dualData p lieS x hx
  have hnum := HarrisNumericalWeilLevel.levelDataBaseChange_numericalObjectCondition D C
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability b compatibility h t ht hs
    htor huS huT dualData lieS L p x hn
  refine ⟨HarrisNumericalWeilLevel.classOf D C hΦ preservation composition unitCoherence
    associativity comparison symmetry stability square universality
    (D.harrisTaylorReflexStructure C (b ≫ p)) compatibility h t ht htor huT addT L (b ≫ p)
    ⟨Y, O'⟩ hgood hnum, ?_⟩
  have hxy : HarrisNumericalWeilLevel.mapRepresentative D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      compatibility h t ht htor huT (CompactOpenLevel.inclusion hle) ⟨Y, O'⟩ = pullData U x := by
    refine Sigma.ext ?_ ?_
    · rfl
    apply heq_of_eq
    apply Subtype.ext
    have hq'mk : q' = RightOrbit.mk (levelSubgroup U') ((frameBC x.1 W).symm eta) := rfl
    show RightOrbit.translate (G := Hsim) ((hodgeLevelFunctor D C).map (CompactOpenLevel.inclusion hle)).element
        ((hodgeLevelFunctor D C).map (CompactOpenLevel.inclusion hle)).respects q' =
      ((orbitBC x.1 W) (levelSubgroup U)).symm x.2.val
    rw [← heta, hq'mk, RightOrbit.translate_mk, hodgeLevelFunctor_map_element]
    change _ = RightOrbit.mk (levelSubgroup U) ((frameBC x.1 W).symm eta)
    congr 1
    rw [show (CompactOpenLevel.inclusion hle).element = 1 from rfl, map_one, right_one]
  exact numericalClassOf_congr D C preservation composition unitCoherence associativity
    comparison symmetry stability square universality compatibility h htor (b ≫ p) t ht huT
    addT hxy hgood hgood hnum hnum

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
