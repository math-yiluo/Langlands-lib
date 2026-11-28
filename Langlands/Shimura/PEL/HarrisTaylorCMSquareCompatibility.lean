import Langlands.Shimura.PEL.HarrisTaylorCMConnectedRigidity
import Langlands.Shimura.PEL.HarrisTaylorCMWitnessTransport
import Langlands.Shimura.PEL.PolarizedWeilLevelWitness
import Langlands.AbelianScheme.RationalAlgebraActionSquare

/-! # Pulled-back witnesses of the normalized CM class relation around commuting squares -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

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
  (htor : TorsionFiniteEtaleStatement.{0})


local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀

section EqTransport

variable {S Z : Scheme.{0}} [QuasiSeparatedSpace S] [QuasiSeparatedSpace Z]
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huZ : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Z, ⊤)))
  [hμfinS : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμetS : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [hμfinZ : ∀ k : Index (fun _ => True), IsFinite (mu Z k.val).X.hom]
  [hμetZ : ∀ k : Index (fun _ => True), Etale (mu Z k.val).X.hom]
  (addZ : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := Z))
  (dualOf : ∀ (c : Z ⟶ S) (X : PositivePolarizedAction D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality (S := S)),
    PositivePullbackDualData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality c X)
  {Ω : Type} [Field Ω] (P : Spec (.of Ω) ⟶ Z)
  (hP : ∀ Y : Cover Z, Finite (Fiber P Y))

omit [IsCMField F] [IsScalarTower ℚ F A] in
include dualityNaturality polarizationStability in
/-- Pullbacks along two equal base maps of representatives related by the point
transport of the equality are related by the transport isomorphism, with
multiplier one. -/
theorem levelDataBaseChange_eq_witness {U : HarrisLevel D} {c c' : Z ⟶ S} (hc : c = c')
    (hPc : ∀ Y : Cover S, Finite (Fiber (P ≫ c) Y))
    (hPc' : ∀ Y : Cover S, Finite (Fiber (P ≫ c') Y))
    (u : HarrisLevelData D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h (P ≫ c) hPc htor huS U)
    (o' : letI := auxiliaryStarRing D C
      (PolarizedWeilLevel.levelTower preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h A
        (D.harrisHodgePELForm C) (P ≫ c') hPc' htor huS u.1).obj ((hodgeLevelFunctor D C).obj U))
    (hu : levelDataPointEq D C preservation composition unitCoherence associativity comparison
      symmetry stability square universality compatibility h htor huS
      (congrArg (fun d => P ≫ d) hc) hPc hPc' U u = ⟨u.1, o'⟩) :
    letI := auxiliaryStarRing D C
    ∃ he : PolarizedWeilLevel.Multiple preservation composition unitCoherence associativity
        comparison symmetry stability square universality addZ
        (levelDataBaseChange D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability c compatibility h P hP hPc htor huS huZ (dualOf c) U u).1
        (levelDataBaseChange D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability c' compatibility h P hP hPc' htor huS huZ (dualOf c') U
          ⟨u.1, o'⟩).1 1
        (eqToIso (congrArg (fun d => (RationalAlgebraAction.pullback d).obj u.1.actionObj) hc)),
      PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
          comparison symmetry stability square universality compatibility h A
          (D.harrisHodgePELForm C) P hP htor huZ addZ
          (levelDataBaseChange D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality dualityNaturality
            polarizationStability c compatibility h P hP hPc htor huS huZ (dualOf c) U u).1
          (levelDataBaseChange D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality dualityNaturality
            polarizationStability c' compatibility h P hP hPc' htor huS huZ (dualOf c') U
            ⟨u.1, o'⟩).1
          ((hodgeLevelFunctor D C).obj U) 1
          (eqToIso (congrArg (fun d => (RationalAlgebraAction.pullback d).obj u.1.actionObj) hc))
          he
          (levelDataBaseChange D C preservation composition unitCoherence associativity
            comparison symmetry stability square universality dualityNaturality
            polarizationStability c compatibility h P hP hPc htor huS huZ (dualOf c) U u).2 =
        (levelDataBaseChange D C preservation composition unitCoherence associativity
          comparison symmetry stability square universality dualityNaturality
          polarizationStability c' compatibility h P hP hPc' htor huS huZ (dualOf c') U
          ⟨u.1, o'⟩).2 := by
  let := auxiliaryStarRing D C
  subst hc
  obtain ⟨X, x⟩ := u
  have ho : x = o' := by
    injection hu
  subst ho
  refine ⟨PolarizedWeilLevel.multiple_refl preservation composition unitCoherence
    associativity comparison symmetry stability square universality addZ _, ?_⟩
  exact congrFun (congrArg DFunLike.coe (PolarizedWeilLevel.levelIso_refl preservation
    composition unitCoherence associativity comparison symmetry stability square universality
    compatibility h A (D.harrisHodgePELForm C) P hP htor huZ addZ _ _)) _

end EqTransport

section Square

variable {S Wk Wl Z : Scheme.{0}} [QuasiSeparatedSpace S] [QuasiSeparatedSpace Wk]
  [QuasiSeparatedSpace Wl] [ConnectedSpace Z] [IsLocallyNoetherian Z]
  (p : S ⟶ Spec (.of F)) (lieS : LieBaseChangeNaturalityStatement S)
  (lieZ : LieBaseChangeNaturalityStatement Z)
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huk : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Wk, ⊤)))
  (hul : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Wl, ⊤)))
  (huZ : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(Z, ⊤)))
  [∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [∀ k : Index (fun _ => True), IsFinite (mu Wk k.val).X.hom]
  [∀ k : Index (fun _ => True), Etale (mu Wk k.val).X.hom]
  [∀ k : Index (fun _ => True), IsFinite (mu Wl k.val).X.hom]
  [∀ k : Index (fun _ => True), Etale (mu Wl k.val).X.hom]
  [∀ k : Index (fun _ => True), IsFinite (mu Z k.val).X.hom]
  [∀ k : Index (fun _ => True), Etale (mu Z k.val).X.hom]
  (addk : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := Wk))
  (addl : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := Wl))
  (addZ : PositivePairAdditivity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := Z))
  (gk : Wk ⟶ S) (gl : Wl ⟶ S) (a : Z ⟶ Wk) (b : Z ⟶ Wl) (hsq : a ≫ gk = b ≫ gl)
  (dualGk : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality gk X)
  (dualGl : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S),
    PositivePullbackDualData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality gl X)
  (dualA : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := Wk),
    PositivePullbackDualData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality a X)
  (dualB : ∀ X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := Wl),
    PositivePullbackDualData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality b X)
  (dualOf : ∀ (c : Z ⟶ S) (X : PositivePolarizedAction D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality (S := S)),
    PositivePullbackDualData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality c X)
  {Ω : Type} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ Z)
  (hP : ∀ Y : Cover Z, Finite (Fiber (𝟙 _ ≫ z) Y))
  (hPa : ∀ Y : Cover Wk, Finite (Fiber ((𝟙 _ ≫ z) ≫ a) Y))
  (hPb : ∀ Y : Cover Wl, Finite (Fiber ((𝟙 _ ≫ z) ≫ b) Y))
  (hPak : ∀ Y : Cover S, Finite (Fiber (((𝟙 _ ≫ z) ≫ a) ≫ gk) Y))
  (hPbl : ∀ Y : Cover S, Finite (Fiber (((𝟙 _ ≫ z) ≫ b) ≫ gl) Y))
  (hPck : ∀ Y : Cover S, Finite (Fiber ((𝟙 _ ≫ z) ≫ (a ≫ gk)) Y))
  (hPcl : ∀ Y : Cover S, Finite (Fiber ((𝟙 _ ≫ z) ≫ (b ≫ gl)) Y))

local notation "pullK" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability gk compatibility h ((𝟙 _ ≫ z) ≫ a) hPa hPak htor huS huk dualGk
local notation "pullL" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability gl compatibility h ((𝟙 _ ≫ z) ≫ b) hPb hPbl htor huS hul dualGl
local notation "pullCk" => levelDataBaseChange D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality dualityNaturality
  polarizationStability (a ≫ gk) compatibility h (𝟙 _ ≫ z) hP hPck htor huS huZ
  (dualOf (a ≫ gk))
local notation "moveK" => levelDataPointEq D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor huS
  (Category.assoc (𝟙 _ ≫ z) a gk) hPak hPck
local notation "moveL" => levelDataPointEq D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor huS
  (Category.assoc (𝟙 _ ≫ z) b gl) hPbl hPcl
local notation "moveKL" => levelDataPointEq D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h htor huS
  (congrArg (fun d => (𝟙 _ ≫ z) ≫ d) hsq) hPck hPcl

set_option maxHeartbeats 6400000 in
include dualityNaturality polarizationStability lieS lieZ huZ addZ dualA dualB dualOf hP hPck
  hPcl in
/-- Two witnesses of the normalized CM class relation on étale pieces, both
obtained from the same representatives on the base, are compatible on every
connected test mapping to both pieces: after pulling back to the test, they
commute with the canonical comparison of the two iterated pullbacks. The proof
compares the two composite witnesses on the test with small-level rigidity. -/
theorem pulledWitness_square_compatible
    (G0 : ConnectedGeometricPointHomFaithfulnessStatement.{0})
    {U : HarrisLevel D}
    (hRigid : CMGeometricCoarseRigidity D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h htor U)
    (xk yk : HarrisLevelData D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality compatibility h
      (((𝟙 _ ≫ z) ≫ a) ≫ gk) hPak htor huS U)
    (ol : letI := auxiliaryStarRing D C
      (PolarizedWeilLevel.levelTower preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h A
        (D.harrisHodgePELForm C) (((𝟙 _ ≫ z) ≫ b) ≫ gl) hPbl htor huS xk.1).obj
        ((hodgeLevelFunctor D C).obj U))
    (ol' : letI := auxiliaryStarRing D C
      (PolarizedWeilLevel.levelTower preservation composition unitCoherence associativity
        comparison symmetry stability square universality compatibility h A
        (D.harrisHodgePELForm C) (((𝟙 _ ≫ z) ≫ b) ≫ gl) hPbl htor huS yk.1).obj
        ((hodgeLevelFunctor D C).obj U))
    (hX : PositiveObjectCondition D C hΦ preservation composition unitCoherence
      associativity comparison symmetry stability square universality
      (D.harrisTaylorReflexStructure C p) xk.1)
    (hnX : HarrisNumericalWeilLevel.NumericalObjectCondition D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality L p xk.1)
    (hox : letI := auxiliaryStarRing D C
      moveKL U (moveK U xk) = moveL U ⟨xk.1, ol⟩)
    (hoy : letI := auxiliaryStarRing D C
      moveKL U (moveK U yk) = moveL U ⟨yk.1, ol'⟩)
    (ek : letI := auxiliaryStarRing D C
      (RationalAlgebraAction.pullback gk).obj xk.1.actionObj ≅
        (RationalAlgebraAction.pullback gk).obj yk.1.actionObj)
    (el : letI := auxiliaryStarRing D C
      (RationalAlgebraAction.pullback gl).obj xk.1.actionObj ≅
        (RationalAlgebraAction.pullback gl).obj yk.1.actionObj)
    (hwk : letI := auxiliaryStarRing D C
      ∃ qk : ℚˣ, ∃ he : PolarizedWeilLevel.Multiple preservation composition unitCoherence
          associativity comparison symmetry stability square universality addk
          (pullK U xk).1 (pullK U yk).1 qk ek,
        PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
          comparison symmetry stability square universality compatibility h A
          (D.harrisHodgePELForm C) ((𝟙 _ ≫ z) ≫ a) hPa htor huk addk
          (pullK U xk).1 (pullK U yk).1 ((hodgeLevelFunctor D C).obj U) qk ek he
          (pullK U xk).2 = (pullK U yk).2)
    (hwl : letI := auxiliaryStarRing D C
      ∃ ql : ℚˣ, ∃ he : PolarizedWeilLevel.Multiple preservation composition unitCoherence
          associativity comparison symmetry stability square universality addl
          (pullL U ⟨xk.1, ol⟩).1 (pullL U ⟨yk.1, ol'⟩).1 ql el,
        PolarizedWeilLevel.levelIso preservation composition unitCoherence associativity
          comparison symmetry stability square universality compatibility h A
          (D.harrisHodgePELForm C) ((𝟙 _ ≫ z) ≫ b) hPb htor hul addl
          (pullL U ⟨xk.1, ol⟩).1 (pullL U ⟨yk.1, ol'⟩).1 ((hodgeLevelFunctor D C).obj U)
          ql el he (pullL U ⟨xk.1, ol⟩).2 = (pullL U ⟨yk.1, ol'⟩).2) :
    letI := auxiliaryStarRing D C
    (RationalAlgebraAction.pullback a).mapIso ek ≪≫
        RationalAlgebraAction.pullbackSquareIso gk gl a b hsq yk.1.actionObj =
      RationalAlgebraAction.pullbackSquareIso gk gl a b hsq xk.1.actionObj ≪≫
        (RationalAlgebraAction.pullback b).mapIso el := by
  let := auxiliaryStarRing D C
  obtain ⟨qk, hek, hlk⟩ := hwk
  obtain ⟨ql, hel, hll⟩ := hwl
  -- Pull the two witnesses back to the connected test.
  obtain ⟨heka, hlka⟩ := levelDataBaseChange_witness D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability a compatibility h (𝟙 _ ≫ z) hP hPa htor huk huZ
    dualA addk addZ (pullK U xk) (pullK U yk) qk ek hek hlk
  obtain ⟨helb, hllb⟩ := levelDataBaseChange_witness D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability b compatibility h (𝟙 _ ≫ z) hP hPb htor hul huZ
    dualB addl addZ (pullL U ⟨xk.1, ol⟩) (pullL U ⟨yk.1, ol'⟩) ql el hel hll
  -- Direct-to-successive comparisons.
  have cxk := levelDataBaseChange_comp_witness D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability gk a compatibility h (𝟙 _ ≫ z) hP hPa hPak hPck htor huS huk huZ
    dualGk dualA (dualOf (a ≫ gk)) addZ U xk
  have cyk := levelDataBaseChange_comp_witness D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability gk a compatibility h (𝟙 _ ≫ z) hP hPa hPak hPck htor huS huk huZ
    dualGk dualA (dualOf (a ≫ gk)) addZ U yk
  have cxl := levelDataBaseChange_comp_witness D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability gl b compatibility h (𝟙 _ ≫ z) hP hPb hPbl hPcl htor huS hul huZ
    dualGl dualB (dualOf (b ≫ gl)) addZ U ⟨xk.1, ol⟩
  have cyl := levelDataBaseChange_comp_witness D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability gl b compatibility h (𝟙 _ ≫ z) hP hPb hPbl hPcl htor huS hul huZ
    dualGl dualB (dualOf (b ≫ gl)) addZ U ⟨yk.1, ol'⟩
  -- Transport along the equality of the two composites.
  have rx := levelDataBaseChange_eq_witness D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor huS huZ addZ dualOf (𝟙 _ ≫ z) hP hsq hPck hPcl
    (moveK U xk) (moveL U ⟨xk.1, ol⟩).2 hox
  have ry := levelDataBaseChange_eq_witness D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor huS huZ addZ dualOf (𝟙 _ ≫ z) hP hsq hPck hPcl
    (moveK U yk) (moveL U ⟨yk.1, ol'⟩).2 hoy
  -- The two composite witnesses on the test.
  have w1 := PolarizedWeilLevel.witness_trans preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h A
    (D.harrisHodgePELForm C) (𝟙 _ ≫ z) hP htor huZ addZ ⟨_, cxk⟩
    (PolarizedWeilLevel.witness_trans preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h A
      (D.harrisHodgePELForm C) (𝟙 _ ≫ z) hP htor huZ addZ ⟨heka, hlka⟩
      (PolarizedWeilLevel.witness_symm preservation composition unitCoherence
        associativity comparison symmetry stability square universality compatibility h A
        (D.harrisHodgePELForm C) (𝟙 _ ≫ z) hP htor huZ addZ ⟨_, cyk⟩))
  have w2 := PolarizedWeilLevel.witness_trans preservation composition unitCoherence
    associativity comparison symmetry stability square universality compatibility h A
    (D.harrisHodgePELForm C) (𝟙 _ ≫ z) hP htor huZ addZ rx
    (PolarizedWeilLevel.witness_trans preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h A
      (D.harrisHodgePELForm C) (𝟙 _ ≫ z) hP htor huZ addZ
      (PolarizedWeilLevel.witness_trans preservation composition unitCoherence
        associativity comparison symmetry stability square universality compatibility h A
        (D.harrisHodgePELForm C) (𝟙 _ ≫ z) hP htor huZ addZ ⟨_, cxl⟩
        (PolarizedWeilLevel.witness_trans preservation composition unitCoherence
          associativity comparison symmetry stability square universality compatibility h A
          (D.harrisHodgePELForm C) (𝟙 _ ≫ z) hP htor huZ addZ ⟨helb, hllb⟩
          (PolarizedWeilLevel.witness_symm preservation composition unitCoherence
            associativity comparison symmetry stability square universality compatibility h A
            (D.harrisHodgePELForm C) (𝟙 _ ≫ z) hP htor huZ addZ ⟨_, cyl⟩)))
      (PolarizedWeilLevel.witness_symm preservation composition unitCoherence
        associativity comparison symmetry stability square universality compatibility h A
        (D.harrisHodgePELForm C) (𝟙 _ ≫ z) hP htor huZ addZ ry))
  obtain ⟨hw1, hl1⟩ := w1
  obtain ⟨hw2, hl2⟩ := w2
  -- Rigidity on the connected test.
  have hGood := levelDataBaseChange_objectCondition D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability (a ≫ gk) compatibility h (𝟙 _ ≫ z) hP hPck htor
    huS huZ (dualOf (a ≫ gk)) p lieS (moveK U xk) hX
  have hNum := HarrisNumericalWeilLevel.levelDataBaseChange_numericalObjectCondition D C
    preservation composition unitCoherence associativity comparison symmetry stability
    square universality dualityNaturality polarizationStability (a ≫ gk) compatibility h
    (𝟙 _ ≫ z) hP hPck htor huS huZ (dualOf (a ≫ gk)) lieS L p (moveK U xk) hnX
  have key := witness_eq_of_geometricRigidity D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor G0 hRigid ((a ≫ gk) ≫ p) lieZ huZ addZ z hP
    (pullCk U (moveK U xk)) (pullCk U (moveK U yk)) hGood hNum _ _ _ _ hw1 hw2 hl1 hl2
  -- Rearrange the equality of the two composite witnesses.
  apply Iso.ext
  have k := congrArg Iso.hom key
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, eqToIso.hom, eqToIso.inv,
    levelDataBaseChangeCompIso] at k
  simp only [Iso.trans_hom, Functor.mapIso_hom, RationalAlgebraAction.pullbackSquareIso,
    Iso.symm_hom, eqToIso.hom]
  rw [← cancel_epi (RationalAlgebraAction.pullbackCompIso gk a xk.1.actionObj).hom]
  simp only [← Category.assoc] at k ⊢
  rw [k]
  simp

end Square

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
