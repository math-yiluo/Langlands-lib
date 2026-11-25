import Langlands.AbelianScheme.Tate.PrimeMonodromy
import Langlands.AbelianScheme.Tate.RationalPrimeHom
import Langlands.AbelianScheme.Tate.WeilPELFrame
import Langlands.Shimura.PEL.HarrisTaylorCMLocalPrimeComparison

/-! # Finite-order monodromy at a small Harris level -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private local instance (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AbelianScheme.Tate
open GroupScheme.Tate (Index)
open Langlands.TateTwist.Divisibility (primePowerIndex)

variable {S : Scheme.{0}}
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))

/-- The existing rational prime Tate representation at the prime of a rational finite
place, using the same torsion units as the full rational Tate representation. -/
abbrev primeTateMonodromyAt (B : AbelianScheme S) (v : Global.FinitePlace ℚ) :
    FundamentalGroup s hs →* (PrimeAdic.Rational B (Over.mk s)
      (Rat.HeightOneSpectrum.primesEquiv v).val ≃ₗ[ℚ_[(Rat.HeightOneSpectrum.primesEquiv v).val]]
        PrimeAdic.Rational B (Over.mk s) (Rat.HeightOneSpectrum.primesEquiv v).val) :=
  PrimeAdic.rationalMonodromyRepresentation s hs htor B
    (Rat.HeightOneSpectrum.primesEquiv v).val
    (fun k => hu (primePowerIndex (fun _ => True) _ (fun _ => trivial) k))

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
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
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]
  [QuasiSeparatedSpace S]
  (X : PositivePolarizedAction D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality (S := S))

local notation "OriginalGroup" => D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ
local notation "SourceGroup" => ScalarExtensionSimilitudePoints A A
  (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)
local notation "scalarEquiv" => D.harrisFiniteAdelicScalarExtensionContinuousEquiv
  (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C)
local notation "orbitTower" => PolarizedWeilLevel.levelTower preservation composition
  unitCoherence associativity comparison symmetry stability square universality
  compatibility h A (D.harrisHodgePELForm C) s hs htor hu X
local notation "Frame" => WeilAdelicFrame preservation composition unitCoherence
  associativity comparison symmetry stability X.hasDual X.geometry X.inversePoincare
  X.evaluation compatibility X.polarization h X.actionObj.action A (D.harrisHodgePELForm C) s
local notation "rightAction" => weilAdelicFrameRightAction preservation composition
  unitCoherence associativity comparison symmetry stability X.hasDual X.geometry
  X.inversePoincare X.evaluation compatibility X.polarization h X.actionObj.action
  A (D.harrisHodgePELForm C) s
local notation "leftAction" => weilAdelicFrameMonodromyAction preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  rationalWeilGeometricTransport X.hasDual X.geometry X.inversePoincare X.evaluation
  X.polarization h X.actionObj.action A (D.harrisHodgePELForm C) s hs htor hu
  (hμfin := hμfin) (hμet := hμet)
local notation "commAction" => weilAdelicFrameActionsComm preservation composition
  unitCoherence associativity comparison symmetry stability compatibility
  rationalWeilGeometricTransport X.hasDual X.geometry X.inversePoincare X.evaluation
  X.polarization h X.actionObj.action A (D.harrisHodgePELForm C) s hs htor hu
  (hμfin := hμfin) (hμet := hμet)
local notation "B" => X.actionObj.abelianScheme
local notation "fullMonodromy" => rationalMonodromyRepresentation s hs htor B (fun _ => True) hu
local notation "coordinate" => localFrameCoordinate D C preservation composition unitCoherence
  associativity comparison symmetry stability square universality compatibility h s X

/-- If an actual Weil-compatible orbit is fixed by monodromy at a Harris level
small at `v`, each finite-order full rational Tate operator acts trivially on
the rational prime Tate module at `v`. -/
theorem primeTateMonodromyAt_eq_one_of_smallLevel (U : HarrisLevel D)
    (v : Global.FinitePlace ℚ) (hsmall : D.rationalInvolution.LevelSmallAt U v) :
    letI := auxiliaryStarRing D C
    ∀ (_a : (orbitTower).obj ((hodgeLevelFunctor D C).obj U)) (gamma : FundamentalGroup s hs),
      IsOfFinOrder (fullMonodromy gamma) →
      primeTateMonodromyAt s hs htor hu B v gamma = 1 := by
  let := auxiliaryStarRing D C
  intro a gamma hfin
  let : MulAction SourceGroupᵐᵒᵖ Frame := rightAction
  let : MulAction (FundamentalGroup s hs) Frame := leftAction
  let : SMulCommClass (FundamentalGroup s hs) SourceGroupᵐᵒᵖ Frame := commAction
  let V := ((hodgeLevelFunctor D C).obj U).subgroup
  change InvariantOrbit (X := Frame) (FundamentalGroup s hs) V at a
  obtain ⟨eta, heta⟩ := Quotient.exists_rep a.val
  change RightOrbit.mk V eta = a.val at heta
  have hfixed : RightOrbit.mk V eta ∈ MulAction.fixedPoints
      (FundamentalGroup s hs) (RightOrbit Frame V) := by
    rw [heta]
    exact a.property
  obtain ⟨g, hg, hframe⟩ := (RightOrbit.mk_mem_fixedPoints V eta).mp hfixed gamma
  let u : OriginalGroup := (scalarEquiv).symm g
  have hu_mem : u ∈ U.subgroup :=
    (hodgeLevelFunctor_obj_mem D C U u).mp
      (by simpa only [u, ContinuousMulEquiv.apply_symm_apply] using hg)
  have htranslate : gamma • eta = right (G := SourceGroup) eta (scalarEquiv u) := by
    simpa only [u, ContinuousMulEquiv.apply_symm_apply] using hframe
  obtain ⟨m, hm, hmonodromy⟩ := hfin.exists_pow_eq_one
  have hiterate (k : ℕ) :
      gamma ^ k • eta = right (G := SourceGroup) eta (scalarEquiv (u ^ k)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ' gamma, mul_smul, ih, right_comm, htranslate, right_mul]
      apply congrArg (right (G := SourceGroup) eta)
      exact ((scalarEquiv).map_mul u (u ^ k)).symm.trans
        (congrArg (fun w : OriginalGroup => scalarEquiv w) (pow_succ' u k).symm)
  have hfix : gamma ^ m • eta = eta := by
    apply Subtype.ext
    ext x
    change fullMonodromy (gamma ^ m) (eta.1 x) = eta.1 x
    rw [map_pow, hmonodromy]
    rfl
  have hpower : u ^ m = 1 := by
    let : IsSimpleRing A := D.simple
    apply (scalarEquiv).injective
    rw [map_one]
    apply weilAdelicFrameRightAction_injective preservation composition unitCoherence
      associativity comparison symmetry stability X.hasDual X.geometry X.inversePoincare
      X.evaluation compatibility X.polarization h X.actionObj.action A
      (D.harrisHodgePELForm C) s
      (D.harrisHodgePELAlgebra C).toSecondKindInvolution.rationalInvolution
      (hodgeRationalPELConditions D C) eta
    change right (G := SourceGroup) eta (scalarEquiv (u ^ m)) = right eta (1 : SourceGroup)
    rw [right_one, ← hiterate, hfix]
  have hlocal : D.rationalInvolution.pointsMap (AlgebraInvolution.finiteEvaluation v)
      u.unop = 1 := by
    apply hsmall u hu_mem
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, ?_⟩
    rw [← map_pow, ← MulOpposite.unop_pow, hpower, MulOpposite.unop_one, map_one]
  have hcoeff := congrArg
    (fun z : D.rationalInvolution.Points (Global.FiniteCompletion ℚ v) =>
      (z.val.1 : (Global.FiniteCompletion ℚ v) ⊗[ℚ] A)) hlocal
  change AlgebraInvolution.changeCoefficients (AlgebraInvolution.finiteEvaluation v)
    (u.unop.val.1 : (Global.FiniteAdeles ℚ) ⊗[ℚ] A) = 1 at hcoeff
  have hconj (x : (Global.FiniteAdeles ℚ) ⊗[ℚ] A) :
      fullMonodromy gamma (eta.1 x) = eta.1 (x * (u.unop.val.1 : (Global.FiniteAdeles ℚ) ⊗[ℚ] A)) :=
    congrArg (fun xi : Frame => xi.1 x) htranslate
  have hcoordinate (y : RationalFull B (Over.mk s)) :
      coordinate v eta (fullMonodromy gamma y) = coordinate v eta y := by
    have h := hconj (eta.1.symm y)
    rw [LinearEquiv.apply_symm_apply] at h
    change AlgebraInvolution.changeCoefficients (AlgebraInvolution.finiteEvaluation v)
      (eta.1.symm (fullMonodromy gamma y)) =
        AlgebraInvolution.changeCoefficients (AlgebraInvolution.finiteEvaluation v) (eta.1.symm y)
    rw [h, LinearEquiv.symm_apply_apply, map_mul, hcoeff, mul_one]
  ext z
  obtain ⟨y, rfl⟩ := PrimeComparison.rationalFullToPrime_surjective (Over.mk s)
    (Rat.HeightOneSpectrum.primesEquiv v).val B z
  exact (PrimeComparison.rationalFullToPrime_monodromy s hs htor B
    (Rat.HeightOneSpectrum.primesEquiv v).val hu gamma y).symm.trans
      (rationalFullToPrime_eq_of_localFrameCoordinate_eq D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        compatibility h s X v eta _ y (hcoordinate y))

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
