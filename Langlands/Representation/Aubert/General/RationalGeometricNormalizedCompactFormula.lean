import Langlands.Representation.Aubert.General.RationalGeometricNormalizedCompact

/-! # Original-function formulas for the actual normalized compact comparison -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

universe u uV uW

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

open Induction

private theorem normalizedCompactTwistEvaluation
    {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup A) (c : SmoothCharacter ℂ A) (σ : Representation ℂ H V)
    {ρ : Representation ℂ A W} (e : ρ.Equiv (compactInduced H σ)) (z : W) (l : A) :
    eval H (twist (c.toMonoidHom.comp H.subtype) σ)
        (compactInductionTwistEquiv H c σ (twistEquiv c.toMonoidHom e z)).val l =
      (c.toMonoidHom l : ℂ) • eval H σ (e z).val l := rfl

end Langlands.Aubert.General

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Induction MeasureTheory MeasureTheory.Measure
open QuotientIntegration HarmonicAnalysis
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (I J : Finset (SimpleRoot i ν))
  (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (dJ : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  [TopologicalSpace (RationalPoint k G.X)]
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  (hUI : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hUJ : IsClosed (unipotent i ν J : Set (RationalPoint k G.X)))
  (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))
  (hMI : IsClosed (levi i ν I : Set (RationalPoint k G.X)))
  (hMJ : IsClosed (levi i ν J : Set (RationalPoint k G.X)))
  (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  (hprojI : Continuous dI.projection) (hprojJ : Continuous dJ.projection)
  (hSource : GeometricSourceDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
  (hTarget : GeometricTargetDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

local notation "Q" => parabolic i ν I
local notation "L" => levi i ν I
local notation "H" => Subgroup.subgroupOf
  (geometricTargetIntersection Q (parabolic i ν J) (n : RationalPoint k G.X)) Q
local notation "K" => Subgroup.subgroupOf
  (geometricTargetIntersection L (parabolic i ν J) (n : RationalPoint k G.X)) L
local notation "S" => Subgroup.subgroupOf
  (geometricSourceIntersection (unipotent i ν I) (levi i ν J)
    (n : RationalPoint k G.X)) (levi i ν J)
local notation "f" => geometricCoefficientProjection
  Q (parabolic i ν J) (levi i ν J) (unipotent i ν J) dJ (n : RationalPoint k G.X)
local notation "s" => Subgroup.inclusion dI.levi_le
local notation "P" => geometricSplitIntermediate i ν I J dI n
local notation "N" => geometricCompactKernel i ν I J dI n
local notation "D" => geometricCompactKernelIntersection i ν I J dI n
local notation "χ" => HaarModulus.closedHalfCharacter
  (unipotent i ν J) hUJ (levi i ν J) dJ.levi_le_normalizer
local notation "κ" => HaarModulus.closedInverseHalfCharacter
  (unipotent i ν I) hUI (levi i ν I) dI.levi_le_normalizer
local notation "μN" => geometricCompactKernelHaar i ν I J dI n hUI
local notation "μD" => geometricCompactIntersectionHaar i ν I J dI n hUI hPI hPJ
local notation "μQ" => geometricCompactQuotientMeasure i ν I J dI n hUI hPI hPJ hUc

local instance formulaKernelMeasurableSpace : MeasurableSpace N := borel N
local instance formulaKernelBorelSpace : BorelSpace N := ⟨rfl⟩
local instance formulaIntersectionMeasurableSpace : MeasurableSpace D := borel D
local instance formulaIntersectionBorelSpace : BorelSpace D := ⟨rfl⟩
local instance formulaQuotientMeasurableSpace : MeasurableSpace (Induction.LeftQuotient D) :=
  borel (Induction.LeftQuotient D)
local instance formulaQuotientBorelSpace : BorelSpace (Induction.LeftQuotient D) := ⟨rfl⟩

local instance formulaKernelHaar_isHaarMeasure : IsHaarMeasure μN := by
  let : LocallyCompactSpace N :=
    geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
  unfold geometricCompactKernelHaar
  infer_instance

local instance formulaKernelHaar_regular : (μN).Regular := by
  let : LocallyCompactSpace N :=
    geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
  unfold geometricCompactKernelHaar
  infer_instance

local instance formulaIntersectionHaar_isHaarMeasure : IsHaarMeasure μD := by
  let : LocallyCompactSpace D :=
    geometricCompactKernelIntersection_locallyCompactSpace i ν I J dI n hUI hPI hPJ
  unfold geometricCompactIntersectionHaar
  infer_instance

local instance formulaIntersectionHaar_regular : (μD).Regular := by
  let : LocallyCompactSpace D :=
    geometricCompactKernelIntersection_locallyCompactSpace i ν I J dI n hUI hPI hPJ
  unfold geometricCompactIntersectionHaar
  infer_instance

local instance formulaQuotientMeasure_finiteOnCompacts : IsFiniteMeasureOnCompacts μQ := by
  let := geometricCompactIntersectionHaar_rightInvariant i ν I J dI n hUI hPI hPJ hUc
  let := (geometricCompactQuotientMeasure_isCompatible i ν I J dI n hUI hPI hPJ hUc).regular
  infer_instance

/-- The canonical-measure comparison evaluates by its actual quotient integral. -/
theorem geometricCompactEquivOfCompactLimit_eval_mk_integral
    (σ : Representation ℂ (levi i ν J) V) (hσ : IsSmooth σ)
    (F : CompactFunctions H (σ.comp f)) (l : L) :
    let : LocallyCompactSpace N :=
      geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
    eval K (geometricCompactCoefficient i ν I J dI n hPI hPJ hSource hTarget σ)
      (geometricCompactEquivOfCompactLimit i ν I J dI n hUI hPI hPJ hUc
        hStandard hG hi hν hN dJ hMI hprojI hprojJ σ hσ hSource hTarget
        (Representation.Coinvariants.mk
          ((compactInduced H (σ.comp f)).comp dI.projection.ker.subtype) F)).val l =
      AlgebraicIntegral.integral μQ
        (geometricCompactIntegrand i ν hStandard hG hi hν hN I J dI dJ n
          hPI hPJ hMI hprojI hprojJ hSource hTarget σ hσ F l) := by
  let : LocallyCompactSpace N :=
    geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
  let : LocallyCompactSpace Q := hPI.locallyCompactSpace
  let := geometricCompactKernelHaar_rightInvariant i ν I J dI n hUI hUc
  let := geometricCompactIntersectionHaar_rightInvariant i ν I J dI n hUI hPI hPJ hUc
  exact geometricCompactEquiv_eval_mk_integral i ν hStandard hG hi hν hN I J dI dJ n
    hPI hPJ hMI hprojI hprojJ hSource hTarget σ hσ μQ
    (geometricCompactKernel_compactOpenBasis i ν I J dI n hUI) μN μD
    inferInstance inferInstance
    (geometricCompactQuotientMeasure_isCompatible i ν I J dI n hUI hPI hPJ hUc)
    (fun O hO h1 => compactOpenSubgroupBasis Q O (hO.mem_nhds h1)) F l

section CoefficientCarrier

variable [LocallyCompactSpace (geometricCompactKernel i ν I J dI n)]

omit [T2Space (RationalPoint k G.X)] in
/-- The scalar corrections change actions; the underlying map is the original
inducing-half Jacquet quotient comparison. -/
theorem geometricNormalizedCompactCoefficientEquiv_apply
    (σ : Representation ℂ (levi i ν J) V) (z : Jacquet.Coinvariants (twist χ σ) S) :
    geometricNormalizedCompactCoefficientEquiv i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget hPI hMJ hUc σ z =
      geometricInducingHalfJacquetEquiv i ν I J dJ n hUJ hSource hTarget hMJ hUc σ z := by
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective (twist χ σ) S z
  rfl

end CoefficientCarrier

omit [T2Space (RationalPoint k G.X)] in
/-- The actual source-class integrand has finite measurable support for every
quotient measure finite on compact sets. -/
theorem geometricCompactIntegrand_finMeasSupp
    (σ : Representation ℂ (levi i ν J) V) (hσ : IsSmooth σ)
    (F : CompactFunctions H (σ.comp f)) (l : L)
    (quotientMeasure : Measure (Induction.LeftQuotient D))
    [IsFiniteMeasureOnCompacts quotientMeasure] :
    (geometricCompactIntegrand i ν hStandard hG hi hν hN I J dI dJ n
      hPI hPJ hMI hprojI hprojJ hSource hTarget σ hσ F l).FinMeasSupp quotientMeasure := by
  let : LocallyCompactSpace Q := hPI.locallyCompactSpace
  unfold geometricCompactIntegrand
  exact (quotientCoinvariantSimple_finMeasSupp _ _ quotientMeasure _).map
    (map_zero (geometricSplitCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
      hSource hTarget σ).toLinearEquiv.toLinearMap)

/-- The actual quotient simple function with values in the original ordinary
source Jacquet carrier, after removing the inducing half on the source radical. -/
def geometricNormalizedCompactIntegrand
    (σ : Representation ℂ (levi i ν J) V) (hσ : IsSmooth σ)
    (F : CompactFunctions H ((twist χ σ).comp f)) (l : L) :
    SimpleFunc (Induction.LeftQuotient D) (Jacquet.Coinvariants σ S) :=
  (geometricCompactIntegrand i ν hStandard hG hi hν hN I J dI dJ n
    hPI hPJ hMI hprojI hprojJ hSource hTarget (twist χ σ)
    ((HaarModulus.isSmooth_twist_closedHalfCharacter_iff
      (unipotent i ν J) hUJ (levi i ν J) dJ.levi_le_normalizer σ).mpr hσ) F l).map
      (geometricInducingHalfJacquetEquiv i ν I J dJ n hUJ hSource hTarget hMJ hUc σ
        ).toLinearEquiv.toLinearMap

omit [T2Space (RationalPoint k G.X)] in
/-- At each original kernel representative the integrand is exactly the
ordinary source Jacquet class of the original function value. -/
@[simp] theorem geometricNormalizedCompactIntegrand_mk
    (σ : Representation ℂ (levi i ν J) V) (hσ : IsSmooth σ)
    (F : CompactFunctions H ((twist χ σ).comp f)) (l : L) (q : N) :
    geometricNormalizedCompactIntegrand i ν I J dI dJ n hUJ hPI hPJ hMI hMJ hUc
        hStandard hG hi hν hN hprojI hprojJ hSource hTarget σ hσ F l (quotientMap D q) =
      Jacquet.mk σ S (eval H ((twist χ σ).comp f) F.val (((q : P) : Q) * s l)) := by
  change geometricInducingHalfJacquetEquiv i ν I J dJ n hUJ hSource hTarget hMJ hUc σ
    (geometricCompactIntegrand i ν hStandard hG hi hν hN I J dI dJ n
      hPI hPJ hMI hprojI hprojJ hSource hTarget (twist χ σ)
      ((HaarModulus.isSmooth_twist_closedHalfCharacter_iff
        (unipotent i ν J) hUJ (levi i ν J) dJ.levi_le_normalizer σ).mpr hσ)
      F l (quotientMap D q)) = _
  rw [geometricCompactIntegrand_mk, geometricInducingHalfJacquetEquiv_mk]

omit [T2Space (RationalPoint k G.X)] in
/-- The ordinary-class integrand has finite measurable support for each
quotient measure finite on compact sets. -/
theorem geometricNormalizedCompactIntegrand_finMeasSupp
    (σ : Representation ℂ (levi i ν J) V) (hσ : IsSmooth σ)
    (F : CompactFunctions H ((twist χ σ).comp f)) (l : L)
    (quotientMeasure : Measure (Induction.LeftQuotient D))
    [IsFiniteMeasureOnCompacts quotientMeasure] :
    (geometricNormalizedCompactIntegrand i ν I J dI dJ n hUJ hPI hPJ hMI hMJ hUc
      hStandard hG hi hν hN hprojI hprojJ hSource hTarget σ hσ F l
      ).FinMeasSupp quotientMeasure := by
  unfold geometricNormalizedCompactIntegrand
  exact (geometricCompactIntegrand_finMeasSupp i ν I J dI dJ n hPI hPJ hMI
    hStandard hG hi hν hN hprojI hprojJ hSource hTarget (twist χ σ)
    ((HaarModulus.isSmooth_twist_closedHalfCharacter_iff
      (unipotent i ν J) hUJ (levi i ν J) dJ.levi_le_normalizer σ).mpr hσ)
    F l quotientMeasure).map
      (map_zero (geometricInducingHalfJacquetEquiv i ν I J dJ n hUJ
        hSource hTarget hMJ hUc σ).toLinearEquiv.toLinearMap)

set_option maxHeartbeats 1800000 in
/-- On an original compact function, normalization retains the target inverse
half and the actual class-preserving source Jacquet map. -/
theorem geometricNormalizedCompactEquiv_eval_mk_integral
    (σ : Representation ℂ (levi i ν J) V) (hσ : IsSmooth σ)
    (F : CompactFunctions H ((twist χ σ).comp f)) (l : L) :
    eval K (geometricNormalizedCompactCoefficient i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget σ)
      (geometricNormalizedCompactEquiv i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget hPI hMJ hUc hStandard hG hi hν hN hMI hprojI hprojJ σ hσ
        (Representation.Coinvariants.mk
          ((compactInduced H ((twist χ σ).comp f)).comp dI.projection.ker.subtype) F)).val l =
      (κ l : ℂ) •
        geometricInducingHalfJacquetEquiv i ν I J dJ n hUJ hSource hTarget hMJ hUc σ
          (AlgebraicIntegral.integral μQ
            (geometricCompactIntegrand i ν hStandard hG hi hν hN I J dI dJ n
              hPI hPJ hMI hprojI hprojJ hSource hTarget (twist χ σ)
              ((HaarModulus.isSmooth_twist_closedHalfCharacter_iff
                (unipotent i ν J) hUJ (levi i ν J) dJ.levi_le_normalizer σ).mpr hσ)
              F l)) := by
  let : LocallyCompactSpace N :=
    geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
  let hχσ := (HaarModulus.isSmooth_twist_closedHalfCharacter_iff
    (unipotent i ν J) hUJ (levi i ν J) dJ.levi_le_normalizer σ).mpr hσ
  let e0 := geometricCompactEquivOfCompactLimit i ν I J dI n hUI hPI hPJ hUc
    hStandard hG hi hν hN dJ hMI hprojI hprojJ (twist χ σ) hχσ hSource hTarget
  let eC := geometricNormalizedCompactCoefficientEquiv i ν I J dI dJ n hUI hUJ hPJ
    hSource hTarget hPI hMJ hUc σ
  let z := Representation.Coinvariants.mk
    ((compactInduced H ((twist χ σ).comp f)).comp dI.projection.ker.subtype) F
  let c : SmoothCharacter ℂ L :=
    { toMonoidHom := κ
      isOpen_ker := HaarModulus.isOpen_ker_closedInverseHalfCharacter
        (unipotent i ν I) hUI L dI.levi_le_normalizer }
  calc
    _ = eC ((κ l : ℂ) •
        eval K (geometricCompactCoefficient i ν I J dI n hPI hPJ hSource hTarget
          (twist χ σ)) (e0 z).val l) :=
      congrArg eC (normalizedCompactTwistEvaluation K c
        (geometricCompactCoefficient i ν I J dI n hPI hPJ hSource hTarget (twist χ σ))
        e0 z l)
    _ = (κ l : ℂ) • eC
        (eval K (geometricCompactCoefficient i ν I J dI n hPI hPJ hSource hTarget
          (twist χ σ)) (e0 z).val l) := eC.map_smul _ _
    _ = (κ l : ℂ) •
        geometricInducingHalfJacquetEquiv i ν I J dJ n hUJ hSource hTarget hMJ hUc σ
          (eval K (geometricCompactCoefficient i ν I J dI n hPI hPJ hSource hTarget
            (twist χ σ)) (e0 z).val l) :=
      congrArg (fun y => (κ l : ℂ) • y)
        (geometricNormalizedCompactCoefficientEquiv_apply i ν I J dI dJ n hUI hUJ hPI
          hPJ hMJ hUc hSource hTarget σ _)
    _ = _ := congrArg (fun y => (κ l : ℂ) •
      geometricInducingHalfJacquetEquiv i ν I J dJ n hUJ hSource hTarget hMJ hUc σ y)
      (geometricCompactEquivOfCompactLimit_eval_mk_integral i ν I J dI dJ n hUI hPI hPJ
        hMI hUc hStandard hG hi hν hN hprojI hprojJ hSource hTarget
        (twist χ σ) hχσ F l)

/-- The normalized comparison is the original target inverse half times the
actual quotient integral of ordinary original-vector Jacquet classes. -/
theorem geometricNormalizedCompactEquiv_eval_mk
    (σ : Representation ℂ (levi i ν J) V) (hσ : IsSmooth σ)
    (F : CompactFunctions H ((twist χ σ).comp f)) (l : L) :
    eval K (geometricNormalizedCompactCoefficient i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget σ)
      (geometricNormalizedCompactEquiv i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget hPI hMJ hUc hStandard hG hi hν hN hMI hprojI hprojJ σ hσ
        (Representation.Coinvariants.mk
          ((compactInduced H ((twist χ σ).comp f)).comp dI.projection.ker.subtype) F)).val l =
      (κ l : ℂ) • AlgebraicIntegral.integral μQ
        (geometricNormalizedCompactIntegrand i ν I J dI dJ n hUJ hPI hPJ hMI hMJ hUc
          hStandard hG hi hν hN hprojI hprojJ hSource hTarget σ hσ F l) := by
  let hχσ := (HaarModulus.isSmooth_twist_closedHalfCharacter_iff
    (unipotent i ν J) hUJ (levi i ν J) dJ.levi_le_normalizer σ).mpr hσ
  have hMap := AlgebraicIntegral.integral_linearMap
    (geometricCompactIntegrand i ν hStandard hG hi hν hN I J dI dJ n
      hPI hPJ hMI hprojI hprojJ hSource hTarget (twist χ σ) hχσ F l)
    (geometricCompactIntegrand_finMeasSupp i ν I J dI dJ n hPI hPJ hMI
      hStandard hG hi hν hN hprojI hprojJ hSource hTarget (twist χ σ) hχσ F l μQ)
    (geometricInducingHalfJacquetEquiv i ν I J dJ n hUJ hSource hTarget hMJ hUc σ
      ).toLinearEquiv.toLinearMap
  exact (geometricNormalizedCompactEquiv_eval_mk_integral i ν I J dI dJ n hUI hUJ
    hPI hPJ hMI hMJ hUc hStandard hG hi hν hN hprojI hprojJ hSource hTarget σ hσ F l).trans
      (congrArg (fun z => (κ l : ℂ) • z) hMap.symm)

end Langlands.Aubert.General.RationalPointFamily
