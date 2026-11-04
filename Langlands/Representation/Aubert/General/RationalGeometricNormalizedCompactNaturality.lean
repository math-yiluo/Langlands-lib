import Langlands.Representation.Aubert.General.RationalGeometricNormalizedCompactFormula

/-! # Naturality of the actual normalized compact comparison -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

universe u uV uW uX

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

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
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hUI : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hUJ : IsClosed (unipotent i ν J : Set (RationalPoint k G.X)))
  (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))
  (hSource : GeometricSourceDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
  (hTarget : GeometricTargetDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))

local notation "Q" => parabolic i ν I
local notation "L" => levi i ν I
local notation "H" => Subgroup.subgroupOf
  (geometricTargetIntersection Q (parabolic i ν J) (n : RationalPoint k G.X)) Q
local notation "K" => Subgroup.subgroupOf
  (geometricTargetIntersection L (parabolic i ν J) (n : RationalPoint k G.X)) L
local notation "S" => Subgroup.subgroupOf
  (geometricSourceIntersection (unipotent i ν I) (levi i ν J)
    (n : RationalPoint k G.X)) (levi i ν J)
local notation "Ls" => Subgroup.subgroupOf
  (geometricSourceIntersection L (levi i ν J)
    (n : RationalPoint k G.X)) (levi i ν J)
local notation "f" => geometricCoefficientProjection
  Q (parabolic i ν J) (levi i ν J) (unipotent i ν J) dJ (n : RationalPoint k G.X)
local notation "p" => geometricCoefficientLeviMap
  L (parabolic i ν J) (levi i ν J) (unipotent i ν J)
  (n : RationalPoint k G.X) hTarget
local notation "s" => Subgroup.inclusion dI.levi_le
local notation "P" => geometricSplitIntermediate i ν I J dI n
local notation "N" => geometricCompactKernel i ν I J dI n
local notation "D" => geometricCompactKernelIntersection i ν I J dI n
local notation "χ" => HaarModulus.closedHalfCharacter
  (unipotent i ν J) hUJ (levi i ν J) dJ.levi_le_normalizer
local notation "κ" => HaarModulus.closedInverseHalfCharacter
  (unipotent i ν I) hUI L dI.levi_le_normalizer
local notation "η" => geometricNormalizedCompactCharacter i ν I J dI dJ n hUI hUJ hPJ hTarget
local notation "μN" => geometricCompactKernelHaar i ν I J dI n hUI

local instance naturalityKernelMeasurableSpace : MeasurableSpace N := borel _
local instance naturalityKernelBorelSpace : BorelSpace N := ⟨rfl⟩
local instance naturalityIntersectionMeasurableSpace : MeasurableSpace D := borel _
local instance naturalityIntersectionBorelSpace : BorelSpace D := ⟨rfl⟩
local instance naturalityQuotientMeasurableSpace :
    MeasurableSpace (Induction.LeftQuotient D) := borel _
local instance naturalityQuotientBorelSpace :
    BorelSpace (Induction.LeftQuotient D) := ⟨rfl⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {X : Type uX} [AddCommGroup X] [Module ℂ X]

/-- The original compact-function coefficient map, descended through the
actual target radical and then twisted by the original inverse half. -/
def geometricNormalizedCompactSourceMap
    {σ : Representation ℂ (levi i ν J) V} {τ : Representation ℂ (levi i ν J) W}
    (a : σ.IntertwiningMap τ) :
    (geometricNormalizedCompactSource i ν I J dI dJ n hUI hUJ σ).IntertwiningMap
      (geometricNormalizedCompactSource i ν I J dI dJ n hUI hUJ τ) :=
  twistIntertwining κ (restrictAlongMap s
    (normalCoinvariantsMap dI.projection.ker
      (compactInducedMap H (restrictAlongMap f (twistIntertwining χ a)))))

@[simp] theorem geometricNormalizedCompactSourceMap_mk
    {σ : Representation ℂ (levi i ν J) V} {τ : Representation ℂ (levi i ν J) W}
    (a : σ.IntertwiningMap τ) (F : CompactFunctions H ((twist χ σ).comp f)) :
    geometricNormalizedCompactSourceMap i ν I J dI dJ n hUI hUJ a
        (Representation.Coinvariants.mk
          ((compactInduced H ((twist χ σ).comp f)).comp dI.projection.ker.subtype) F) =
      Representation.Coinvariants.mk
        ((compactInduced H ((twist χ τ).comp f)).comp dI.projection.ker.subtype)
        (compactInducedMap H (restrictAlongMap f (twistIntertwining χ a)) F) := rfl

/-- The ordinary source Jacquet map with its unchanged actual full-intersection
coefficient character. -/
def geometricNormalizedCompactCoefficientMap
    {σ : Representation ℂ (levi i ν J) V} {τ : Representation ℂ (levi i ν J) W}
    (a : σ.IntertwiningMap τ) :
    (geometricNormalizedCompactCoefficient i ν I J dI dJ n hUI hUJ hPJ
      hSource hTarget σ).IntertwiningMap
      (geometricNormalizedCompactCoefficient i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget τ) :=
  twistIntertwining η (restrictAlongMap p (Jacquet.map S Ls hSource.levi_le_normalizer a))

@[simp] theorem geometricNormalizedCompactCoefficientMap_mk
    {σ : Representation ℂ (levi i ν J) V} {τ : Representation ℂ (levi i ν J) W}
    (a : σ.IntertwiningMap τ) (v : V) :
    geometricNormalizedCompactCoefficientMap i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget a (Jacquet.mk σ S v) = Jacquet.mk τ S (a v) := rfl

/-- The actual compact-induced target map, with every coefficient correction
retained in its source and target actions. -/
def geometricNormalizedCompactTargetMap
    {σ : Representation ℂ (levi i ν J) V} {τ : Representation ℂ (levi i ν J) W}
    (a : σ.IntertwiningMap τ) :
    (geometricNormalizedCompactTarget i ν I J dI dJ n hUI hUJ hPJ
      hSource hTarget σ).IntertwiningMap
      (geometricNormalizedCompactTarget i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget τ) :=
  compactInducedMap K (geometricNormalizedCompactCoefficientMap
    i ν I J dI dJ n hUI hUJ hPJ hSource hTarget a)

@[simp] theorem geometricNormalizedCompactTargetMap_eval
    {σ : Representation ℂ (levi i ν J) V} {τ : Representation ℂ (levi i ν J) W}
    (a : σ.IntertwiningMap τ)
    (F : CompactFunctions K (geometricNormalizedCompactCoefficient i ν I J dI dJ n
      hUI hUJ hPJ hSource hTarget σ)) (l : L) :
    eval K (geometricNormalizedCompactCoefficient i ν I J dI dJ n
        hUI hUJ hPJ hSource hTarget τ)
      (geometricNormalizedCompactTargetMap i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget a F).val l =
      Jacquet.map S Ls hSource.levi_le_normalizer a
        (eval K (geometricNormalizedCompactCoefficient i ν I J dI dJ n
          hUI hUJ hPJ hSource hTarget σ) F.val l) := rfl

variable
  (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hMI : IsClosed (levi i ν I : Set (RationalPoint k G.X)))
  (hMJ : IsClosed (levi i ν J : Set (RationalPoint k G.X)))
  (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  (hprojI : Continuous dI.projection) (hprojJ : Continuous dJ.projection)

/-- Original coefficient intertwiners commute pointwise with the actual
ordinary-class quotient simple function. -/
theorem geometricNormalizedCompactIntegrand_natural
    {σ : Representation ℂ (levi i ν J) V} {τ : Representation ℂ (levi i ν J) W}
    (hσ : IsSmooth σ) (hτ : IsSmooth τ) (a : σ.IntertwiningMap τ)
    (F : CompactFunctions H ((twist χ σ).comp f)) (l : L) :
    geometricNormalizedCompactIntegrand i ν I J dI dJ n hUJ hPI hPJ hMI hMJ hUc
        hStandard hG hi hν hN hprojI hprojJ hSource hTarget τ hτ
        (compactInducedMap H (restrictAlongMap f (twistIntertwining χ a)) F) l =
      (geometricNormalizedCompactIntegrand i ν I J dI dJ n hUJ hPI hPJ hMI hMJ hUc
        hStandard hG hi hν hN hprojI hprojJ hSource hTarget σ hσ F l).map
        (Jacquet.map S Ls hSource.levi_le_normalizer a).toLinearMap := by
  ext q
  induction q using Quotient.inductionOn with
  | h q =>
    change geometricNormalizedCompactIntegrand i ν I J dI dJ n hUJ hPI hPJ hMI hMJ hUc
      hStandard hG hi hν hN hprojI hprojJ hSource hTarget τ hτ
      (compactInducedMap H (restrictAlongMap f (twistIntertwining χ a)) F) l
      (quotientMap D q) = _
    rw [geometricNormalizedCompactIntegrand_mk]
    change _ = Jacquet.map S Ls hSource.levi_le_normalizer a
      (geometricNormalizedCompactIntegrand i ν I J dI dJ n hUJ hPI hPJ hMI hMJ hUc
        hStandard hG hi hν hN hprojI hprojJ hSource hTarget σ hσ F l (quotientMap D q))
    rw [geometricNormalizedCompactIntegrand_mk, Jacquet.map_mk]
    rfl

variable [T2Space (RationalPoint k G.X)]

local notation "μD" => geometricCompactIntersectionHaar i ν I J dI n hUI hPI hPJ
local notation "μQ" => geometricCompactQuotientMeasure i ν I J dI n hUI hPI hPJ hUc

local instance naturalityKernelHaar_isHaarMeasure : IsHaarMeasure μN := by
  let : LocallyCompactSpace N :=
    geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
  unfold geometricCompactKernelHaar
  infer_instance

local instance naturalityKernelHaar_regular : (μN).Regular := by
  let : LocallyCompactSpace N :=
    geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
  unfold geometricCompactKernelHaar
  infer_instance

local instance naturalityIntersectionHaar_isHaarMeasure : IsHaarMeasure μD := by
  let : LocallyCompactSpace D :=
    geometricCompactKernelIntersection_locallyCompactSpace i ν I J dI n hUI hPI hPJ
  unfold geometricCompactIntersectionHaar
  infer_instance

local instance naturalityIntersectionHaar_regular : (μD).Regular := by
  let : LocallyCompactSpace D :=
    geometricCompactKernelIntersection_locallyCompactSpace i ν I J dI n hUI hPI hPJ
  unfold geometricCompactIntersectionHaar
  infer_instance

local instance naturalityQuotientMeasure_finiteOnCompacts :
    IsFiniteMeasureOnCompacts μQ := by
  let := geometricCompactIntersectionHaar_rightInvariant i ν I J dI n hUI hPI hPJ hUc
  let := (geometricCompactQuotientMeasure_isCompatible i ν I J dI n hUI hPI hPJ hUc).regular
  infer_instance

/-- Original coefficient maps commute with evaluation of the actual normalized
comparison on every compact function and every target Levi point. -/
theorem geometricNormalizedCompactEquiv_eval_natural
    {σ : Representation ℂ (levi i ν J) V} {τ : Representation ℂ (levi i ν J) W}
    (hσ : IsSmooth σ) (hτ : IsSmooth τ) (a : σ.IntertwiningMap τ)
    (F : CompactFunctions H ((twist χ σ).comp f)) (l : L) :
    eval K (geometricNormalizedCompactCoefficient i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget τ)
      (geometricNormalizedCompactEquiv i ν I J dI dJ n hUI hUJ hPJ hSource hTarget
        hPI hMJ hUc hStandard hG hi hν hN hMI hprojI hprojJ τ hτ
        (Representation.Coinvariants.mk
          ((compactInduced H ((twist χ τ).comp f)).comp dI.projection.ker.subtype)
          (compactInducedMap H (restrictAlongMap f (twistIntertwining χ a)) F))).val l =
      Jacquet.map S Ls hSource.levi_le_normalizer a
        (eval K (geometricNormalizedCompactCoefficient i ν I J dI dJ n hUI hUJ hPJ
          hSource hTarget σ)
          (geometricNormalizedCompactEquiv i ν I J dI dJ n hUI hUJ hPJ hSource hTarget
            hPI hMJ hUc hStandard hG hi hν hN hMI hprojI hprojJ σ hσ
            (Representation.Coinvariants.mk
              ((compactInduced H ((twist χ σ).comp f)).comp dI.projection.ker.subtype)
              F)).val l) := by
  let gσ := geometricNormalizedCompactIntegrand i ν I J dI dJ n hUJ hPI hPJ hMI hMJ hUc
    hStandard hG hi hν hN hprojI hprojJ hSource hTarget σ hσ F l
  let gτ := geometricNormalizedCompactIntegrand i ν I J dI dJ n hUJ hPI hPJ hMI hMJ hUc
    hStandard hG hi hν hN hprojI hprojJ hSource hTarget τ hτ
    (compactInducedMap H (restrictAlongMap f (twistIntertwining χ a)) F) l
  let b := (Jacquet.map S Ls hSource.levi_le_normalizer a).toLinearMap
  have hg : gτ = gσ.map b := geometricNormalizedCompactIntegrand_natural
    i ν I J dI dJ n hUJ hPJ hSource hTarget hPI hMI hMJ hUc hStandard hG hi hν hN
    hprojI hprojJ hσ hτ a F l
  have hfin : gσ.FinMeasSupp μQ := geometricNormalizedCompactIntegrand_finMeasSupp
    i ν I J dI dJ n hUJ hPI hPJ hMI hMJ hUc hStandard hG hi hν hN hprojI hprojJ
    hSource hTarget σ hσ F l μQ
  calc
    _ = (κ l : ℂ) • AlgebraicIntegral.integral μQ gτ :=
      geometricNormalizedCompactEquiv_eval_mk i ν I J dI dJ n hUI hUJ hPI hPJ hMI hMJ
        hUc hStandard hG hi hν hN hprojI hprojJ hSource hTarget τ hτ
        (compactInducedMap H (restrictAlongMap f (twistIntertwining χ a)) F) l
    _ = (κ l : ℂ) • b (AlgebraicIntegral.integral μQ gσ) :=
      congrArg (fun y => (κ l : ℂ) • y)
        ((congrArg (AlgebraicIntegral.integral μQ) hg).trans
          (AlgebraicIntegral.integral_linearMap gσ hfin b))
    _ = b ((κ l : ℂ) • AlgebraicIntegral.integral μQ gσ) := (b.map_smul _ _).symm
    _ = _ := congrArg b
      (geometricNormalizedCompactEquiv_eval_mk i ν I J dI dJ n hUI hUJ hPI hPJ hMI hMJ
        hUc hStandard hG hi hν hN hprojI hprojJ hSource hTarget σ hσ F l).symm

/-- The actual normalized compact comparison commutes with all original
coefficient intertwiners, including between different carrier universes. -/
theorem geometricNormalizedCompactEquiv_natural
    {σ : Representation ℂ (levi i ν J) V} {τ : Representation ℂ (levi i ν J) W}
    (hσ : IsSmooth σ) (hτ : IsSmooth τ) (a : σ.IntertwiningMap τ)
    (z : Representation.Coinvariants
      ((compactInduced H ((twist χ σ).comp f)).comp dI.projection.ker.subtype)) :
    geometricNormalizedCompactEquiv i ν I J dI dJ n hUI hUJ hPJ hSource hTarget
        hPI hMJ hUc hStandard hG hi hν hN hMI hprojI hprojJ τ hτ
        (geometricNormalizedCompactSourceMap i ν I J dI dJ n hUI hUJ a z) =
      geometricNormalizedCompactTargetMap i ν I J dI dJ n hUI hUJ hPJ hSource hTarget a
        (geometricNormalizedCompactEquiv i ν I J dI dJ n hUI hUJ hPJ hSource hTarget
          hPI hMJ hUc hStandard hG hi hν hN hMI hprojI hprojJ σ hσ z) := by
  refine Representation.Coinvariants.induction_on z ?_
  intro F
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext l
  exact geometricNormalizedCompactEquiv_eval_natural
    i ν I J dI dJ n hUI hUJ hPJ hSource hTarget hPI hMI hMJ hUc
    hStandard hG hi hν hN hprojI hprojJ hσ hτ a F l

end Langlands.Aubert.General.RationalPointFamily
