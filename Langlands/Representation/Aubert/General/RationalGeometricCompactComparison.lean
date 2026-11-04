import Langlands.Representation.Induction.SplitStagesComparison
import Langlands.Representation.Aubert.General.RationalGeometricSplitCoefficient

/-! # Actual rational geometric compact comparison -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 80000

universe u uA uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

section SubgroupTransport

variable {A : Type uA} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Subgroup equality commutes with the scalar twist before compact induction. -/
private def compactInducedSubgroupTwistCongr {H K : Subgroup A} (h : H = K)
    (χ : H →* ℂˣ) (ρ : Representation ℂ H V) :
    (Induction.compactInduced H (twist χ ρ)).Equiv
      (Induction.compactInduced K
        (twist (χ.comp (MulEquiv.toMonoidHom (MulEquiv.subgroupCongr h).symm))
          (ρ.comp (MulEquiv.toMonoidHom (MulEquiv.subgroupCongr h).symm)))) := by
  subst K
  exact Representation.Equiv.refl _

private theorem compactInducedSubgroupTwistCongr_eval {H K : Subgroup A} (h : H = K)
    (χ : H →* ℂˣ) (ρ : Representation ℂ H V)
    (f : Induction.CompactFunctions H (twist χ ρ)) (a : A) :
    Induction.eval K
        (twist (χ.comp (MulEquiv.toMonoidHom (MulEquiv.subgroupCongr h).symm))
          (ρ.comp (MulEquiv.toMonoidHom (MulEquiv.subgroupCongr h).symm)))
        (compactInducedSubgroupTwistCongr h χ ρ f).val a =
      Induction.eval H (twist χ ρ) f.val a := by
  subst K
  rfl

end SubgroupTransport

namespace RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open MeasureTheory MeasureTheory.Measure
open Induction QuotientIntegration HarmonicAnalysis

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  (I J : Finset (SimpleRoot i ν))
  (dI : IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
  (dJ : IsSemidirectDecomposition (parabolic i ν J) (levi i ν J) (unipotent i ν J))
  (n : Group.RelativeWeyl.normalizer (torusPoints i))
  [TopologicalSpace (RationalPoint k G.X)] [IsTopologicalGroup (RationalPoint k G.X)]

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
  (geometricSourceIntersection L (levi i ν J) (n : RationalPoint k G.X)) (levi i ν J)
local notation "f" => geometricCoefficientProjection
  Q (parabolic i ν J) (levi i ν J) (unipotent i ν J) dJ (n : RationalPoint k G.X)
local notation "s" => Subgroup.inclusion dI.levi_le
local notation "P" => geometricSplitIntermediate i ν I J dI n
local notation "hker" => geometricSplit_ker_le i ν I J dI n
local notation "hHP" =>
  stabilizer_le_geometricSplitIntermediate i ν I J dI n hStandard hG hi hν hN
local notation "rP" => splitStagesRetraction dI.projection s
  (fun m => dI.projection_levi m) P hker
local notation "sP" => MonoidHom.subgroupComap s P
local notation "HP" => Subgroup.subgroupOf H P
local notation "φ" => MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHP)
local notation "hSH" => geometricSplit_section_mem i ν I J dI n
local notation "hSI" => (fun l : Subgroup.comap s P => hSH l)
local notation "eK" => geometricSplitQuotientEquiv i ν I J dI n
local notation "D" => Subgroup.comap (Subgroup.subtype (MonoidHom.ker rP)) HP
local notation "j" => MonoidHom.subgroupComap (Subgroup.subtype (MonoidHom.ker rP)) HP

variable
  (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hPJ : IsClosed (parabolic i ν J : Set (RationalPoint k G.X)))

local notation "hHc" => isClosed_geometricStabilizer i ν I J n hPI hPJ
local notation "hHPc" => IsClosed.preimage
  (continuous_subtype_val : Continuous (Subgroup.subtype P)) hHc

/-- The kernel of the actual restricted target Levi projection. -/
abbrev geometricCompactKernel : Subgroup P := MonoidHom.ker rP

/-- The actual orbit-stabilizer intersection inside the restricted kernel. -/
abbrev geometricCompactKernelIntersection : Subgroup (geometricCompactKernel i ν I J dI n) := D

variable [LocallyCompactSpace (geometricCompactKernel i ν I J dI n)]
  [MeasurableSpace (geometricCompactKernel i ν I J dI n)]
  [BorelSpace (geometricCompactKernel i ν I J dI n)]
  [MeasurableSpace (geometricCompactKernelIntersection i ν I J dI n)]
  [BorelSpace (geometricCompactKernelIntersection i ν I J dI n)]

/-- The actual inverse-conjugation subgroup-to-kernel Haar ratio, on the
literal target-intersection parabolic. -/
def geometricCompactHaarCharacter : K →* ℂˣ :=
  (Jacquet.complexCharacter (splitKernelHaarRatio rP sP HP hSI hHPc)).comp
    (MulEquiv.toMonoidHom (MulEquiv.symm eK))

variable
  [T2Space (RationalPoint k G.X)] [LocallyCompactSpace (RationalPoint k G.X)]
  (hMI : IsClosed (levi i ν I : Set (RationalPoint k G.X)))
  (hprojI : Continuous dI.projection) (hprojJ : Continuous dJ.projection)

local notation "hPc" => isClosed_geometricSplitIntermediate i ν I J dI n hMI hPJ hprojI
local notation "χ" => geometricCompactHaarCharacter i ν I J dI n hPI hPJ

variable
  (hSource : GeometricSourceDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))
  (hTarget : GeometricTargetDecomposition
    (parabolic i ν) (levi i ν) (unipotent i ν) I J (n : RationalPoint k G.X))

local notation "p" => geometricCoefficientLeviMap
  L (parabolic i ν J) (levi i ν J) (unipotent i ν J) (n : RationalPoint k G.X) hTarget

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (levi i ν J) V) (hσ : IsSmooth σ)

/-- The exact unnormalized coefficient, including the actual Haar ratio. -/
abbrev geometricCompactCoefficient : Representation ℂ K (Jacquet.Coinvariants σ S) :=
  twist χ ((Jacquet.action σ S Ls hSource.levi_le_normalizer).comp p)

set_option maxHeartbeats 800000 in
/-- The original kernel-coinvariant representation restricted to the original Levi. -/
abbrev geometricCompactSource : Representation ℂ L
    (Representation.Coinvariants ((compactInduced H (σ.comp f)).comp dI.projection.ker.subtype)) :=
  (Representation.toCoinvariants (compactInduced H (σ.comp f)) dI.projection.ker).comp s

set_option maxHeartbeats 800000 in
/-- Compact induction from the literal target intersection with the actual coefficient. -/
abbrev geometricCompactTarget : Representation ℂ L
    (CompactFunctions K (geometricCompactCoefficient i ν I J dI n hPI hPJ hSource hTarget σ)) :=
  compactInduced K (geometricCompactCoefficient i ν I J dI n hPI hPJ hSource hTarget σ)

include hprojJ hσ in
omit [T2Space (RationalPoint k G.X)] [LocallyCompactSpace (RationalPoint k G.X)] in
private theorem geometricCompactPullback_smooth : IsSmooth (σ.comp f) :=
  isSmooth_comp f
    (continuous_geometricCoefficientProjection Q (parabolic i ν J)
      (levi i ν J) (unipotent i ν J) dJ (n : RationalPoint k G.X) hprojJ) hσ

variable
  [MeasurableSpace (Induction.LeftQuotient (geometricCompactKernelIntersection i ν I J dI n))]
  [BorelSpace (Induction.LeftQuotient (geometricCompactKernelIntersection i ν I J dI n))]
  (quotientMeasure : Measure (Induction.LeftQuotient (geometricCompactKernelIntersection i ν I J dI n))) [IsFiniteMeasureOnCompacts quotientMeasure]
  (hKernelBasis : ∀ O : Set (geometricCompactKernel i ν I J dI n),
    IsOpen O → (1 : geometricCompactKernel i ν I J dI n) ∈ O →
      ∃ U : OpenSubgroup (geometricCompactKernel i ν I J dI n),
        IsCompact (U : Set (geometricCompactKernel i ν I J dI n)) ∧
          (U : Set (geometricCompactKernel i ν I J dI n)) ⊆ O)
  (μN : Measure (geometricCompactKernel i ν I J dI n)) (μD : Measure (geometricCompactKernelIntersection i ν I J dI n))
  [IsHaarMeasure μN] (hRegularN : μN.Regular) [IsMulRightInvariant μN]
  [IsHaarMeasure μD] (hRegularD : μD.Regular) [IsMulRightInvariant μD]
  (hCompatible : IsCompatible (geometricCompactKernelIntersection i ν I J dI n) μN μD quotientMeasure)
  (hBasis : ∀ O : Set (parabolic i ν I), IsOpen O → (1 : parabolic i ν I) ∈ O →
    ∃ U : OpenSubgroup (parabolic i ν I), IsCompact (U : Set (parabolic i ν I)) ∧ (U : Set (parabolic i ν I)) ⊆ O)

set_option maxHeartbeats 800000 in
/-- The actual compact orbit-stabilizer quotient is compact induction of the
Haar-corrected source-intersection Jacquet coefficient. -/
def geometricCompactEquiv :
    Representation.Equiv (geometricCompactSource i ν I J dI dJ n σ)
      (geometricCompactTarget i ν I J dI n hPI hPJ hSource hTarget σ) := by
  letI := hRegularN
  letI := hRegularD
  let : LocallyCompactSpace Q := hPI.locallyCompactSpace
  have hNclosed : IsClosed (dI.projection.ker : Set Q) :=
    isClosed_singleton.preimage hprojI
  let hσf := geometricCompactPullback_smooth i ν I J dJ n hprojJ σ hσ
  let eStages := splitStagesCompactEquiv dI.projection s
    (fun m => dI.projection_levi m) hprojI
    (continuous_geometricSplitSection i ν I dI) P H hker hHP hPc hHc hSH
    (σ.comp f) hσf quotientMeasure hKernelBasis μN μD hCompatible hNclosed hBasis
  let χ0 := Jacquet.complexCharacter (splitKernelHaarRatio rP sP HP hSI hHPc)
  let ρ0 := splitKernelCoefficientAction rP sP HP hSI ((σ.comp f).comp φ)
  let eSubgroup := compactInducedSubgroupTwistCongr
    (geometricSplit_comap_section i ν I J dI n) χ0 ρ0
  refine eStages.trans ?_
  refine eSubgroup.trans ?_
  exact compactInducedEquiv K (twistEquiv χ
      (geometricSplitCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
        hSource hTarget σ))

set_option maxHeartbeats 800000 in
/-- The actual source Jacquet class of the original compact function, on the
relative kernel quotient. -/
def geometricCompactIntegrand (F : CompactFunctions H (σ.comp f)) (l : L) :
    SimpleFunc (Induction.LeftQuotient D) (Jacquet.Coinvariants σ S) := by
  let : LocallyCompactSpace Q := hPI.locallyCompactSpace
  exact (quotientCoinvariantSimple D (((σ.comp f).comp φ).comp j)
    (splitStagesKernelSlice dI.projection s (fun m => dI.projection_levi m)
      hprojI (continuous_geometricSplitSection i ν I dI) P H hker hHP hPc hHc hSH
      (σ.comp f) (geometricCompactPullback_smooth i ν I J dJ n hprojJ σ hσ) F l)).map
    (geometricSplitCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
      hSource hTarget σ).toLinearEquiv.toLinearMap

set_option maxHeartbeats 800000 in
omit [T2Space (RationalPoint k G.X)]
  [LocallyCompactSpace (geometricCompactKernel i ν I J dI n)]
  [MeasurableSpace (geometricCompactKernel i ν I J dI n)]
  [BorelSpace (geometricCompactKernel i ν I J dI n)]
  [MeasurableSpace (geometricCompactKernelIntersection i ν I J dI n)]
  [BorelSpace (geometricCompactKernelIntersection i ν I J dI n)] in
/-- The integrand retains the identical original vector before taking its
source-radical Jacquet class. -/
@[simp] theorem geometricCompactIntegrand_mk
    (F : CompactFunctions H (σ.comp f)) (l : L) (q : geometricCompactKernel i ν I J dI n) :
    geometricCompactIntegrand i ν hStandard hG hi hν hN I J dI dJ n
        hPI hPJ hMI hprojI hprojJ hSource hTarget σ hσ F l (quotientMap D q) =
      Jacquet.mk σ S (eval H (σ.comp f) F.val (((q : P) : Q) * s l)) := by
  let : LocallyCompactSpace Q := hPI.locallyCompactSpace
  change (geometricSplitCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
    hSource hTarget σ) (Representation.Coinvariants.mk (((σ.comp f).comp φ).comp j)
      (eval H (σ.comp f) F.val (((q : P) : Q) * s l))) = _
  exact geometricSplitCoefficientEquiv_mk i ν hStandard hG hi hν hN I J dI dJ n
    hSource hTarget σ _

set_option maxHeartbeats 800000 in
/-- On every original compact function the comparison is precisely the
compatible quotient integral, without an additional scalar. -/
theorem geometricCompactEquiv_eval_mk_integral
    (F : CompactFunctions H (σ.comp f)) (l : L) :
    eval K (geometricCompactCoefficient i ν I J dI n hPI hPJ hSource hTarget σ)
      (geometricCompactEquiv i ν hStandard hG hi hν hN I J dI dJ n
        hPI hPJ hMI hprojI hprojJ hSource hTarget σ hσ quotientMeasure hKernelBasis
        μN μD hRegularN hRegularD hCompatible hBasis
        (Representation.Coinvariants.mk ((compactInduced H (σ.comp f)).comp
          dI.projection.ker.subtype) F)).val l =
      AlgebraicIntegral.integral quotientMeasure
        (geometricCompactIntegrand i ν hStandard hG hi hν hN I J dI dJ n
          hPI hPJ hMI hprojI hprojJ hSource hTarget σ hσ F l) := by
  let _ := hRegularN
  let _ := hRegularD
  let : LocallyCompactSpace Q := hPI.locallyCompactSpace
  let hσf := geometricCompactPullback_smooth i ν I J dJ n hprojJ σ hσ
  let eC := geometricSplitCoefficientEquiv i ν hStandard hG hi hν hN I J dI dJ n
    hSource hTarget σ
  let slice := splitStagesKernelSlice dI.projection s (fun m => dI.projection_levi m)
    hprojI (continuous_geometricSplitSection i ν I dI) P H hker hHP hPc hHc hSH
    (σ.comp f) hσf F l
  let raw := quotientCoinvariantSimple D (((σ.comp f).comp φ).comp j) slice
  let eStages := splitStagesCompactEquiv dI.projection s (fun m => dI.projection_levi m)
    hprojI (continuous_geometricSplitSection i ν I dI) P H hker hHP hPc hHc hSH
    (σ.comp f) hσf quotientMeasure hKernelBasis μN μD hCompatible
    (isClosed_singleton.preimage hprojI) hBasis
  let χ0 := Jacquet.complexCharacter (splitKernelHaarRatio rP sP HP hSI hHPc)
  let ρ0 := splitKernelCoefficientAction rP sP HP hSI ((σ.comp f).comp φ)
  have hSub := compactInducedSubgroupTwistCongr_eval
    (geometricSplit_comap_section i ν I J dI n) χ0 ρ0
    (eStages (Representation.Coinvariants.mk _ F)) l
  have hInt := splitStagesCompactEquiv_eval_mk_integral dI.projection s
    (fun m => dI.projection_levi m) hprojI (continuous_geometricSplitSection i ν I dI)
    P H hker hHP hPc hHc hSH (σ.comp f) hσf quotientMeasure hKernelBasis μN μD
    hCompatible (isClosed_singleton.preimage hprojI) hBasis F l
  have hMap := (AlgebraicIntegral.integral_linearMap raw
    (quotientCoinvariantSimple_finMeasSupp D _ quotientMeasure slice)
    eC.toLinearEquiv.toLinearMap).symm
  exact (congrArg eC (hSub.trans hInt)).trans hMap

end RationalPointFamily

end Langlands.Aubert.General
