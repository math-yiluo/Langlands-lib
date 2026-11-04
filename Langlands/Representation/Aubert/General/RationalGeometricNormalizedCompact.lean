import Langlands.Representation.Aubert.General.RationalGeometricInducingHalfCoefficient
import Langlands.Representation.Aubert.General.RationalGeometricCompactAnalysis
import Langlands.Representation.Induction.CharacterTwistProof
import Langlands.Representation.Category.Twist

/-! # Actual compact comparison with the original endpoint normalizations -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

universe u uV uW

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Induction
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

local notation "L" => levi i ν I
local notation "K" => Subgroup.subgroupOf
  (geometricTargetIntersection (levi i ν I) (parabolic i ν J)
    (n : RationalPoint k G.X)) (levi i ν I)
local notation "S" => Subgroup.subgroupOf
  (geometricSourceIntersection (unipotent i ν I) (levi i ν J)
    (n : RationalPoint k G.X)) (levi i ν J)
local notation "Ls" => Subgroup.subgroupOf
  (geometricSourceIntersection (levi i ν I) (levi i ν J)
    (n : RationalPoint k G.X)) (levi i ν J)
local notation "p" => geometricCoefficientLeviMap
  (levi i ν I) (parabolic i ν J) (levi i ν J) (unipotent i ν J)
  (n : RationalPoint k G.X) hTarget
local notation "χ" => HaarModulus.closedHalfCharacter
  (unipotent i ν J) hUJ (levi i ν J) dJ.levi_le_normalizer
local notation "κ" => HaarModulus.closedInverseHalfCharacter
  (unipotent i ν I) hUI (levi i ν I) dI.levi_le_normalizer
local notation "δU" => geometricCompactRadicalModulus i ν I J dI n hUI
local notation "δD" => geometricCompactCorrectionModulus i ν I J dI n hUI hPJ
local notation "χp" => MonoidHom.comp (MonoidHom.comp χ (Subgroup.subtype Ls)) p
local notation "N" => geometricCompactKernel i ν I J dI n
local notation "D" => geometricCompactKernelIntersection i ν I J dI n

/-- The exact remaining coefficient character on the entire target
intersection, before a distinct-radical balance is used. -/
def geometricNormalizedCompactCharacter : K →* ℂˣ :=
  (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δU) /
    Jacquet.complexCharacter δD) * χp

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The original ordinary source Jacquet carrier with all remaining factors. -/
abbrev geometricNormalizedCompactCoefficient (σ : Representation ℂ (levi i ν J) V) :
    Representation ℂ K (Jacquet.Coinvariants σ S) :=
  twist (geometricNormalizedCompactCharacter i ν I J dI dJ n hUI hUJ hPJ hTarget)
    ((Jacquet.action σ S Ls hSource.levi_le_normalizer).comp p)

/-- The original compact orbit quotient, with the inducing positive half
and the target inverse half of the actual ambient radicals. -/
abbrev geometricNormalizedCompactSource (σ : Representation ℂ (levi i ν J) V) :=
  twist κ (geometricCompactSource i ν I J dI dJ n (twist χ σ))

/-- Compact induction of the explicitly normalized actual coefficient. -/
abbrev geometricNormalizedCompactTarget (σ : Representation ℂ (levi i ν J) V) :=
  compactInduced K
    (geometricNormalizedCompactCoefficient i ν I J dI dJ n hUI hUJ hPJ
      hSource hTarget σ)

local instance normalizedKernelMeasurableSpace : MeasurableSpace N := borel N
local instance normalizedKernelBorelSpace : BorelSpace N := ⟨rfl⟩
local instance normalizedIntersectionMeasurableSpace : MeasurableSpace D := borel D
local instance normalizedIntersectionBorelSpace : BorelSpace D := ⟨rfl⟩

variable
  (hPI : IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hMJ : IsClosed (levi i ν J : Set (RationalPoint k G.X)))
  (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))

section CoefficientComparison

variable [LocallyCompactSpace (geometricCompactKernel i ν I J dI n)]

local notation "θ" => geometricCompactHaarCharacter i ν I J dI n hPI hPJ

/-- The target inverse half cancels exactly half of the numerator of the
actual Haar ratio, on every point of the full target intersection. -/
theorem geometricNormalizedCompactCharacter_eq (l : K) :
    (((κ).comp (K).subtype) * θ * χp) l =
      geometricNormalizedCompactCharacter i ν I J dI dJ n hUI hUJ hPJ hTarget l := by
  change κ (l : L) * θ l * χp l =
    (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δU) l /
      Jacquet.complexCharacter δD l) * χp l
  rw [geometricCompactHaarCharacter_eq_ambient i ν I J dI n hUI hPJ hPI l]
  have hsquare :
      Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δU) l ^ 2 =
        Jacquet.complexCharacter δU l := by
    simpa only [Jacquet.complexCharacter, MonoidHom.comp_apply, map_pow] using
      congrArg (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
        (Jacquet.positiveHalfCharacter_sq δU l)
  change (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δU) l)⁻¹ *
      (Jacquet.complexCharacter δU l / Jacquet.complexCharacter δD l) * χp l =
    (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δU) l /
      Jacquet.complexCharacter δD l) * χp l
  rw [← hsquare, pow_two]
  simp only [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel, one_mul]

/-- The inducing half passes through the original source Jacquet quotient
after pullback along the actual intersection projection. -/
def geometricInducingHalfJacquetEquiv (σ : Representation ℂ (levi i ν J) V) :
    Representation.Equiv
      ((Jacquet.action (twist χ σ) S Ls hSource.levi_le_normalizer).comp p)
      (geometricInducingHalfSourceCoefficientAction i ν I J dJ n hUJ
        hSource hTarget σ) :=
  restrictAlongEquiv p (Jacquet.actionTwistEquiv σ S Ls hSource.levi_le_normalizer χ
    (geometricSourceRadical_le_ker_inducingHalfCharacter i ν I J dJ n hUJ hMJ hUc))

@[simp] theorem geometricInducingHalfJacquetEquiv_mk
    (σ : Representation ℂ (levi i ν J) V) (v : V) :
    geometricInducingHalfJacquetEquiv i ν I J dJ n hUJ hSource hTarget hMJ hUc σ
      (Jacquet.mk (twist χ σ) S v) = Jacquet.mk σ S v := rfl

/-- The actual Haar-corrected coefficient, with target inverse half, is
the explicitly normalized coefficient on the original ordinary Jacquet carrier. -/
def geometricNormalizedCompactCoefficientEquiv (σ : Representation ℂ (levi i ν J) V) :
    (twist ((κ).comp (K).subtype)
      (geometricCompactCoefficient i ν I J dI n hPI hPJ hSource hTarget
        (twist χ σ))).Equiv
      (geometricNormalizedCompactCoefficient i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget σ) := by
  refine (twistEquiv ((κ).comp (K).subtype) (twistEquiv θ
    (geometricInducingHalfJacquetEquiv i ν I J dJ n hUJ
      hSource hTarget hMJ hUc σ))).trans (equivOfRepresentationEq ?_)
  change twist ((κ).comp (K).subtype)
    (twist θ (twist χp ((Jacquet.action σ S Ls hSource.levi_le_normalizer).comp p))) = _
  rw [twist_twist, twist_twist]
  apply congrArg (fun c : K →* ℂˣ =>
    twist c ((Jacquet.action σ S Ls hSource.levi_le_normalizer).comp p))
  exact MonoidHom.ext (geometricNormalizedCompactCharacter_eq
    i ν I J dI dJ n hUI hUJ hPJ hTarget hPI)

@[simp] theorem geometricNormalizedCompactCoefficientEquiv_mk
    (σ : Representation ℂ (levi i ν J) V) (v : V) :
    geometricNormalizedCompactCoefficientEquiv i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget hPI hMJ hUc σ (Jacquet.mk (twist χ σ) S v) =
      Jacquet.mk σ S v := rfl

@[simp] theorem geometricNormalizedCompactCoefficientEquiv_symm_mk
    (σ : Representation ℂ (levi i ν J) V) (v : V) :
    (geometricNormalizedCompactCoefficientEquiv i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget hPI hMJ hUc σ).symm (Jacquet.mk σ S v) =
      Jacquet.mk (twist χ σ) S v := rfl

/-- The full coefficient normalization commutes with original coefficient maps. -/
theorem geometricNormalizedCompactCoefficientEquiv_natural
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (levi i ν J) V} {τ : Representation ℂ (levi i ν J) W}
    (a : σ.IntertwiningMap τ) (z : Jacquet.Coinvariants (twist χ σ) S) :
    geometricNormalizedCompactCoefficientEquiv i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget hPI hMJ hUc τ
        (Jacquet.map S Ls hSource.levi_le_normalizer (twistIntertwining χ a) z) =
      Jacquet.map S Ls hSource.levi_le_normalizer a
        (geometricNormalizedCompactCoefficientEquiv i ν I J dI dJ n hUI hUJ hPJ
          hSource hTarget hPI hMJ hUc σ z) := by
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective (twist χ σ) S z
  change geometricNormalizedCompactCoefficientEquiv i ν I J dI dJ n hUI hUJ hPJ
      hSource hTarget hPI hMJ hUc τ (Jacquet.mk (twist χ τ) S (a v)) = _
  rw [geometricNormalizedCompactCoefficientEquiv_mk,
    geometricNormalizedCompactCoefficientEquiv_mk]
  rfl

end CoefficientComparison

variable [T2Space (RationalPoint k G.X)]
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hN : HasPointNormalizerComparison i)
  (hMI : IsClosed (levi i ν I : Set (RationalPoint k G.X)))
  (hprojI : Continuous dI.projection) (hprojJ : Continuous dJ.projection)

/-- The actual compact orbit quotient with both original endpoint halves
is compact induction of the explicitly normalized coefficient. -/
def geometricNormalizedCompactEquiv (σ : Representation ℂ (levi i ν J) V)
    (hσ : IsSmooth σ) :
    (geometricNormalizedCompactSource i ν I J dI dJ n hUI hUJ σ).Equiv
      (geometricNormalizedCompactTarget i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget σ) := by
  letI : LocallyCompactSpace N :=
    geometricCompactKernel_locallyCompactSpace i ν I J dI n hUI
  let e0 := geometricCompactEquivOfCompactLimit i ν I J dI n hUI hPI hPJ hUc
    hStandard hG hi hν hN dJ hMI hprojI hprojJ (twist χ σ)
    ((HaarModulus.isSmooth_twist_closedHalfCharacter_iff
      (unipotent i ν J) hUJ (levi i ν J) dJ.levi_le_normalizer σ).mpr hσ)
    hSource hTarget
  let e1 := compactInductionTwistEquiv K
    { toMonoidHom := κ
      isOpen_ker := HaarModulus.isOpen_ker_closedInverseHalfCharacter
        (unipotent i ν I) hUI L dI.levi_le_normalizer }
    (geometricCompactCoefficient i ν I J dI n hPI hPJ hSource hTarget (twist χ σ))
  exact (twistEquiv κ e0).trans (e1.trans (compactInducedEquiv K
    (geometricNormalizedCompactCoefficientEquiv i ν I J dI dJ n hUI hUJ hPJ
      hSource hTarget hPI hMJ hUc σ)))

include hPJ hPI hMJ hUc hStandard hG hi hν hN hMI hprojI hprojJ hSource hTarget in
/-- Smoothness of the original normalized compact quotient follows from
the actual equivalence and smoothness of compact induction. -/
theorem isSmooth_geometricNormalizedCompactSource
    (σ : Representation ℂ (levi i ν J) V) (hσ : IsSmooth σ) :
    IsSmooth (geometricNormalizedCompactSource i ν I J dI dJ n hUI hUJ σ) := by
  let e := geometricNormalizedCompactEquiv i ν I J dI dJ n hUI hUJ hPJ
    hSource hTarget hPI hMJ hUc hStandard hG hi hν hN hMI hprojI hprojJ σ hσ
  exact isSmooth_of_surjective e.symm.toIntertwiningMap e.symm.surjective
    (compactInduced_smooth _ _)

/-- The comparison on precisely the original smooth carriers. -/
def geometricNormalizedCompactSmoothIso (σ : SmoothRep ℂ (levi i ν J)) :
    SmoothRep.of (geometricNormalizedCompactSource i ν I J dI dJ n hUI hUJ σ.representation)
        (isSmooth_geometricNormalizedCompactSource i ν I J dI dJ n hUI hUJ hPJ
          hSource hTarget hPI hMJ hUc hStandard hG hi hν hN hMI hprojI hprojJ
          σ.representation σ.isSmooth) ≅
      SmoothRep.of (geometricNormalizedCompactTarget i ν I J dI dJ n hUI hUJ hPJ
        hSource hTarget σ.representation) (compactInduced_smooth _ _) :=
  SmoothRep.mkIso (geometricNormalizedCompactEquiv i ν I J dI dJ n hUI hUJ hPJ
    hSource hTarget hPI hMJ hUc hStandard hG hi hν hN hMI hprojI hprojJ
    σ.representation σ.isSmooth)

end Langlands.Aubert.General.RationalPointFamily
