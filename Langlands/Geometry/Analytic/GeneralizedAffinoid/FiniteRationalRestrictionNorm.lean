import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalGluingProof
import Langlands.Geometry.Analytic.TateUniversal.Definitions
import Mathlib.Analysis.Normed.Operator.Banach

/-! # Closed range and norm estimates for finite rational restrictions -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} {I : Type v} [Fintype I]
  (D : I → RationalChart K A)

/-- Simultaneous restriction to the actual finite family of rational quotients. -/
def finiteRestriction : A →L[K] (∀ i, (D i).algebra) :=
  ContinuousLinearMap.pi fun i => (D i).baseMap.toContinuousLinearMap

omit [CompleteSpace K] [Fintype I] in
@[simp]
theorem finiteRestriction_apply (a : A) (i : I) :
    finiteRestriction D a i = (D i).baseMap a := rfl

omit [Fintype I] in
/-- The actual restriction family satisfies the original overlap equations. -/
theorem finiteRestriction_compatible (a : A) (i j : I) :
    (interLeft (D i) (D j)).restriction ((D i).baseMap a) =
      (interRight (D i) (D j)).restriction ((D j).baseMap a) := by
  exact (congrArg (fun f : BoundedAlgHom K A ((D i).inter (D j)).algebra => f a)
    (interLeft (D i) (D j)).comp_baseMap).trans
      (congrArg (fun f : BoundedAlgHom K A ((D i).inter (D j)).algebra => f a)
        (interRight (D i) (D j)).comp_baseMap).symm

/-- Scalar rational descent identifies the range with the overlap equalizer. -/
theorem range_finiteRestriction
    (hcover : ∀ x : BanachSpectrum A, ∃ i, x ∈ (D i).locus) :
    Set.range (finiteRestriction D) =
      {s | ∀ i j, (interLeft (D i) (D j)).restriction (s i) =
        (interRight (D i) (D j)).restriction (s j)} := by
  ext s
  constructor
  · rintro ⟨a, rfl⟩
    exact finiteRestriction_compatible D a
  · intro hs
    obtain ⟨a, ha, _⟩ := wholeSpectrumRationalGluing K A I D hcover s hs
    exact ⟨a, funext ha⟩

/-- Uniqueness in scalar gluing makes the actual restriction map injective. -/
theorem injective_finiteRestriction
    (hcover : ∀ x : BanachSpectrum A, ∃ i, x ∈ (D i).locus) :
    Function.Injective (finiteRestriction D) := by
  intro a b hab
  obtain ⟨c, _, hc⟩ := wholeSpectrumRationalGluing K A I D hcover
    (finiteRestriction D a) (finiteRestriction_compatible D a)
  exact (hc a (fun _ => rfl)).trans
    (hc b (fun i => (congrFun hab i).symm)).symm

/-- The overlap equalizer is closed in the finite product of quotient Banach algebras. -/
theorem isClosed_range_finiteRestriction
    (hcover : ∀ x : BanachSpectrum A, ∃ i, x ∈ (D i).locus) :
    IsClosed (Set.range (finiteRestriction D)) := by
  rw [range_finiteRestriction D hcover]
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_eq
      ((interLeft (D i) (D j)).restriction.continuous.comp (continuous_apply i))
      ((interRight (D i) (D j)).restriction.continuous.comp (continuous_apply j))

omit [CompleteSpace K] in
/-- Every rational structural map, and hence the product restriction, is contractive. -/
theorem norm_finiteRestriction_le (a : A) : ‖finiteRestriction D a‖ ≤ ‖a‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg a)).2
  intro i
  exact RationalPresentation.norm_baseMap_le K A (D i).radii
    (D i).denominator (D i).numerators a

namespace AuxiliaryScalar

variable (L : Type w) [NontriviallyNormedField L] [NormedAlgebra L A]

/-- The scalar action on a rational quotient induced through its actual base map. -/
@[instance_reducible]
def quotientNormedAlgebra (d : RationalChart K A) : NormedAlgebra L d.algebra where
  toAlgebra := (d.baseMap.toAlgHom.toRingHom.comp (algebraMap L A)).toAlgebra
  norm_smul_le z b := by
    change ‖d.baseMap (algebraMap L A z) * b‖ ≤ ‖z‖ * ‖b‖
    apply (norm_mul_le _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg b)
    calc
      ‖d.baseMap (algebraMap L A z)‖ ≤ ‖algebraMap L A z‖ :=
        RationalPresentation.norm_baseMap_le K A d.radii d.denominator d.numerators _
      _ = ‖z‖ * ‖(1 : A)‖ := norm_algebraMap A z
      _ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left (norm_one_le K A) (norm_nonneg z)
      _ = ‖z‖ := mul_one _

/-- The unchanged structural ring map is bounded and linear over the auxiliary scalars. -/
def baseMapOver (d : RationalChart K A) :
    letI := quotientNormedAlgebra L d
    BoundedAlgHom L A d.algebra := by
  letI := quotientNormedAlgebra L d
  exact {
    toAlgHom := { d.baseMap.toAlgHom.toRingHom with commutes' := fun _ => rfl }
    bounded := d.baseMap.bounded }

/-- The original product restriction with the induced auxiliary linear structure. -/
def finiteRestrictionOver :
    letI (i : I) := quotientNormedAlgebra L (D i)
    A →L[L] (∀ i, (D i).algebra) := by
  letI (i : I) := quotientNormedAlgebra L (D i)
  exact ContinuousLinearMap.pi fun i => (baseMapOver L (D i)).toContinuousLinearMap

omit [CompleteSpace K] [Fintype I] in
@[simp]
theorem finiteRestrictionOver_apply (a : A) (i : I) :
    finiteRestrictionOver D L a i = (D i).baseMap a := rfl

include L in
/-- A nontrivially normed auxiliary scalar field supplies the open-mapping estimate.
No auxiliary scalar structure on overlap algebras is required. -/
theorem exists_norm_bound
    (hcover : ∀ x : BanachSpectrum A, ∃ i, x ∈ (D i).locus) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : A, ‖a‖ ≤ C * ‖fun i => (D i).baseMap a‖ := by
  let (i : I) := quotientNormedAlgebra L (D i)
  have hinj : Function.Injective (finiteRestrictionOver D L) :=
    injective_finiteRestriction D hcover
  have hclosed : IsClosed (Set.range (finiteRestrictionOver D L)) :=
    isClosed_range_finiteRestriction D hcover
  obtain ⟨C, hC⟩ := ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range
    (finiteRestrictionOver D L) hinj hclosed
  refine ⟨(C : ℝ) + 1, by positivity, fun a => ?_⟩
  have h := hC.le_mul_dist a 0
  simp only [dist_zero_right, map_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

end AuxiliaryScalar

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
