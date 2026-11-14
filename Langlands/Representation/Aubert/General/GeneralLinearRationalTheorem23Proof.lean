import Langlands.Representation.Aubert.General.GeneralLinearRationalTheorem23Statement
import Langlands.Representation.Aubert.AubertTheorem23Proof
import Langlands.Representation.Aubert.SegmentSocleHeadProof
import Langlands.Representation.Aubert.BinaryProductExactnessProof
import Langlands.Representation.Aubert.GradedInductionRingLawsProof
import Langlands.Representation.Aubert.SegmentPolynomialComparisonProof

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped DirectSum CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily.GL

open GroupScheme SmoothRep GeneralLinear
open Langlands.AlgebraicGeometry.PointTopology

private theorem conjugate_eq_of_intertwines
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℤ A] [Module ℤ B] (e : A ≃ₗ[ℤ] B)
    (D : A →ₗ[ℤ] A) (R : B →ₗ[ℤ] B)
    (h : e.toLinearMap.comp D = R.comp e.toLinearMap) :
    e.toLinearMap.comp (D.comp e.symm.toLinearMap) = R := by
  ext x
  change e (D (e.symm x)) = R x
  calc
    e (D (e.symm x)) = R (e (e.symm x)) := LinearMap.congr_fun h _
    _ = R x := by rw [e.apply_symm_apply]

theorem rationalUnadjustedOperatorIdentification :
    RationalUnadjustedOperatorIdentificationStatement.{u, v} := by
  intro p _ F T N ν hν
  let := T.topology
  let : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  let := rationalGLTopology F T N
  have h := rationalAlternatingOperatorComparison.{u, v} F T N ν hν
  refine ⟨h.1, ?_⟩
  intro _ _ _
  have h' := h.2
  refine ⟨h'.1, ?_⟩
  intro hU hP hproj hUc hiFl hrFl
  exact conjugate_eq_of_intertwines (rationalGLPullbackEquiv.{u, v} F T N)
    (Aubert.alternatingOperator.{u, max (u + 1) v} F T N) _
    (h'.2 hU hP hproj hUc hiFl hrFl)

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)

theorem rationalSupportAdjustment : RationalSupportAdjustmentStatement.{u, v} F T := by
  let := T.topology
  let : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  intro N
  let := rationalGLTopology F T N
  let e := GroupScheme.GeneralLinear.rationalPointsContinuousMulEquiv N F.Carrier
  let eK := rationalGLPullbackEquiv.{u, v} F T N
  constructor
  · intro E hE
    let M := SmoothRep.pullback e.symm E
    have hM : M.IsIrreducible :=
      (Langlands.isIrreducible_comp_continuousMulEquiv_iff E.representation e.symm).mpr hE
    have hc : eK.symm (FiniteLengthGrothendieckGroup.ofRepresentation E
        (hasFiniteLength_of_isIrreducible hE)) =
        FiniteLengthGrothendieckGroup.ofRepresentation M
          (hasFiniteLength_of_isIrreducible hM) :=
      FiniteLengthGrothendieckGroup.pullback_ofRepresentation e.symm E _ _
    change eK (Aubert.adjustedOperator.{u, max (u + 1) v} F T N
        (eK.symm _)) =
      rationalSupportSign.{u, v} F T N E hE •
        eK (Aubert.alternatingOperator.{u, max (u + 1) v} F T N (eK.symm _))
    have hm := Aubert.adjustedOperator_irreducible.{u, max (u + 1) v} F T N M hM
    change Aubert.adjustedOperator.{u, max (u + 1) v} F T N
        (FiniteLengthGrothendieckGroup.ofRepresentation M _) = _ at hm
    rw [hc, hm, map_smul]
    rfl
  · intro E hE B σ hσ hqc hsub
    have hM : (SmoothRep.pullback e.symm E).IsIrreducible :=
      (Langlands.isIrreducible_comp_continuousMulEquiv_iff E.representation e.symm).mpr hE
    exact Aubert.supportSign_of_support.{u, max (u + 1) v} F T B σ hσ hqc
      (SmoothRep.pullback e.symm E) hM hsub

theorem rationalRankZero : RationalRankZeroStatement.{u, v} F T := by
  let := T.topology
  let : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  let := rationalGLTopology F T 0
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp only [rationalUnadjustedOperator, LinearMap.comp_apply,
      Aubert.alternatingOperator_rankZero, LinearMap.id_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  · ext x
    simp only [rationalAdjustedOperator, LinearMap.comp_apply,
      Aubert.adjustedOperator_rankZero, LinearMap.id_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  · intro E hE
    exact Aubert.supportSign_rankZero.{u, max (u + 1) v} F T _

private theorem rationalGradedPullbackEquiv_homogeneous
    (N : ℕ) :
    let := T.topology
    ∀ x, rationalGradedPullbackEquiv.{u, v} F T (Aubert.gradedInclusion.{u, max (u + 1) v} F T N x) =
      rationalGradedInclusion.{u, v} F T N (rationalGLPullbackEquiv.{u, v} F T N x) := by
  let := T.topology
  dsimp only
  intro x
  simp only [rationalGradedPullbackEquiv, Aubert.gradedInclusion,
    rationalGradedInclusion, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof,
    LinearEquiv.coe_coe]

theorem rationalGradedHomogeneous : RationalGradedHomogeneousStatement.{u, v} F T := by
  let := T.topology
  intro N x
  let e := rationalGradedPullbackEquiv.{u, v} F T
  let eN := rationalGLPullbackEquiv.{u, v} F T N
  obtain ⟨y, rfl⟩ := eN.surjective x
  change e (Aubert.gradedAdjustedOperator.{u, max (u + 1) v} F T
      (e.symm (rationalGradedInclusion.{u, v} F T N (eN y)))) =
    rationalGradedInclusion.{u, v} F T N
      (eN (Aubert.adjustedOperator.{u, max (u + 1) v} F T N (eN.symm (eN y))))
  rw [← rationalGradedPullbackEquiv_homogeneous.{u, v} F T, e.symm_apply_apply,
    Aubert.gradedAdjustedOperator_homogeneous, rationalGradedPullbackEquiv_homogeneous,
    eN.symm_apply_apply]

theorem rationalSegmentSocleHead : RationalSegmentSocleHeadStatement.{u, v} F T := by
  let := T.topology
  let : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  intro Δ πZ πS hZ hS
  let := rationalGLTopology F T Δ.degree
  let e := GroupScheme.GeneralLinear.rationalPointsContinuousMulEquiv Δ.degree F.Carrier
  let eK := rationalGLPullbackEquiv.{u, v} F T Δ.degree
  have hπZ := hasFiniteLength_of_isIrreducible (by
    obtain ⟨_, _, h⟩ := hZ
    exact h.1)
  have hπS := hasFiniteLength_of_isIrreducible (by
    obtain ⟨_, _, h⟩ := hS
    exact h.1)
  have hx : FiniteLengthGrothendieckGroup.ofRepresentation (SmoothRep.pullback e πZ)
      (pullbackFunctor_preservesFiniteLength e πZ hπZ) =
      eK (GeneralLinear.finiteLengthClass.{max (u + 1) v, u} Δ.degree F.Carrier πZ hπZ) :=
    (FiniteLengthGrothendieckGroup.pullback_ofRepresentation e πZ hπZ _).symm
  have hy : FiniteLengthGrothendieckGroup.ofRepresentation (SmoothRep.pullback e πS)
      (pullbackFunctor_preservesFiniteLength e πS hπS) =
      eK (GeneralLinear.finiteLengthClass.{max (u + 1) v, u} Δ.degree F.Carrier πS hπS) :=
    (FiniteLengthGrothendieckGroup.pullback_ofRepresentation e πS hπS _).symm
  change eK (Aubert.alternatingOperator.{u, max (u + 1) v} F T Δ.degree
    (eK.symm _)) = (-1 : ℤ) ^ (Δ.degree - Δ.length) • _
  rw [hx, hy, eK.symm_apply_apply, Aubert.segmentSocleHead F T Δ πZ πS hZ hS,
    map_smul]

variable (hx : Aubert.BinaryProductExactnessStatement.{u, max (u + 1) v} F T)
  (hl : Aubert.GradedInductionRingLawsStatement.{u, max (u + 1) v} F T hx)
  (hp : Aubert.SegmentPolynomialComparisonStatement.{u, max (u + 1) v} F T hx hl)

theorem rationalWholeGradedTheorem23 :
    RationalWholeGradedTheorem23Statement.{u, v} F T hx hl hp := by
  let := T.topology
  let := Aubert.gradedInductionRing.{u, max (u + 1) v} F T hx hl
  let := rationalGradedInductionRing.{u, v} F T hx hl
  let e := rationalGradedRingEquiv.{u, v} F T hx hl
  let D := Aubert.gradedAdjustedOperator.{u, max (u + 1) v} F T
  let Z := Aubert.zelevinskyEndomorphism.{u, max (u + 1) v} F T hx hl hp
  obtain ⟨hm, hi, hc⟩ := Aubert.aubertTheorem23.{u, max (u + 1) v} F T hx hl hp
  change (∀ x y, D (x * y) = D x * D y) at hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    change e (D (e.symm (x * y))) = e (D (e.symm x)) * e (D (e.symm y))
    rw [map_mul, hm, map_mul]
  · change e (D (e.symm 1)) = 1
    have hu := Aubert.gradedAdjustedOperator_unit.{u, max (u + 1) v} F T
    change D 1 = 1 at hu
    rw [map_one, hu, map_one]
  · intro x
    change e (D (e.symm (e (D (e.symm x))))) = x
    rw [e.symm_apply_apply, Aubert.adjustedInvolutivity F T, e.apply_symm_apply]
  · intro x
    change e (Z (e.symm (e (Z (e.symm x))))) = x
    rw [e.symm_apply_apply, hi, e.apply_symm_apply]
  · apply LinearMap.ext
    intro x
    change e (D (e.symm x)) = e (Z (e.symm x))
    exact congrArg e (LinearMap.congr_fun hc _)
  · intro P
    rfl
  · intro d
    change rationalGradedPullbackEquiv.{u, v} F T
        (Aubert.segmentMonomialBasis.{u, max (u + 1) v} F T hx hl hp d) = _
    rw [Aubert.segmentMonomialBasis_apply]

theorem rationalTheorem23 : RationalTheorem23Statement.{u, v} := by
  refine ⟨rationalUnadjustedOperatorIdentification, ?_⟩
  intro p _ F T hx hl hp
  exact ⟨rationalSupportAdjustment F T, rationalRankZero F T,
    rationalGradedHomogeneous F T, rationalSegmentSocleHead F T,
    rationalWholeGradedTheorem23 F T hx hl hp⟩

/-- The whole-ring result with every matrix premise supplied by its published proof. -/
theorem rationalWholeGradedTheorem23Canonical :
    let hx := Aubert.binaryProductExactness.{u, max (u + 1) v} F T
    let hl := Aubert.gradedInductionRingLaws.{u, max (u + 1) v} F T hx
    RationalWholeGradedTheorem23Statement.{u, v} F T hx hl
      (Aubert.segmentPolynomialComparison.{u, max (u + 1) v} F T hx hl) :=
  rationalWholeGradedTheorem23 F T _ _ _

end Langlands.Aubert.General.RationalPointFamily.GL
