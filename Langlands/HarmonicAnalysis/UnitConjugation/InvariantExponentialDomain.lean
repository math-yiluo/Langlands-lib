import Langlands.Galois.Local.AbsoluteDefinitions
import Langlands.HarmonicAnalysis.UnitConjugation.ExponentialConjugacy
import Langlands.HarmonicAnalysis.UnitConjugation.NilpotentApproximation
import Langlands.HarmonicAnalysis.UnitConjugation.SmallExponentialSubalgebra
import Langlands.LinearAlgebra.IntegralEndomorphismBasis
import Mathlib.Topology.MetricSpace.Ultra.Pi

/-! # An invariant clopen domain of exponential coordinates -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Set Function Metric Module ValuativeRel _root_.Topology

variable (F A : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [hChar : CharZero F]

local instance : NontriviallyNormedField F := LocalGalois.localNormedField F
local instance : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
local instance : CompleteSpace F := LocalGalois.localNormedField_complete F

variable [NormedRing A] [hAlg : NormedAlgebra F A] [hFin : FiniteDimensional F A]

/-- The exponential minus one is an open embedding on a conjugation-invariant
clopen neighborhood of zero of a finite-dimensional algebra over a local field. -/
def InvariantExponentialDomainStatement : Prop :=
  ∃ C : Set A, IsClopen C ∧ (0 : A) ∈ C ∧
    (∀ (u : Aˣ) (x : A), conjugationHomeomorph u x ∈ C ↔ x ∈ C) ∧
    IsOpenEmbedding (fun x : C => NormedSpace.exp (x : A) - 1)

omit [CharZero F] in
private theorem coordinateEnd_ultrametric (ι : Type*) [Fintype ι] :
    IsUltrametricDist ((ι → F) →L[F] (ι → F)) := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  intro a b
  apply ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg a).trans (le_max_left _ _))
  intro v
  refine (IsUltrametricDist.norm_add_le_max (a v) (b v)).trans (max_le ?_ ?_)
  · exact (a.le_opNorm v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg v))
  · exact (b.le_opNorm v).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg v))

omit [CharZero F] hFin in
private theorem coordinateEnd_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι F A) (T : Module.End F A) {r : ℝ} (hr : 0 ≤ r)
    (hEntry : ∀ i j, ‖LinearMap.toMatrix b b T i j‖ ≤ r) :
    ‖Module.End.toContinuousLinearMap (ι → F) (b.equivFun.conjAlgEquiv F T)‖ ≤ r := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hr
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hr (norm_nonneg v))).mpr
  intro i
  have h : (Module.End.toContinuousLinearMap (ι → F) (b.equivFun.conjAlgEquiv F T) v) i =
      ∑ j, LinearMap.toMatrix b b T i j * v j := by
    have hM := congrFun (LinearMap.toMatrix_mulVec_repr b b T (b.equivFun.symm v)) i
    change b.equivFun (T (b.equivFun.symm v)) i = _
    rw [Basis.equivFun_apply]
    rw [← hM, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [h]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr (norm_nonneg v))
  intro j _
  rw [norm_mul]
  exact mul_le_mul (hEntry i j) (norm_le_pi_norm v j) (norm_nonneg _) hr

set_option maxHeartbeats 3400000 in
set_option backward.isDefEq.respectTransparency false in
include hChar hAlg hFin in
theorem invariantExponentialDomain : InvariantExponentialDomainStatement A := by
  classical
  let : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let I := Fin (Module.finrank F A)
  let V := I → F
  let M := V →L[F] V
  let : IsUltrametricDist M := coordinateEnd_ultrametric F I
  obtain ⟨ε, hε, hSmall⟩ := smallExponentialSubalgebra (F := F) (A := M)
  obtain ⟨a, ha, haε⟩ := NormedField.exists_norm_lt F hε
  let r := ‖a‖
  have ha₀ : a ≠ 0 := norm_pos_iff.mp ha
  let B := closedBall (0 : M) r
  obtain ⟨hConv, hCharts⟩ := hSmall r ha haε.le
  let C : Set A := (fun x : A => leftRegularCoefficients F (a⁻¹ • x)) ⁻¹' closedBall 0 1
  have hC : IsClopen C :=
    (IsUltrametricDist.isClopen_closedBall (0 : I → F) one_ne_zero).preimage
      (continuous_leftRegularCoefficients.comp (continuous_id.const_smul a⁻¹))
  have hC₀ : (0 : A) ∈ C := by
    change leftRegularCoefficients F (a⁻¹ • (0 : A)) ∈ closedBall 0 1
    rw [smul_zero, (leftRegularCoefficients_eq_zero_iff (F := F) 0).mpr IsNilpotent.zero]
    exact mem_closedBall_self zero_le_one
  have hInv (u : Aˣ) (x : A) : conjugationHomeomorph u x ∈ C ↔ x ∈ C := by
    change leftRegularCoefficients F (a⁻¹ • conjugationHomeomorph u x) ∈ closedBall 0 1 ↔ _
    have hsmul : a⁻¹ • conjugationHomeomorph u x = conjugationHomeomorph u (a⁻¹ • x) := by
      simp only [conjugationHomeomorph_apply, mul_smul_comm, smul_mul_assoc]
    rw [hsmul, leftRegularCoefficients_conjugation]
    rfl
  let e (b : Basis I F A) : Module.End F A ≃ₐ[F] M :=
    (b.equivFun.conjAlgEquiv F).trans (Module.End.toContinuousLinearMap V)
  let j (b : Basis I F A) : A →ₐ[F] M := (e b).toAlgHom.comp (Algebra.lmul F A)
  have hj (b : Basis I F A) : IsClosedEmbedding (j b) :=
    LinearMap.isClosedEmbedding_of_injective (f := (j b).toLinearMap)
      (LinearMap.ker_eq_bot.mpr ((e b).injective.comp Algebra.lmul_injective))
  let f (x : A) := NormedSpace.exp x - 1
  have hf (b : Basis I F A) (x : A) : j b (f x) = NormedSpace.exp (j b x) - 1 :=
    map_exp_sub_one_of_closedEmbedding (j b) (hj b) x
  let U (b : Basis I F A) := j b ⁻¹' B
  have hU (b : Basis I F A) : IsOpen (U b) :=
    (IsUltrametricDist.isOpen_closedBall _ ha.ne').preimage (hj b).continuous
  have hCover (x : A) (hx : x ∈ C) : ∃ b : Basis I F A, x ∈ U b := by
    let O := (valuation F).integer
    let : Module O A := Module.compHom A (algebraMap O F)
    let : IsScalarTower O F A := IsScalarTower.of_compHom O F A
    let T := Algebra.lmul F A (a⁻¹ • x)
    have hTest (y : F) : y ∈ range (algebraMap O F) ↔ ‖y‖ ≤ 1 := by
      change (∃ z : O, z.val = y) ↔ ‖y‖ ≤ 1
      rw [show (1 : ℝ) = ‖(1 : F)‖ from norm_one.symm, LocalGalois.localNormedField_le, map_one]
      exact ⟨fun ⟨z, hz⟩ => hz ▸ z.property, fun hy => ⟨⟨y, hy⟩, rfl⟩⟩
    have hcoeff (i : ℕ) : T.charpoly.coeff i ∈ range (algebraMap O F) := by
      apply (hTest _).2
      rw [mem_preimage, mem_closedBall, dist_zero_right] at hx
      by_cases hi : i < Module.finrank F A
      · exact (pi_norm_le_iff_of_nonneg zero_le_one).mp hx ⟨i, hi⟩
      · have hdeg : T.charpoly.natDegree = Module.finrank F A := LinearMap.charpoly_natDegree T
        rcases eq_or_lt_of_le (le_of_not_gt hi) with heq | hlt
        · rw [← heq, ← hdeg, (LinearMap.charpoly_monic T).coeff_natDegree, norm_one]
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.symm ▸ hlt), norm_zero]
          exact zero_le_one
    obtain ⟨b, hb⟩ := LinearAlgebra.integralEndomorphismBasis (O := O) T hcoeff
    have hb' := coordinateEnd_norm_le F A b T (r := 1) zero_le_one (fun i k => (hTest _).1 (hb i k))
    refine ⟨b, ?_⟩
    change j b x ∈ closedBall 0 r
    rw [mem_closedBall, dist_zero_right]
    have hEq : j b x = a • (e b) T := by
      change j b x = a • j b (a⁻¹ • x)
      rw [map_smul, smul_smul, mul_inv_cancel₀ ha₀, one_smul]
    rw [hEq, norm_smul]
    simpa only [r, mul_one] using
      mul_le_mul_of_nonneg_left (show ‖(e b) T‖ ≤ 1 from hb') (norm_nonneg a)
  have hLocal (b : Basis I F A) : IsOpenEmbedding (fun x : U b => f x) := by
    let S := (j b).range
    have hS : IsClosed (S : Set M) := (hj b).isClosed_range
    obtain ⟨eSmall, heSmall⟩ := hCharts S hS
    have hJ : IsEmbedding (fun x : U b => j b x) := (hj b).isEmbedding.comp IsEmbedding.subtypeVal
    have hRange : range (fun x : U b => j b x) = B ∩ (S : Set M) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x.property, ⟨x.val, rfl⟩⟩
      · rintro ⟨hy, x, rfl⟩
        exact ⟨⟨x, hy⟩, rfl⟩
    let J := hJ.toHomeomorph.trans (Homeomorph.setCongr hRange)
    let E := (J.trans eSmall.toHomeomorph).trans J.symm
    have hEval (x : U b) : j b (J.symm (eSmall (J x))) = (eSmall (J x) : M) := by
      change (J (J.symm (eSmall (J x))) : M) = _
      rw [J.apply_symm_apply]
    have hfun : (fun x : U b => f x) = Subtype.val ∘ E := by
      funext x
      apply (hj b).injective
      change j b (f x) = j b (J.symm (eSmall (J x)))
      rw [hf, hEval, heSmall]
      rfl
    rw [hfun]
    exact (hU b).isOpenEmbedding_subtypeVal.comp E.isOpenEmbedding
  have hCcont : ContinuousOn f C := by
    apply continuousOn_of_locally_continuousOn
    intro x hx
    obtain ⟨b, hb⟩ := hCover x hx
    exact ⟨U b, hU b, hb,
      (continuousOn_iff_continuous_domRestrict.mpr (hLocal b).continuous).mono inter_subset_right⟩
  let b₀ : Basis I F A := Module.finBasis F A
  have hSat (x : A) (hx : x ∈ C) : ∃ g : M ≃ₐ[F] M,
      ∃ y ∈ eball 0 (NormedSpace.expSeries F M).radius, g y = j b₀ x := by
    obtain ⟨b, hb⟩ := hCover x hx
    refine ⟨(e b).symm.trans (e b₀), j b x, hConv hb, ?_⟩
    change (e b₀) ((e b).symm ((e b) (Algebra.lmul F A x))) = _
    rw [(e b).symm_apply_apply]
    rfl
  have hinj : Injective (fun x : C => f x) := by
    intro x y hxy
    apply Subtype.ext
    apply (hj b₀).injective
    apply exponentialConjugacy (F := F) (A := M) (hSat x x.property) (hSat y y.property)
    have h := congrArg (j b₀) hxy
    rw [hf, hf] at h
    have h' := congrArg (fun z : M => z + 1) h
    simpa only [sub_add_cancel] using h'
  have hOpen : IsOpenMap (fun x : C => f x) := by
    intro Z hZ
    let W := (Subtype.val : C → A) '' Z
    have hW : IsOpen W := hC.2.isOpenMap_subtype_val _ hZ
    have hEq : (fun x : C => f x) '' Z =
        ⋃ b : Basis I F A, (fun x : U b => f x) '' ((Subtype.val : U b → A) ⁻¹' W) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨b, hb⟩ := hCover x x.property
        exact mem_iUnion.mpr ⟨b, ⟨⟨x, hb⟩, ⟨x, hx, rfl⟩, rfl⟩⟩
      · intro hy
        obtain ⟨b, z, ⟨x, hx, hzx⟩, rfl⟩ := mem_iUnion.mp hy
        exact ⟨x, hx, congrArg f hzx⟩
    rw [hEq]
    exact isOpen_iUnion fun b => (hLocal b).isOpenMap _ (hW.preimage continuous_subtype_val)
  exact ⟨C, hC, hC₀, hInv, IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuousOn_iff_continuous_domRestrict.mp hCcont) hinj hOpen⟩

end Langlands.HarmonicAnalysis.UnitConjugation
