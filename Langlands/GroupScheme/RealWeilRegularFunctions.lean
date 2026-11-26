import Langlands.AlgebraicGeometry.PointTopology.LiftedRealOpenZariskiDensity
import Langlands.GroupScheme.AffineWeilRestrictionForwardTopology
import Langlands.GroupScheme.Reductive.AffineWeilConnectedReductive
import Langlands.GroupScheme.Rational.ConnectedGroupUnirationalityReduction
import Langlands.GroupScheme.Torus.TorusUnirationalityProof
import Mathlib.Analysis.RCLike.Lemmas

/-! # Real regular functions on archimedean coefficient points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open Langlands.Algebra Langlands.AlgebraicGeometry.PointTopology

private local instance {K : Type u} [Field K] [TopologicalSpace K]
    (H : GroupScheme (Spec (CommRingCat.of K))) :
    TopologicalSpace (H.affinePoints (CommAlgCat.of K K)) :=
  H.affinePointsTopologicalSpace (CommAlgCat.of K K)

/-- The real regular functions on a finite archimedean coefficient group contain every real-linear
component of evaluation. Equality of such functions propagates from a neighbourhood of the
identity by density on the real Weil restriction. -/
theorem exists_realRegularFunctions (K : Type u) [RCLike K]
    (H : GroupScheme (Spec (CommRingCat.of K))) [IsAffine H.X.left] (hH : IsConnectedReductive H) :
    ∃ S : Subalgebra ℝ (H.affinePoints (CommAlgCat.of K K) → ℝ),
      (∀ (a : Γ(H.X.left, ⊤)) (l : K →ₗ[ℝ] ℝ),
        (fun p => l (H.affinePointEvaluation (CommAlgCat.of K K) p a)) ∈ S) ∧
      ∀ f ∈ S, (∀ᶠ p in nhds (1 : H.affinePoints (CommAlgCat.of K K)), f p = 0) → ∀ p, f p = 0 := by
  let R := ULift.{u} ℝ
  let : Algebra R K := {
    algebraMap := (algebraMap ℝ K).comp (ULift.ringEquiv : R ≃+* ℝ).toRingHom
    smul := fun r x => r.down • x
    commutes' := fun _ _ => mul_comm _ _
    smul_def' := fun r x => by
      change r.down • x = algebraMap ℝ K r.down * x
      exact Algebra.smul_def r.down x }
  let : IsScalarTower ℝ R K := by
    constructor
    intro x y z
    change (x * y.down) • z = x • (y.down • z)
    exact mul_smul _ _ _
  let : Module.Finite R K := Module.Finite.of_restrictScalars_finite ℝ R K
  let : CharZero R := ⟨fun _ _ h => (Nat.cast_injective (R := ℝ)) (congrArg ULift.down h)⟩
  let : Algebra.IsSeparable R K := Algebra.IsSeparable.of_integral R K
  let : ContinuousSMul R K := ⟨by
    change Continuous (fun p : R × K => p.1.down • p.2)
    exact (continuous_uliftDown.comp continuous_fst).smul continuous_snd⟩
  let : Smooth H.X.hom := hH.smooth
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let W := AffineWeil.groupScheme R K H
  let : IsAffine W.X.left := inferInstanceAs (IsAffine (affineWeilRestriction R K H.X).left)
  let C := WeilRestrictionFiniteType R K (AffineCoordinateRing K H.X)
  let P := W.affinePoints (CommAlgCat.of R R)
  let Q := H.affinePoints (CommAlgCat.of K K)
  let e : P ≃* Q := AffineWeil.basePointsEquiv R K H
  let ev (q : P) : C →ₐ[R] R := affineRingPointEquiv R C R q
  let S : Subalgebra ℝ (Q → ℝ) := {
    carrier := {f | ∃ a : C, ∀ q : P, f (e q) = (ev q a).down}
    zero_mem' := ⟨0, fun q => by change 0 = (ev q 0).down; rw [map_zero]; rfl⟩
    one_mem' := ⟨1, fun q => by change 1 = (ev q 1).down; rw [map_one]; rfl⟩
    add_mem' := by
      rintro f g ⟨a, ha⟩ ⟨b, hb⟩
      refine ⟨a + b, fun q => ?_⟩
      change f (e q) + g (e q) = (ev q (a + b)).down
      rw [ha, hb, map_add]
      rfl
    mul_mem' := by
      rintro f g ⟨a, ha⟩ ⟨b, hb⟩
      refine ⟨a * b, fun q => ?_⟩
      change f (e q) * g (e q) = (ev q (a * b)).down
      rw [ha, hb, map_mul]
      rfl
    algebraMap_mem' := by
      intro s
      exact ⟨algebraMap R C (ULift.up s), fun q => by
        change s = (ev q (algebraMap R C (ULift.up s))).down
        rw [AlgHom.commutes, Algebra.algebraMap_self_apply]⟩ }
  refine ⟨S, ?_, ?_⟩
  · intro a l
    have h (t : K ⊗[R] C) : ∃ s : C, ∀ q,
        l (Algebra.TensorProduct.rid R K K (Algebra.TensorProduct.lTensor (S := K) K (ev q) t)) =
          (ev q s).down := by
      induction t with
      | tmul b c =>
        refine ⟨algebraMap R C (ULift.up (l b)) * c, fun q => ?_⟩
        change l (((ev q c).down : ℝ) • b) =
          (ev q (algebraMap R C (ULift.up (l b)) * c)).down
        rw [map_smul, map_mul, AlgHom.commutes, Algebra.algebraMap_self_apply]
        exact mul_comm _ _
      | add x y hx hy =>
        obtain ⟨s, hs⟩ := hx
        obtain ⟨t, ht⟩ := hy
        refine ⟨s + t, fun q => ?_⟩
        simp only [map_add, hs, ht]
        rfl
    obtain ⟨s, hs⟩ := h (WeilRestrictionFiniteType.universalPoint R K
      (AffineCoordinateRing K H.X) a)
    refine ⟨s, fun q => ?_⟩
    change l (H.affinePointEvaluation (CommAlgCat.of K K) (e q) a) = (ev q s).down
    rw [← H.affineSchemePointEquiv_evaluation (CommAlgCat.of K K) (e q) a]
    exact (congrArg l (DFunLike.congr_fun (AffineWeil.basePointsEquiv_coordinates R K H q) a)).trans (hs q)
  · intro f hf hzero p
    obtain ⟨a, ha⟩ := hf
    have hcont : Continuous e := AffineWeil.continuous_basePointsEquiv_of_continuousSMul R K H
    let e' := (W.affinePointsRingPointHomeomorph (CommAlgCat.of R R)).symm
    have hzero' : ∀ᶠ q in nhds (e'.symm 1), f (e (e' q)) = 0 := by
      have he : Continuous (fun q => e (e' q)) := hcont.comp e'.continuous
      have ht := he.continuousAt (x := e'.symm 1).tendsto
      simp only [e'.apply_symm_apply, map_one] at ht
      exact ht.eventually hzero
    obtain ⟨U, hU, ho, h1⟩ := mem_nhds_iff.mp hzero'
    have hW : IsConnectedReductive W := AffineWeil.isConnectedReductive_restriction R K H hH
    have huni := ConnectedUnirationality.infinite_reductive_isUnirational torusUnirationality W hW
    have hd := liftedRealOpenZariskiDensity.{u} W huni U ho ⟨_, h1⟩
    have hnil : IsNilpotent a := by
      apply (PrimeSpectrum.basicOpen_eq_bot_iff a).mp
      by_contra hn
      have hn' : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum C)).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr fun h => hn (SetLike.coe_injective h)
      obtain ⟨x, hx, q, hq, rfl⟩ := hd.inter_open_nonempty _ PrimeSpectrum.isOpen_basicOpen hn'
      have hq0 : ev (e' q) a = 0 := by
        apply ULift.down_injective
        exact (ha (e' q)).symm.trans (hU hq)
      have hqSpec : q.left = Spec.map (CommRingCat.ofHom (ev (e' q)).toRingHom) := by
        have heq : (e' q : RingPoint R W.X R) = q :=
          W.affinePointsRingPointHomeomorph_symm_apply (CommAlgCat.of R R) q
        have hleft : (e' q).left = q.left := congrArg (fun p : RingPoint R W.X R => p.left) heq
        exact hleft.symm.trans (Spec.map_preimage (e' q).left).symm
      change q.left (IsLocalRing.closedPoint R) ∈ PrimeSpectrum.basicOpen a at hx
      rw [hqSpec] at hx
      change ev (e' q) a ∉ IsLocalRing.maximalIdeal R at hx
      exact hx (hq0 ▸ Ideal.zero_mem _)
    rw [← e.apply_symm_apply p, ha]
    rw [(hnil.map (ev (e.symm p))).eq_zero]
    rfl

end Langlands.GroupScheme
