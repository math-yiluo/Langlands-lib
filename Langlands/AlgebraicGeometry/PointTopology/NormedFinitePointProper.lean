import Langlands.AlgebraicGeometry.PointTopology.AffineProofs
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.MetricSpace.ProperSpace

/-! # Finite maps on affine points over a proper normed field -/

open Topology

namespace Langlands.AlgebraicGeometry.PointTopology

/-- A root of a monic specialization is bounded by one plus the sum of the
norms of its specialized lower coefficients. -/
theorem norm_root_le_one_add_sum {A L : Type*} [CommRing A] [NormedField L]
    (P : Polynomial A) (hP : P.Monic) (e : A →+* L) {x : L}
    (hx : P.eval₂ e x = 0) :
    ‖x‖ ≤ 1 + ∑ i ∈ Finset.range P.natDegree, ‖e (P.coeff i)‖ := by
  have hmonic := hP.map e
  have hroot : (P.map e).IsRoot x := by
    simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using hx
  have hbound := hroot.norm_lt_cauchyBound hmonic.ne_zero
  have hsum : (Finset.range P.natDegree).sup (fun i => ‖e (P.coeff i)‖₊) ≤
      ∑ i ∈ Finset.range P.natDegree, ‖e (P.coeff i)‖₊ := by
    exact Finset.sup_le fun i hi =>
      Finset.single_le_sum (f := fun j => ‖e (P.coeff j)‖₊) (fun _ _ => zero_le) hi
  rw [Polynomial.cauchyBound, hP.natDegree_map e, hmonic.leadingCoeff] at hbound
  simp only [nnnorm_one, div_one, Polynomial.coeff_map] at hbound
  have hle := hbound.le.trans (add_le_add_left hsum 1)
  have hreal := NNReal.coe_le_coe.mpr hle
  simpa [add_comm] using hreal

namespace AlgPoint

variable {R A B L : Type*} [CommRing R] [CommRing A] [CommRing B] [NormedField L]
  [Algebra R A] [Algebra R B] [Algebra R L] [Algebra A B] [IsScalarTower R A B]

/-- Evaluation of an integral element is bounded above over a compact set of base points. -/
theorem exists_norm_le_preimage_of_isIntegral {K : Set (AlgPoint R A L)} (hK : IsCompact K)
    {b : B} (hb : IsIntegral A b) :
    ∃ C : ℝ, ∀ q ∈ precomp (S := L) (IsScalarTower.toAlgHom R A B) ⁻¹' K, ‖q b‖ ≤ C := by
  obtain ⟨P, hm, hP⟩ := hb
  let F (p : AlgPoint R A L) : ℝ :=
    1 + ∑ i ∈ Finset.range P.natDegree, ‖p (P.coeff i)‖
  have hF : Continuous F := continuous_const.add <|
    continuous_finsetSum _ fun i _ => (continuous_eval (P.coeff i)).norm
  obtain ⟨C, hC⟩ := (hK.image hF).isBounded.exists_norm_le
  refine ⟨C, fun q hq => ?_⟩
  let p := precomp (S := L) (IsScalarTower.toAlgHom R A B) q
  have hroot : P.eval₂ p.toAlgHom.toRingHom (q b) = 0 := by
    change Polynomial.aeval b P = 0 at hP
    rw [Polynomial.aeval_def] at hP
    let e := q.toAlgHom.toRingHom
    change P.eval₂ (e.comp (algebraMap A B)) (e b) = 0
    simpa only [Polynomial.hom_eval₂, map_zero] using
      congrArg q.toAlgHom.toRingHom hP
  exact (norm_root_le_one_add_sum P hm p.toAlgHom.toRingHom hroot).trans <|
    (le_abs_self (F p)).trans (hC _ ⟨p, hq, rfl⟩)

/-- A finite map of affine finite-type algebras induces a proper map of points
with values in a proper normed field. -/
theorem isProperMap_precomp_of_moduleFinite [ProperSpace L] [Algebra.FiniteType R A]
    [Module.Finite A B] :
    IsProperMap (precomp (S := L) (IsScalarTower.toAlgHom R A B)) := by
  let : LocallyCompactSpace (AlgPoint R A L) :=
    affineLocalCompactness_proof R A L inferInstance
  let : Algebra.FiniteType R B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  let f := IsScalarTower.toAlgHom R A B
  refine isProperMap_iff_isCompact_preimage.mpr ⟨continuous_precomp f, fun {K} hK => ?_⟩
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R B)
  let e := AlgPoint.polynomialPointHomeomorph (R := R) (S := L) (Fin n)
  have he : IsClosedEmbedding (e ∘ precomp g) :=
    e.isClosedEmbedding.comp (isClosedEmbedding_precomp_of_surjective g hg)
  choose C hC using fun i : Fin n => exists_norm_le_preimage_of_isIntegral hK
    (Algebra.IsIntegral.isIntegral (R := A) (g (MvPolynomial.X i)))
  let box : Set (Fin n → L) := Set.pi Set.univ (fun i => Metric.closedBall 0 (C i))
  have hbox : IsCompact box := isCompact_univ_pi fun i => isCompact_closedBall 0 (C i)
  refine (he.isCompact_preimage hbox).of_isClosed_subset
    (hK.isClosed.preimage (continuous_precomp f)) ?_
  intro q hq i _
  change q (g (MvPolynomial.X i)) ∈ Metric.closedBall 0 (C i)
  exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hC i q hq)

end AlgPoint

end Langlands.AlgebraicGeometry.PointTopology
