import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedness
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Degree.Support

/-! # Uniform bounds for integral evaluations and finite affine morphisms -/

noncomputable section

universe u v w z

open CategoryTheory ValuativeRel Polynomial
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

section Evaluations

variable {F : Type u} [Field F] [ValuativeRel F]
  {A : Type v} [CommRing A] {B : Type w} [CommRing B] {ι : Type z}

private theorem monic_root_vle
    (p : Polynomial A) (hp : p.Monic) (f : A →+* F)
    {x c : F} (hc : 1 ≤ᵥ c)
    (hcoeff : ∀ i ∈ p.support, f (p.coeff i) ≤ᵥ c)
    (hx : p.eval₂ f x = 0) : x ≤ᵥ c := by
  classical
  let : Nontrivial A := f.domain_nontrivial
  by_contra hxc
  have hcx : c <ᵥ x := hxc
  have hx0 : x ≠ 0 := ((zero_vle c).trans_vlt hcx).ne_zero
  have h1x : 1 ≤ᵥ x := hc.trans hcx.vle
  let v := ValuativeRel.valuation F
  have hlead : f (p.coeff p.natDegree) * x ^ p.natDegree = x ^ p.natDegree := by
    simp [coeff_natDegree, hp.leadingCoeff]
  have hdom : ∀ i ∈ p.support \ {p.natDegree},
      v (f (p.coeff i) * x ^ i) <
        v (f (p.coeff p.natDegree) * x ^ p.natDegree) := by
    intro i hi
    obtain ⟨his, hin⟩ := Finset.mem_sdiff.mp hi
    have hil : i < p.natDegree :=
      lt_of_le_of_ne (le_natDegree_of_mem_supp i his) (by simpa using hin)
    have hterm : f (p.coeff i) * x ^ i <ᵥ x ^ (i + 1) := by
      simpa only [pow_succ'] using
        mul_vlt_mul_left (zero_vlt_iff.mpr (pow_ne_zero _ hx0))
          ((hcoeff i his).trans_vlt hcx)
    have hpow : x ^ (i + 1) ≤ᵥ x ^ p.natDegree :=
      pow_vle_pow_of_one_vle h1x (Nat.succ_le_of_lt hil)
    rw [hlead]
    exact v.vlt_iff_lt.mp (hterm.trans_vle hpow)
  have hsum := v.map_sum_eq_of_lt
    (natDegree_mem_support_of_nonzero hp.ne_zero) hdom
  have heval : v (p.eval₂ f x) = v (x ^ p.natDegree) := by
    simpa only [eval₂_eq_sum, Polynomial.sum, hlead] using hsum
  rw [hx, map_zero] at heval
  exact (v.ne_zero_iff.mpr (pow_ne_zero _ hx0)) heval.symm

omit [CommRing A] in
private theorem finite_uniform_bound
    (e : ι → A → F) (s : Finset A)
    (h : ∀ a ∈ s, ∃ b : F, b ≠ 0 ∧ ∀ i, e i a ≤ᵥ b) :
    ∃ c : F, c ≠ 0 ∧ 1 ≤ᵥ c ∧ ∀ a ∈ s, ∀ i, e i a ≤ᵥ c := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, vle_rfl, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨c, hc, h1c, hcs⟩ := ih (fun b hb => h b (Finset.mem_insert_of_mem hb))
    obtain ⟨b, hb, hba⟩ := h a (Finset.mem_insert_self _ _)
    rcases vle_total b c with hbc | hcb
    · refine ⟨c, hc, h1c, ?_⟩
      intro a' ha' i
      rcases Finset.mem_insert.mp ha' with rfl | ha'
      · exact (hba i).trans hbc
      · exact hcs a' ha' i
    · refine ⟨b, hb, h1c.trans hcb, ?_⟩
      intro a' ha' i
      rcases Finset.mem_insert.mp ha' with rfl | ha'
      · exact hba i
      · exact (hcs a' ha' i).trans hcb

private theorem exists_integral_evaluation_bound
    (f : A →+* B) (e : ι → B →+* F)
    (h : ∀ a : A, ∃ c : F, c ≠ 0 ∧ ∀ i, e i (f a) ≤ᵥ c)
    (b : B) (hb : f.IsIntegralElem b) :
    ∃ c : F, c ≠ 0 ∧ ∀ i, e i b ≤ᵥ c := by
  classical
  obtain ⟨p, hp, hpb⟩ := hb
  obtain ⟨c, hc, h1c, hcs⟩ := finite_uniform_bound
    (fun i a => e i (f a)) (p.support.image p.coeff) (fun a _ => h a)
  refine ⟨c, hc, fun i => monic_root_vle p hp ((e i).comp f) h1c ?_ ?_⟩
  · intro j hj
    exact hcs _ (Finset.mem_image_of_mem _ hj) i
  · rw [← Polynomial.hom_eval₂, hpb, map_zero]

/-- A nonzero uniform bound for evaluations of an element integral over an
algebra whose evaluations are bounded separately on each element. -/
def integralEvaluationBound
    (f : A →+* B) (e : ι → B →+* F)
    (h : ∀ a : A, ∃ c : F, c ≠ 0 ∧ ∀ i, e i (f a) ≤ᵥ c)
    (b : B) (hb : f.IsIntegralElem b) :
    {c : F // c ≠ 0 ∧ ∀ i, e i b ≤ᵥ c} :=
  ⟨Classical.choose (exists_integral_evaluation_bound f e h b hb),
    Classical.choose_spec (exists_integral_evaluation_bound f e h b hb)⟩

/-- Integral coordinate maps reflect uniform boundedness of evaluation families. -/
theorem bounded_evaluations_of_integral
    (f : A →+* B) (hf : f.IsIntegral) (e : ι → B →+* F)
    (h : ∀ a : A, ∃ c : F, c ≠ 0 ∧ ∀ i, e i (f a) ≤ᵥ c)
    (b : B) : ∃ c : F, c ≠ 0 ∧ ∀ i, e i b ≤ᵥ c :=
  ⟨(integralEvaluationBound f e h b (hf b)).val,
    (integralEvaluationBound f e h b (hf b)).property⟩

end Evaluations

section Schemes

variable (F : Type u) [Field F] [ValuativeRel F]
  {X Y : Over (Spec (CommRingCat.of F))} [IsAffine X.left] [IsAffine Y.left]

omit [ValuativeRel F] in
private theorem evaluation_pullback (f : X ⟶ Y) (p : RationalPoint F X)
    (a : AffineCoordinateRing F Y) :
    rationalPointAlgebraHom F X p (affineCoordinatePullback F f a) =
      rationalPointAlgebraHom F Y (p ≫ f) a := by
  unfold rationalPointAlgebraHom
  rw [rationalPointEquiv_natural, affineSchemePointEquiv_natural]
  rfl

/-- Integral morphisms of affine schemes reflect regular-function boundedness
from the image of any set of actual rational points. -/
theorem isAlgebraicallyBounded_of_integralHom
    (f : X ⟶ Y) [IsIntegralHom f.left]
    (S : Set (RationalPoint F X))
    (hS : IsAlgebraicallyBounded F Y ((fun p => p ≫ f) '' S)) :
    IsAlgebraicallyBounded F X S := by
  let e : S → AffineCoordinateRing F X →+* F :=
    fun p => (rationalPointAlgebraHom F X p.val).toRingHom
  have hf : (affineCoordinatePullback F f).toRingHom.IsIntegral :=
    f.left.isIntegral_app ⊤ (isAffineOpen_top Y.left)
  have h : ∀ a : AffineCoordinateRing F Y, ∃ c : F,
      c ≠ 0 ∧ ∀ i, e i (affineCoordinatePullback F f a) ≤ᵥ c := by
    intro a
    obtain ⟨c, hc, hca⟩ := hS a
    refine ⟨c, hc, fun p => ?_⟩
    change rationalPointAlgebraHom F X p.val (affineCoordinatePullback F f a) ≤ᵥ c
    rw [evaluation_pullback]
    exact hca _ ⟨p.val, p.property, rfl⟩
  intro a
  obtain ⟨c, hc, hca⟩ :=
    bounded_evaluations_of_integral (affineCoordinatePullback F f).toRingHom hf e h a
  exact ⟨c, hc, fun p hp => hca ⟨p, hp⟩⟩

/-- The inverse image of a bounded set under an integral affine morphism is bounded. -/
theorem isAlgebraicallyBounded_preimage_of_integralHom
    (f : X ⟶ Y) [IsIntegralHom f.left]
    (S : Set (RationalPoint F Y)) (hS : IsAlgebraicallyBounded F Y S) :
    IsAlgebraicallyBounded F X ((fun p => p ≫ f) ⁻¹' S) := by
  apply isAlgebraicallyBounded_of_integralHom F f
  intro a
  obtain ⟨c, hc, hca⟩ := hS a
  refine ⟨c, hc, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact hca _ hp

/-- KP Lemma 2.2.10 for actual affine schemes over any valuative field. -/
theorem isAlgebraicallyBounded_preimage_of_finite
    (f : X ⟶ Y) [IsFinite f.left]
    (S : Set (RationalPoint F Y)) (hS : IsAlgebraicallyBounded F Y S) :
    IsAlgebraicallyBounded F X ((fun p => p ≫ f) ⁻¹' S) :=
  isAlgebraicallyBounded_preimage_of_integralHom F f S hS

end Schemes

end Langlands.AlgebraicGeometry.PointTopology
