import Langlands.Geometry.Analytic.StrictTestDomain.Definitions
import Langlands.Geometry.Analytic.TatePresentation
import Langlands.Geometry.Analytic.BoundedQuotient

/-! # Testing a strict-test representation on pairs of maps -/

noncomputable section

universe u v

namespace Langlands.Analytic

namespace StrictTateAlgebra

/-- Over a finite index type, a monomial value is the finite product of powers. -/
theorem monomialValue_fintype {σ : Type*} [Fintype σ] {B : Type*} [NormedCommRing B]
    (b : σ → B) (d : σ →₀ ℕ) : monomialValue σ B b d = ∏ i, b i ^ d i :=
  Finsupp.prod_fintype _ _ fun _ => pow_zero _

/-- A tuple of elements of norm at most one has bounded monomials. -/
theorem hasBoundedMonomials_of_norm_le_one {σ : Type*} {B : Type*} [NormedCommRing B]
    (b : σ → B) (hb : ∀ i, ‖b i‖ ≤ 1) : HasBoundedMonomials σ B b := by
  classical
  refine ⟨max 1 ‖(1 : B)‖, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun d => ?_⟩
  unfold monomialValue Finsupp.prod
  rcases d.support.eq_empty_or_nonempty with h | h
  · rw [h, Finset.prod_empty]
    exact le_max_right _ _
  · refine (Finset.norm_prod_le' _ h _).trans ?_
    refine (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i hi => ?_).trans
      (le_max_left _ _)
    exact (norm_pow_le' _ (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))).trans
      (pow_le_one₀ (norm_nonneg _) (hb i))

/-- Concatenating two tuples with bounded monomials gives a tuple with bounded
monomials. -/
theorem hasBoundedMonomials_append {m n : ℕ} {B : Type*} [NormedCommRing B]
    (b : Fin m → B) (b' : Fin n → B) (hb : HasBoundedMonomials (Fin m) B b)
    (hb' : HasBoundedMonomials (Fin n) B b') :
    HasBoundedMonomials (Fin (m + n)) B (Fin.append b b') := by
  obtain ⟨C, hC, hbC⟩ := hb
  obtain ⟨C', hC', hbC'⟩ := hb'
  refine ⟨C * C', mul_pos hC hC', fun d => ?_⟩
  have h := hbC (Finsupp.equivFunOnFinite.symm fun i => d (Fin.castAdd n i))
  have h' := hbC' (Finsupp.equivFunOnFinite.symm fun j => d (Fin.natAdd m j))
  rw [monomialValue_fintype] at h h' ⊢
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  simp only [Finsupp.coe_equivFunOnFinite_symm] at h h'
  exact (norm_mul_le _ _).trans (mul_le_mul h h' (norm_nonneg _) hC.le)

end StrictTateAlgebra

namespace PresentedStrictAffinoidAlgebra

open StrictTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- Presentation coordinates have norm at most one. -/
theorem norm_coordinate_le_one (A : PresentedStrictAffinoidAlgebra K) (k : Fin A.arity) :
    ‖coordinate K A k‖ ≤ 1 := by
  calc ‖coordinate K A k‖ = ‖Ideal.Quotient.mk A.ideal (X (Fin A.arity) K k)‖ := rfl
    _ ≤ ‖X (Fin A.arity) K k‖ := Ideal.Quotient.norm_mk_le A.ideal _
    _ = 1 := by rw [X, norm_monomial, norm_one]

end PresentedStrictAffinoidAlgebra

namespace StrictTestDomain

open PresentedStrictAffinoidAlgebra StrictTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

namespace PairTest

variable (Q : PresentedStrictAffinoidAlgebra K) {W : Type v} [NormedCommRing W]
  [NormedAlgebra K W] [IsUltrametricDist W] [CompleteSpace W]
  (u v : BoundedAlgHom K Q W)

/-- The coordinates of `Q` under `u`, followed by those under `v`. -/
def tuple : Fin (Q.arity + Q.arity) → W :=
  Fin.append (fun k => u (coordinate K Q k)) (fun k => v (coordinate K Q k))

omit [IsUltrametricDist W] [CompleteSpace W] in
theorem hasBoundedMonomials_tuple :
    HasBoundedMonomials (Fin (Q.arity + Q.arity)) W (tuple Q u v) :=
  hasBoundedMonomials_append _ _
    (hasBoundedMonomials_map_X (Fin Q.arity) K W (u.comp (presentationMap K Q)))
    (hasBoundedMonomials_map_X (Fin Q.arity) K W (v.comp (presentationMap K Q)))

/-- Evaluation of Tate series in twice as many variables at the pair of
coordinate tuples. -/
def eval : BoundedAlgHom K (StrictTateAlgebra (Fin (Q.arity + Q.arity)) K) W :=
  evaluateHom (Fin (Q.arity + Q.arity)) K W (tuple Q u v) (hasBoundedMonomials_tuple Q u v)

/-- The presented strict affinoid algebra whose relations are the kernel of the
evaluation. It maps injectively onto the image of the evaluation in `W`. -/
def algebra : PresentedStrictAffinoidAlgebra K :=
  ofRelations K (Q.arity + Q.arity) {f | eval Q u v f = 0}

/-- The embedding of the test algebra into `W`. -/
def toTarget : BoundedAlgHom K (algebra Q u v) W :=
  liftRelations K (Q.arity + Q.arity) {f | eval Q u v f = 0} W (tuple Q u v)
    (hasBoundedMonomials_tuple Q u v) fun _ hf => hf

theorem toTarget_injective : Function.Injective (toTarget Q u v) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨f, rfl⟩ := presentationMap_surjective K (algebra Q u v) x
  exact presentationMap_relation K (Q.arity + Q.arity) {f | eval Q u v f = 0} hx

theorem toTarget_coordinate (j : Fin (Q.arity + Q.arity)) :
    toTarget Q u v (coordinate K (algebra Q u v) j) = tuple Q u v j :=
  liftRelations_coordinate K _ _ W _ _ _ j

variable [CompleteSpace K]

/-- Evaluation of Tate series in `Q.arity` variables at the coordinates of the
test algebra selected by `e`. -/
def lift (e : Fin Q.arity → Fin (Q.arity + Q.arity)) :
    BoundedAlgHom K (StrictTateAlgebra (Fin Q.arity) K) (algebra Q u v) :=
  evaluateHom (Fin Q.arity) K (algebra Q u v) (fun k => coordinate K (algebra Q u v) (e k))
    (hasBoundedMonomials_of_norm_le_one _ fun _ => norm_coordinate_le_one _ _)

theorem toTarget_comp_lift (e : Fin Q.arity → Fin (Q.arity + Q.arity))
    (t : BoundedAlgHom K Q W) (he : ∀ k, tuple Q u v (e k) = t (coordinate K Q k)) :
    (toTarget Q u v).comp (lift Q u v e) = t.comp (presentationMap K Q) := by
  apply StrictTateAlgebra.hom_ext
  intro k
  change toTarget Q u v (evaluate (Fin Q.arity) K (algebra Q u v)
      (fun k => coordinate K (algebra Q u v) (e k)) (X (Fin Q.arity) K k)) =
    t (coordinate K Q k)
  rw [evaluate_X, toTarget_coordinate]
  exact he k

/-- The map `Q → algebra Q u v` lifting `t` along the coordinates selected by `e`. -/
def inclusion (e : Fin Q.arity → Fin (Q.arity + Q.arity)) (t : BoundedAlgHom K Q W)
    (he : ∀ k, tuple Q u v (e k) = t (coordinate K Q k)) :
    BoundedAlgHom K Q (algebra Q u v) := by
  letI := Q.ideal_closed
  exact BoundedAlgHom.liftQuotient K Q.ideal (lift Q u v e) fun f hf =>
    toTarget_injective Q u v <| by
      have h := congrArg (fun χ : BoundedAlgHom K _ W => χ f) (toTarget_comp_lift Q u v e t he)
      change toTarget Q u v (lift Q u v e f) = t (presentationMap K Q f) at h
      have h0 : presentationMap K Q f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hf
      rw [h, h0, map_zero t.toAlgHom, map_zero (toTarget Q u v).toAlgHom]

theorem toTarget_comp_inclusion (e : Fin Q.arity → Fin (Q.arity + Q.arity))
    (t : BoundedAlgHom K Q W) (he : ∀ k, tuple Q u v (e k) = t (coordinate K Q k)) :
    (toTarget Q u v).comp (inclusion Q u v e t he) = t := by
  apply BoundedAlgHom.ext
  intro x
  obtain ⟨f, rfl⟩ := presentationMap_surjective K Q x
  exact congrArg (fun χ : BoundedAlgHom K _ W => χ f) (toTarget_comp_lift Q u v e t he)

/-- The first coordinate inclusion, lifting `u`. -/
def left : BoundedAlgHom K Q (algebra Q u v) :=
  inclusion Q u v (Fin.castAdd Q.arity) u fun k => Fin.append_left _ _ k

/-- The second coordinate inclusion, lifting `v`. -/
def right : BoundedAlgHom K Q (algebra Q u v) :=
  inclusion Q u v (Fin.natAdd Q.arity) v fun k => Fin.append_right _ _ k

theorem toTarget_comp_left : (toTarget Q u v).comp (left Q u v) = u :=
  toTarget_comp_inclusion Q u v _ u _

theorem toTarget_comp_right : (toTarget Q u v).comp (right Q u v) = v :=
  toTarget_comp_inclusion Q u v _ v _

end PairTest

variable [CompleteSpace K]

/-- A map representing a subset for strict tests is an epimorphism towards
complete ultrametric normed algebras: two bounded maps out of `Q` that agree on
the image of `P` are equal. The test algebra is presented by the kernel of the
joint evaluation at both coordinate tuples. -/
theorem eq_of_comp_eq {P Q : PresentedStrictAffinoidAlgebra K} {i : BoundedAlgHom K P Q}
    {U : Set (BanachSpectrum P)} (hU : Represents K i U) {W : Type v} [NormedCommRing W]
    [NormedAlgebra K W] [IsUltrametricDist W] [CompleteSpace W]
    (u v : BoundedAlgHom K Q W) (huv : u.comp i = v.comp i) : u = v := by
  have hlr : (PairTest.left Q u v).comp i = (PairTest.right Q u v).comp i := by
    apply BoundedAlgHom.ext
    intro a
    apply PairTest.toTarget_injective Q u v
    have hl := congrArg (fun χ : BoundedAlgHom K Q W => χ (i a)) (PairTest.toTarget_comp_left Q u v)
    have hr := congrArg (fun χ : BoundedAlgHom K Q W => χ (i a)) (PairTest.toTarget_comp_right Q u v)
    have ha := congrArg (fun χ : BoundedAlgHom K P W => χ a) huv
    change PairTest.toTarget Q u v (PairTest.left Q u v (i a)) = u (i a) at hl
    change PairTest.toTarget Q u v (PairTest.right Q u v (i a)) = v (i a) at hr
    change u (i a) = v (i a) at ha
    change PairTest.toTarget Q u v (PairTest.left Q u v (i a)) =
      PairTest.toTarget Q u v (PairTest.right Q u v (i a))
    rw [hl, hr, ha]
  have himage : HasImageIn K ((PairTest.left Q u v).comp i) U := by
    intro z
    rw [← hU.2.1]
    exact ⟨BanachSpectrum.comap (PairTest.left Q u v).toBoundedRingHom z, rfl⟩
  obtain ⟨ψ, -, huniq⟩ := hU.2.2 _ _ himage
  have hl : PairTest.left Q u v = ψ := huniq _ rfl
  have hr : PairTest.right Q u v = ψ := huniq _ hlr.symm
  calc u = (PairTest.toTarget Q u v).comp (PairTest.left Q u v) :=
        (PairTest.toTarget_comp_left Q u v).symm
    _ = (PairTest.toTarget Q u v).comp (PairTest.right Q u v) := by rw [hl, hr]
    _ = v := PairTest.toTarget_comp_right Q u v

end StrictTestDomain

end Langlands.Analytic
