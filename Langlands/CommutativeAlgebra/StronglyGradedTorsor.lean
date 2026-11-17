import Langlands.CommutativeAlgebra.StronglyGraded
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Faithful flatness and the tensor comparison of a strongly graded ring -/

noncomputable section

universe u v

open scoped TensorProduct

namespace Langlands.CommutativeAlgebra.StronglyGraded

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M]
variable {c : A →+* AddMonoidAlgebra A M} (hc : IsGrading c)

/-- The degree-zero coefficient, valued in the degree-zero subring. -/
def zeroProjection : A →ₗ[degreeZero (c := c)] degreeZero (c := c) :=
  (projection (c := c) 0).codRestrict _ (fun a => projection_mem hc 0 a)

@[simp] theorem zeroProjection_coe (r : degreeZero (c := c)) :
    zeroProjection hc (r : A) = r := by
  apply Subtype.ext
  change (c (r : A)).coeff 0 = r
  rw [r.property]
  simp

include hc in
/-- A strong grading is faithfully flat over degree zero. -/
theorem faithfullyFlat (hs : IsStrong (c := c)) :
    Module.FaithfullyFlat (degreeZero (c := c)) A := by
  let := projective hc hs
  apply (Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top _ _).2
  refine ⟨inferInstance, fun I hI => ?_⟩
  have hp : Function.Surjective (zeroProjection hc) :=
    fun r => ⟨(r : A), zeroProjection_coe hc r⟩
  have h := congrArg (Submodule.map (zeroProjection hc)) hI
  rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hp] at h
  simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using h

/-- The coaction as a map of degree-zero algebras. -/
def coactionAlgHom : A →ₐ[degreeZero (c := c)] AddMonoidAlgebra A M where
  __ := c
  commutes' r := r.property

/-- The canonical torsor comparison, `a ⊗ b ↦ a c(b)`. -/
def canonical : A ⊗[degreeZero (c := c)] A →ₐ[A] AddMonoidAlgebra A M :=
  Algebra.TensorProduct.lift AddMonoidAlgebra.singleZeroAlgHom
    (coactionAlgHom (c := c)) (fun _ _ => Commute.all _ _)

@[simp] theorem canonical_tmul (a b : A) :
    canonical (c := c) (a ⊗ₜ[degreeZero (c := c)] b) =
      AddMonoidAlgebra.single 0 a * c b := rfl

/-- On a homogeneous second factor, the comparison is a single monomial. -/
theorem canonical_tmul_homogeneous {m : M} {b : A}
    (hb : b ∈ component (c := c) m) (a : A) :
    canonical (c := c) (a ⊗ₜ[degreeZero (c := c)] b) =
      AddMonoidAlgebra.single m (a * b) := by
  rw [canonical_tmul, hb, AddMonoidAlgebra.single_mul_single, zero_add]

include hc in
/-- The canonical comparison is bijective for a strongly graded ring. -/
theorem canonical_bijective (hs : IsStrong (c := c)) :
    Function.Bijective (canonical (c := c)) := by
  classical
  choose ns xs ys hx hy hsum using hs
  let t : M → A ⊗[degreeZero (c := c)] A :=
    fun m => ∑ i, ys m i ⊗ₜ[degreeZero (c := c)] xs m i
  have ht (m : M) : canonical (c := c) (t m) = AddMonoidAlgebra.single m 1 := by
    simp only [t, map_sum, canonical_tmul_homogeneous (hx _ _)]
    change (∑ i, (AddMonoidAlgebra.singleAddHom m) (ys m i * xs m i)) = _
    rw [← map_sum]
    have hm : (∑ i, ys m i * xs m i) = 1 := by
      simpa only [mul_comm] using hsum m
    rw [hm]
    rfl
  have htb (m : M) (b : A) (hb : b ∈ component (c := c) m) :
      b • t m = (1 : A) ⊗ₜ[degreeZero (c := c)] b := by
    simp only [t, Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul]
    have hbal (i : Fin (ns m)) :
        (b * ys m i) ⊗ₜ[degreeZero (c := c)] xs m i =
          (1 : A) ⊗ₜ[degreeZero (c := c)] ((b * ys m i) * xs m i) := by
      let r : degreeZero (c := c) := ⟨b * ys m i, by
        change c (b * ys m i) = AddMonoidAlgebra.single 0 (b * ys m i)
        simpa only [mem_component, add_neg_cancel] using mul_mem_component hb (hy m i)⟩
      simpa only [Algebra.smul_def, algebraMap_degreeZero, mul_one] using
        (TensorProduct.smul_tmul (R := degreeZero (c := c)) r (1 : A) (xs m i))
    simp_rw [hbal]
    rw [← TensorProduct.tmul_sum]
    congr 1
    calc
      (∑ i, b * ys m i * xs m i) = b * ∑ i, xs m i * ys m i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = b := by rw [hsum, mul_one]
  let inv : AddMonoidAlgebra A M →ₗ[A] A ⊗[degreeZero (c := c)] A :=
    (Finsupp.linearCombination A t).comp (AddMonoidAlgebra.coeffLinearEquiv A).toLinearMap
  have hinv (m : M) (a : A) : inv (AddMonoidAlgebra.single m a) = a • t m := by
    exact Finsupp.linearCombination_single A (v := t) a m
  have hleft (x : A ⊗[degreeZero (c := c)] A) : inv (canonical (c := c) x) = x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      rw [← sum_projection hc b]
      simp only [TensorProduct.tmul_sum, map_sum]
      apply Finset.sum_congr rfl
      intro m _
      rw [canonical_tmul_homogeneous (projection_mem hc m b), hinv, mul_smul,
        htb m _ (projection_mem hc m b)]
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hright (x : AddMonoidAlgebra A M) : canonical (c := c) (inv x) = x := by
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | single m a =>
      rw [hinv, map_smul, ht]
      simp
  exact ⟨Function.LeftInverse.injective hleft, Function.RightInverse.surjective hright⟩

/-- The canonical algebra isomorphism of a strong grading. -/
def canonicalIso (hs : IsStrong (c := c)) :
    A ⊗[degreeZero (c := c)] A ≃ₐ[A] AddMonoidAlgebra A M :=
  AlgEquiv.ofBijective (canonical (c := c)) (canonical_bijective hc hs)

end Langlands.CommutativeAlgebra.StronglyGraded
