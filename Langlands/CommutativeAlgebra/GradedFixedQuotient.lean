import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic

/-! # Formal smoothness of the fixed quotient of a group grading -/

noncomputable section

universe u v w

namespace Langlands.CommutativeAlgebra.GradedFixedQuotient

open AddMonoidAlgebra

variable {M : Type w} [AddCommGroup M]

/-- The degree-zero coefficient of a product, when all off-zero coefficients of both
factors lie in a square-zero ideal. -/
theorem coeff_mul_zero_of_off_mem {D : Type*} [CommRing D] {J : Ideal D}
    (hJ : ∀ a ∈ J, ∀ b ∈ J, a * b = 0)
    {q q' : AddMonoidAlgebra D M}
    (hq : ∀ m, m ≠ 0 → q.coeff m ∈ J)
    (hq' : ∀ m, m ≠ 0 → q'.coeff m ∈ J) :
    (q * q').coeff 0 = q.coeff 0 * q'.coeff 0 := by
  classical
  rw [AddMonoidAlgebra.coeff_mul]
  have key : ∀ m₁ m₂ : M,
      (if m₁ + m₂ = 0 then q.coeff m₁ * q'.coeff m₂ else 0) =
      if m₁ = 0 then (if m₂ = 0 then q.coeff m₁ * q'.coeff m₂ else 0) else 0 := by
    intro m₁ m₂
    by_cases h1 : m₁ = 0
    · simp [h1]
    · by_cases h : m₁ + m₂ = 0
      · have h2 : m₂ ≠ 0 := fun h2 => h1 (by simpa [h2] using h)
        rw [ite_eq_left h, ite_eq_right h1]
        exact hJ _ (hq _ h1) _ (hq' _ h2)
      · simp [h, h1]
  simp only [Finsupp.sum, key]
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro m _ hm
      simp [hm]
    · intro hm
      simp [Finsupp.notMem_support_iff.1 hm]
  · intro m _ hm
    simp [hm]
  · intro hm
    simp [Finsupp.notMem_support_iff.1 hm]

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

/-- The ideal defining the fixed quotient: all coefficients of `c b - b X⁰`. -/
def fixedIdeal (c : B →+* AddMonoidAlgebra B M) : Ideal B :=
  Ideal.span {d | ∃ b m, (c b - AddMonoidAlgebra.single 0 b).coeff m = d}

/-- An algebra-valued point kills the fixed ideal exactly when it is fixed by the
coaction, expressed in the group algebra over its target. -/
theorem fixedIdeal_le_ker_iff (c : B →+* AddMonoidAlgebra B M)
    {D : Type*} [CommRing D] (f : B →+* D) :
    fixedIdeal c ≤ RingHom.ker f ↔
      ∀ b, AddMonoidAlgebra.mapRingHom M f (c b) =
        AddMonoidAlgebra.single 0 (f b) := by
  classical
  rw [fixedIdeal, Ideal.span_le]
  constructor
  · intro h b
    ext m
    have hm := h (show (c b - AddMonoidAlgebra.single 0 b).coeff m ∈
      {d | ∃ b m, (c b - AddMonoidAlgebra.single 0 b).coeff m = d} from ⟨b, m, rfl⟩)
    change f ((c b - AddMonoidAlgebra.single 0 b).coeff m) = 0 at hm
    rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, map_sub, sub_eq_zero] at hm
    simpa only [AddMonoidAlgebra.coeff_mapRingHom,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply, apply_ite, map_zero] using hm
  · intro h d hd
    rcases hd with ⟨b, m, rfl⟩
    change f ((c b - AddMonoidAlgebra.single 0 b).coeff m) = 0
    rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, map_sub]
    apply sub_eq_zero.mpr
    have hm := congrArg (fun q : AddMonoidAlgebra D M => q.coeff m) (h b)
    simpa only [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, apply_ite, map_zero, sub_eq_zero] using hm

/-- A formally smooth algebra has a formally smooth fixed quotient for an additive
commutative group grading. The hypotheses say that scalars have degree zero and each
coefficient is homogeneous of its indicated degree. -/
theorem formallySmooth_quotient_fixedIdeal (c : B →+* AddMonoidAlgebra B M)
    [Algebra.FormallySmooth R B]
    (hR : ∀ r : R, c (algebraMap R B r) =
      AddMonoidAlgebra.single 0 (algebraMap R B r))
    (hδ : ∀ b m, c ((c b).coeff m) = AddMonoidAlgebra.single m ((c b).coeff m)) :
    Algebra.FormallySmooth R (B ⧸ fixedIdeal c) := by
  classical
  refine Algebra.FormallySmooth.of_comp_surjective fun D _ _ J hJ x => ?_
  have hJ' : ∀ a ∈ J, ∀ b ∈ J, a * b = 0 := by
    intro a ha b hb
    have h : a * b ∈ J ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul ha hb
    simpa only [hJ, Ideal.mem_bot] using h
  let y : B →ₐ[R] D ⧸ J := x.comp (Ideal.Quotient.mkₐ R (fixedIdeal c))
  have hy : ∀ b m, y ((c b - AddMonoidAlgebra.single 0 b).coeff m) = 0 := by
    intro b m
    have h : (c b - AddMonoidAlgebra.single 0 b).coeff m ∈ fixedIdeal c :=
      Ideal.subset_span ⟨b, m, rfl⟩
    change x (Ideal.Quotient.mk (fixedIdeal c) _) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 h, map_zero]
  have hyn : ∀ b m, m ≠ 0 → y ((c b).coeff m) = 0 := by
    intro b m hm
    have h := hy b m
    simpa only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
      AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hm, sub_zero] using h
  have hy0 : ∀ b, y ((c b).coeff 0) = y b := by
    intro b
    have h := hy b 0
    simpa only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply,
      AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, map_sub, sub_eq_zero] using h
  have hnil : IsNilpotent J := ⟨2, hJ⟩
  let Y : B →ₐ[R] D := Algebra.FormallySmooth.lift J hnil y
  have hY : ∀ b, Ideal.Quotient.mk J (Y b) = y b :=
    Algebra.FormallySmooth.mk_lift J hnil y
  let L : B →+* AddMonoidAlgebra D M :=
    (AddMonoidAlgebra.mapRingHom M (Y : B →+* D)).comp c
  have hL : ∀ b m, (L b).coeff m = Y ((c b).coeff m) := by
    intro b m
    exact AddMonoidAlgebra.coeff_mapRingHom _ _ _
  have hLm : ∀ b m, m ≠ 0 → (L b).coeff m ∈ J := by
    intro b m hm
    rw [hL, ← Ideal.Quotient.eq_zero_iff_mem, hY, hyn b m hm]
  let z : B →ₐ[R] D :=
    { toFun := fun b => (L b).coeff 0
      map_one' := by rw [map_one]; exact AddMonoidAlgebra.coeff_one_zero
      map_mul' := fun b b' => by
        rw [map_mul]
        exact coeff_mul_zero_of_off_mem hJ' (hLm b) (hLm b')
      map_zero' := congrArg (fun q : AddMonoidAlgebra D M => q.coeff 0) L.map_zero
      map_add' := fun b b' => by rw [map_add]; rfl
      commutes' := fun r => by
        rw [hL, hR, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
        exact Y.commutes r }
  have hz_apply : ∀ b, z b = Y ((c b).coeff 0) := fun b => hL b 0
  have hz_homogeneous : ∀ b m, z ((c b).coeff m) =
      if m = 0 then Y ((c b).coeff m) else 0 := by
    intro b m
    rw [hz_apply, hδ, AddMonoidAlgebra.coeff_single]
    by_cases hm : m = 0
    · simp [hm]
    · simp [hm, Ne.symm hm]
  have hz : ∀ d ∈ fixedIdeal c, z d = 0 := by
    intro d hd
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hd
    · rintro _ ⟨b, m, rfl⟩
      rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply]
      by_cases hm : m = 0
      · subst hm
        rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, map_sub,
          hz_homogeneous, ite_eq_left rfl, hz_apply, sub_self]
      · rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hm, sub_zero,
          hz_homogeneous, ite_eq_right hm]
    · exact map_zero z
    · intro a a' _ _ ha ha'
      rw [map_add, ha, ha', add_zero]
    · intro a a' _ ha'
      rw [smul_eq_mul, map_mul, ha', mul_zero]
  refine ⟨Ideal.Quotient.liftₐ (fixedIdeal c) z hz, ?_⟩
  apply Ideal.Quotient.algHom_ext
  refine AlgHom.ext fun b => ?_
  change Ideal.Quotient.mk J (z b) = y b
  rw [hz_apply, hY, hy0]

end Langlands.CommutativeAlgebra.GradedFixedQuotient
