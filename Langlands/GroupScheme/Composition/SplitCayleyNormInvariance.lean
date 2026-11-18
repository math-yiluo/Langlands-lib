import Langlands.GroupScheme.Composition.CayleyAutomorphismGroup

/-! # Automorphisms of the split Cayley algebra over a field preserve its norm -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace SplitCayley

section Ring

variable (R : Type u) [CommRing R]

/-- The trace `a + b` of a Zorn vector matrix `(a, u, v, b)`. -/
def trace (x : Fin 8 → R) : R := x 0 + x 7

/-- Every Zorn vector matrix satisfies its quadratic equation `x² = T(x) x - N(x) 1`. -/
theorem mul_self (x : Fin 8 → R) :
    mul R x x = trace R x • x - norm R x • unit R := by
  funext i
  fin_cases i <;> simp [mul_apply, mulFun, trace, norm_apply, unit] <;> ring

end Ring

section Field

variable {F : Type u} [Field F]

/-- A linear automorphism of `F⁸` fixing `(1, 0, 0, 1)` and preserving the Zorn product
preserves the Zorn norm. -/
theorem norm_mulVec_eq (g : GL (Fin 8) F)
    (hu : (g : Matrix (Fin 8) (Fin 8) F).mulVec (unit F) = unit F)
    (hm : ∀ x y, (g : Matrix (Fin 8) (Fin 8) F).mulVec (mul F x y) =
      mul F ((g : Matrix (Fin 8) (Fin 8) F).mulVec x) ((g : Matrix (Fin 8) (Fin 8) F).mulVec y))
    (x : Fin 8 → F) :
    norm F ((g : Matrix (Fin 8) (Fin 8) F).mulVec x) = norm F x := by
  set y := (g : Matrix (Fin 8) (Fin 8) F).mulVec x with hy
  have h1 : mul F y y = trace F x • y - norm F x • unit F := by
    rw [hy, ← hm, mul_self, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hu]
  have h2 := mul_self F y
  have h3 : (trace F x - trace F y) • y = (norm F x - norm F y) • unit F := by
    rw [sub_smul, sub_smul]
    exact sub_eq_sub_iff_sub_eq_sub.mp (h1.symm.trans h2)
  have hginv : ∀ v : Fin 8 → F, ((g⁻¹ : GL (Fin 8) F) : Matrix (Fin 8) (Fin 8) F).mulVec
      ((g : Matrix (Fin 8) (Fin 8) F).mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  by_cases hT : trace F x = trace F y
  · rw [hT, sub_self, zero_smul] at h3
    have h0 := congrFun h3 0
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, unit] at h0
    simp only [Matrix.cons_val_zero, mul_one] at h0
    exact (sub_eq_zero.mp h0.symm).symm
  · exfalso
    apply hT
    have hne : trace F x - trace F y ≠ 0 := sub_ne_zero.mpr hT
    set c := (trace F x - trace F y)⁻¹ * (norm F x - norm F y) with hc
    have hyc : y = c • unit F := by
      rw [hc, mul_smul, ← h3, smul_smul, inv_mul_cancel₀ hne, one_smul]
    have hxc : x = c • unit F := by
      have h := hginv x
      rw [← hy, hyc, Matrix.mulVec_smul] at h
      have hu' : ((g⁻¹ : GL (Fin 8) F) : Matrix (Fin 8) (Fin 8) F).mulVec (unit F) = unit F := by
        conv_lhs => rw [← hu]
        exact hginv _
      rw [hu'] at h
      exact h.symm
    rw [← hxc] at hyc
    rw [hyc]

/-- The polar form of the Zorn norm is preserved as well. -/
theorem polar_norm_mulVec_eq (g : GL (Fin 8) F)
    (hu : (g : Matrix (Fin 8) (Fin 8) F).mulVec (unit F) = unit F)
    (hm : ∀ x y, (g : Matrix (Fin 8) (Fin 8) F).mulVec (mul F x y) =
      mul F ((g : Matrix (Fin 8) (Fin 8) F).mulVec x) ((g : Matrix (Fin 8) (Fin 8) F).mulVec y))
    (x y : Fin 8 → F) :
    QuadraticMap.polar (norm F) ((g : Matrix (Fin 8) (Fin 8) F).mulVec x)
        ((g : Matrix (Fin 8) (Fin 8) F).mulVec y) =
      QuadraticMap.polar (norm F) x y := by
  simp only [QuadraticMap.polar, ← Matrix.mulVec_add, norm_mulVec_eq g hu hm]

end Field

end SplitCayley

namespace CayleyDatum

variable {K : Type u} [Field K]

/-- Automorphism matrices of the split datum with coefficients in a field preserve the Zorn
norm over that field. -/
theorem split_norm_mulVec_eq {F : Type u} [Field F] (φ : K →+* F) {g : GL (Fin 8) F}
    (hg : (split K).IsAutomorphismMatrix φ g) (x : Fin 8 → F) :
    SplitCayley.norm F ((g : Matrix (Fin 8) (Fin 8) F).mulVec x) = SplitCayley.norm F x := by
  refine SplitCayley.norm_mulVec_eq g ?_ ?_ x
  · have h := hg.1
    rw [split_unitOver] at h
    exact h
  · intro y z
    have h := hg.2 y z
    rw [split_multiplicationOver, split_multiplicationOver] at h
    exact h

/-- Automorphism matrices are preserved by every change of coefficients. -/
theorem IsAutomorphismMatrix.map (c : CayleyDatum K) {A B : Type u} [CommRing A] [CommRing B]
    (φ : K →+* A) (f : A →+* B) {g : GL (Fin 8) A} (hg : c.IsAutomorphismMatrix φ g) :
    c.IsAutomorphismMatrix (f.comp φ) (Matrix.GeneralLinearGroup.map f g) := by
  rw [isAutomorphismMatrix_iff] at hg ⊢
  refine ⟨fun i => ?_, fun i j k => ?_⟩
  · change c.unitDefect (f.comp φ) ((g : Matrix (Fin 8) (Fin 8) A).map f) i = 0
    rw [← c.map_unitDefect φ f, hg.1 i, map_zero]
  · have h := c.map_multiplicationDefect φ f (g : Matrix (Fin 8) (Fin 8) A)
      (Pi.single j 1) (Pi.single k 1) i
    have hs : ∀ m : Fin 8, (fun l => f ((Pi.single m (1 : A) : Fin 8 → A) l)) =
        Pi.single m 1 := by
      intro m
      funext l
      by_cases hl : l = m
      · subst hl; simp
      · simp [hl]
    rw [hs, hs, hg.2 i j k, map_zero] at h
    exact h.symm.trans rfl

end CayleyDatum

end Langlands.GroupScheme
