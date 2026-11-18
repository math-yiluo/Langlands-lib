import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions

/-! # Controlled finite coefficient changes and bounded algebraic comparisons -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

namespace BoundedAlgHom

variable {K : Type u} {A : Type v} {B : Type w} {C : Type z}
  [NormedField K] [NormedCommRing A] [NormedCommRing B] [NormedCommRing C]
  [NormedAlgebra K A] [NormedAlgebra K B] [NormedAlgebra K C]

/-- Changing a fixed finite generating tuple preserves controlled coefficient
lifts when the map already has a finite Banach structure. -/
theorem IsFiniteBanach.exists_coefficient_lifts {f : BoundedAlgHom K A B}
    (hf : f.IsFiniteBanach) {n : ℕ} (b : Fin n → B)
    (hb : Function.Surjective (f.coefficientMap b)) :
    ∃ M > 0, ∀ y : B, ∃ c : Fin n → A,
      f.coefficientMap b c = y ∧ ‖c‖ ≤ M * ‖y‖ := by
  classical
  obtain ⟨m, d, D, hD, hd⟩ := hf
  choose a ha using fun j : Fin m => hb (d j)
  let S := (∑ j, ‖a j‖) + 1
  have hsum : 0 ≤ ∑ j, ‖a j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hS : 0 < S := by dsimp [S]; linarith
  refine ⟨S * D, mul_pos hS hD, fun y => ?_⟩
  obtain ⟨c, hc, hcn⟩ := hd y
  let c' : Fin n → A := fun k => ∑ j, c j * a j k
  have hc' : f.coefficientMap b c' = f.coefficientMap d c := by
    change (∑ k, f (∑ j, c j * a j k) * b k) = ∑ j, f (c j) * d j
    simp_rw [map_sum, Finset.sum_mul, map_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← ha j, coefficientMap_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => mul_assoc _ _ _
  refine ⟨c', hc'.trans hc, ?_⟩
  have hchange : ‖c'‖ ≤ S * ‖c‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hS.le (norm_nonneg c))).2
    intro k
    calc
      ‖c' k‖ ≤ ∑ j, ‖c j * a j k‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖c‖ * ‖a j‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact (norm_mul_le _ _).trans
          (mul_le_mul (norm_le_pi_norm c j) (norm_le_pi_norm (a j) k)
            (norm_nonneg _) (norm_nonneg c))
      _ = (∑ j, ‖a j‖) * ‖c‖ := by rw [← Finset.mul_sum, mul_comm]
      _ ≤ S * ‖c‖ := mul_le_mul_of_nonneg_right (by dsimp [S]; linarith)
        (norm_nonneg c)
  exact hchange.trans ((mul_le_mul_of_nonneg_left hcn hS.le).trans_eq
    (mul_assoc S D ‖y‖).symm)

/-- A compatible algebraic map from a finite Banach algebra is bounded.
The proof uses the supplied finite coefficient lifts, so no nontrivial
valuation or completeness assumption is needed. -/
def ofFiniteBanachTriangle (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach)
    (g : BoundedAlgHom K A C) (h : B →ₐ[K] C)
    (comm : h.comp f.toAlgHom = g.toAlgHom) : BoundedAlgHom K B C where
  toAlgHom := h
  bounded := by
    obtain ⟨n, b, M, hM, hb⟩ := hf
    obtain ⟨D, hD, hg⟩ := g.bounded
    let S := (∑ i, ‖h (b i)‖) + 1
    have hsum : 0 ≤ ∑ i, ‖h (b i)‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    have hS : 0 < S := by dsimp [S]; linarith
    refine ⟨D * M * S, mul_pos (mul_pos hD hM) hS, fun y => ?_⟩
    obtain ⟨c, hc, hcn⟩ := hb y
    have heq : h y = ∑ i, g (c i) * h (b i) := by
      rw [← hc, coefficientMap_apply, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul]
      exact congrArg (fun q : A →ₐ[K] C => q (c i) * h (b i)) comm
    change ‖h y‖ ≤ (D * M * S) * ‖y‖
    rw [heq]
    calc
      ‖∑ i, g (c i) * h (b i)‖ ≤ ∑ i, ‖g (c i) * h (b i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, (D * M * ‖y‖) * ‖h (b i)‖ := by
        apply Finset.sum_le_sum
        intro i _
        apply (norm_mul_le _ _).trans
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        calc
          ‖g (c i)‖ ≤ D * ‖c i‖ := hg _
          _ ≤ D * ‖c‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm c i) hD.le
          _ ≤ D * (M * ‖y‖) := mul_le_mul_of_nonneg_left hcn hD.le
          _ = D * M * ‖y‖ := (mul_assoc _ _ _).symm
      _ = (D * M * ‖y‖) * (∑ i, ‖h (b i)‖) := (Finset.mul_sum _ _ _).symm
      _ ≤ (D * M * ‖y‖) * S := mul_le_mul_of_nonneg_left
        (by dsimp [S]; linarith) (mul_nonneg (mul_pos hD hM).le (norm_nonneg y))
      _ = (D * M * S) * ‖y‖ := by ring

@[simp] theorem ofFiniteBanachTriangle_toAlgHom
    (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach)
    (g : BoundedAlgHom K A C) (h : B →ₐ[K] C)
    (comm : h.comp f.toAlgHom = g.toAlgHom) :
    (ofFiniteBanachTriangle f hf g h comm).toAlgHom = h := rfl

@[simp] theorem ofFiniteBanachTriangle_comp
    (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach)
    (g : BoundedAlgHom K A C) (h : B →ₐ[K] C)
    (comm : h.comp f.toAlgHom = g.toAlgHom) :
    (ofFiniteBanachTriangle f hf g h comm).comp f = g :=
  BoundedAlgHom.ext fun a => congrArg (fun q : A →ₐ[K] C => q a) comm

end BoundedAlgHom

namespace BoundedAlgEquiv

variable {K : Type u} {A : Type v} {B : Type w} {C : Type z}
  [NormedField K] [NormedCommRing A] [NormedCommRing B] [NormedCommRing C]
  [NormedAlgebra K A] [NormedAlgebra K B] [NormedAlgebra K C]

/-- An algebraic equivalence over a fixed base between two supplied finite
Banach algebras has bounded maps in both directions. -/
def ofFiniteBanachTriangle (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach)
    (g : BoundedAlgHom K A C) (hg : g.IsFiniteBanach)
    (e : B ≃ₐ[K] C) (comm : e.toAlgHom.comp f.toAlgHom = g.toAlgHom) :
    BoundedAlgEquiv K B C := by
  have comm_symm : e.symm.toAlgHom.comp g.toAlgHom = f.toAlgHom := by
    apply AlgHom.ext
    intro a
    have ha := congrArg (fun q : A →ₐ[K] C => q a) comm
    change e.symm (g a) = f a
    rw [← ha]
    exact e.symm_apply_apply _
  exact ofHomInv
    (BoundedAlgHom.ofFiniteBanachTriangle f hf g e.toAlgHom comm)
    (BoundedAlgHom.ofFiniteBanachTriangle g hg f e.symm.toAlgHom comm_symm)
    e.symm_apply_apply e.apply_symm_apply

@[simp] theorem ofFiniteBanachTriangle_toAlgEquiv
    (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach)
    (g : BoundedAlgHom K A C) (hg : g.IsFiniteBanach)
    (e : B ≃ₐ[K] C) (comm : e.toAlgHom.comp f.toAlgHom = g.toAlgHom) :
    (ofFiniteBanachTriangle f hf g hg e comm).toAlgEquiv = e := by
  ext
  rfl

end BoundedAlgEquiv
end Langlands.Analytic
