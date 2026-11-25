/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Polynomial.ContentIdeal
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.SymmetricProduct.Bilinear

/-!
# Multiplication of binary forms

A point `(a₀ : a₁)` of `ℙ¹` is a linear form `a₀ t + a₁` up to scalars, and a point
`(b₀ : ⋯ : bₖ)` of `ℙᵏ` is a polynomial `∑ⱼ bⱼ tʲ` of degree at most `k` up to scalars. Their
product `(a₀ t + a₁) · ∑ⱼ bⱼ tʲ` is a polynomial of degree at most `k + 1`, i.e. a point of
`ℙᵏ⁺¹`. The coefficients of the product are bilinear in `a` and `b`, so this is a bilinear
morphism `ℙ¹ ×_ℤ ℙᵏ ⟶ ℙᵏ⁺¹` in the sense of `AlgebraicGeometry.Proj.bilinear`; it is
well defined because the product of two polynomials whose coefficients generate the unit ideal
again has this property (Gauss' lemma for content ideals), finite by the general theory, and
surjective because over an algebraically closed field every nonzero polynomial of degree at most
`k + 1` is the product of a linear form and a polynomial of degree at most `k` (with the convention
that the linear form `1` accounts for a root at infinity).

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace.mulCoeff` — the coefficients of the product.
- `AlgebraicGeometry.ProjectiveSpace.mulForm` — the coefficients as linear forms in the Segre
  coordinates.
- `AlgebraicGeometry.ProjectiveSpace.projectiveLineMul` — the multiplication morphism
  `ℙ¹_{ℙᵏ_S} ⟶ ℙᵏ⁺¹_S`.

## Main results

- `AlgebraicGeometry.ProjectiveSpace.span_range_mulCoeff` — the coefficients of the product have
  no common zero.
- `AlgebraicGeometry.ProjectiveSpace.exists_mulCoeff_eq` — the factorisation of binary forms
  over an algebraically closed field.
- `AlgebraicGeometry.ProjectiveSpace.isFinite_projectiveLineMul`,
  `AlgebraicGeometry.ProjectiveSpace.surjective_projectiveLineMul`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

section Algebra

variable {R : Type*} [CommRing R] {k : ℕ}

/-- The coefficient of `tᶜ` in the product `(a₀ t + a₁) · ∑ⱼ bⱼ tʲ`. -/
def mulCoeff (a : ULift.{u} (Fin 2) → R) (b : ULift.{u} (Fin (k + 1)) → R) (c : ℕ) : R :=
  ∑ j : ULift.{u} (Fin (k + 1)), ((if c = (j.down : ℕ) + 1 then a ⟨0⟩ * b j else 0) +
    (if c = (j.down : ℕ) then a ⟨1⟩ * b j else 0))

/-- The polynomial `∑ⱼ bⱼ tʲ` attached to a vector `b`. -/
def vecPoly (b : ULift.{u} (Fin (k + 1)) → R) : R[X] :=
  ∑ j : ULift.{u} (Fin (k + 1)), C (b j) * X ^ (j.down : ℕ)

/-- `mulCoeff a b c` is the coefficient of `tᶜ` in `(a₀ t + a₁) · ∑ⱼ bⱼ tʲ`. -/
lemma mulCoeff_eq_coeff (a : ULift.{u} (Fin 2) → R) (b : ULift.{u} (Fin (k + 1)) → R) (c : ℕ) :
    mulCoeff a b c = ((C (a ⟨0⟩) * X + C (a ⟨1⟩)) * vecPoly b).coeff c := by
  rw [vecPoly, Finset.mul_sum, finsetSum_coeff, mulCoeff]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have : (C (a ⟨0⟩) * X + C (a ⟨1⟩)) * (C (b j) * X ^ (j.down : ℕ)) =
      C (a ⟨0⟩ * b j) * X ^ ((j.down : ℕ) + 1) + C (a ⟨1⟩ * b j) * X ^ (j.down : ℕ) := by
    simp only [C_mul, pow_succ]
    ring
  rw [this, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X_pow]

/-- The coefficients of `∑ⱼ bⱼ tʲ` are the entries of `b`. -/
lemma coeff_vecPoly (b : ULift.{u} (Fin (k + 1)) → R) (j : ULift.{u} (Fin (k + 1))) :
    (vecPoly b).coeff j.down = b j := by
  rw [vecPoly, finsetSum_coeff, Finset.sum_eq_single j]
  · rw [coeff_C_mul_X_pow, ite_eq_left rfl]
  · intro j' _ hj'
    rw [coeff_C_mul_X_pow, ite_eq_right]
    intro h
    exact hj' (ULift.ext (Fin.ext h.symm))
  · simp

/-- A polynomial of degree at most `k` is `∑ⱼ bⱼ tʲ` for its vector of coefficients. -/
lemma vecPoly_coeff (Q : R[X]) (hQ : Q.natDegree < k + 1) :
    vecPoly (fun j : ULift.{u} (Fin (k + 1)) ↦ Q.coeff j.down) = Q := by
  conv_rhs => rw [Q.as_sum_range_C_mul_X_pow' hQ]
  rw [vecPoly, ← Fin.sum_univ_eq_sum_range (fun i ↦ C (Q.coeff i) * X ^ i),
    ← (Equiv.ulift : ULift.{u} (Fin (k + 1)) ≃ Fin (k + 1)).sum_comp]
  rfl

/-- **No common zero**: if the entries of `a` and of `b` generate the unit ideal, so do the
coefficients of the product `(a₀ t + a₁) · ∑ⱼ bⱼ tʲ` (Gauss' lemma for content ideals). -/
lemma span_range_mulCoeff (a : ULift.{u} (Fin 2) → R) (b : ULift.{u} (Fin (k + 1)) → R)
    (ha : Ideal.span (Set.range a) = ⊤) (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun c : Fin (k + 2) ↦ mulCoeff a b c) = ⊤ := by
  have hA : (C (a ⟨0⟩) * X + C (a ⟨1⟩)).contentIdeal = ⊤ := by
    refine top_unique (ha ▸ Ideal.span_le.mpr ?_)
    rintro _ ⟨⟨i⟩, rfl⟩
    fin_cases i
    · have h := coeff_mem_contentIdeal (C (a ⟨0⟩) * X + C (a ⟨1⟩)) 1
      rwa [coeff_add, coeff_C_mul, coeff_X_one, coeff_C, ite_eq_right one_ne_zero, mul_one,
        add_zero] at h
    · have h := coeff_mem_contentIdeal (C (a ⟨0⟩) * X + C (a ⟨1⟩)) 0
      rwa [coeff_add, coeff_C_mul, coeff_X_zero, mul_zero, zero_add, coeff_C_zero] at h
  have hB : (vecPoly b).contentIdeal = ⊤ := by
    refine top_unique (hb ▸ Ideal.span_le.mpr ?_)
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, ← coeff_vecPoly b j]
    exact coeff_mem_contentIdeal _ _
  have hAB := contentIdeal_mul_eq_top_of_contentIdeal_eq_top hA hB
  refine top_unique (hAB ▸ Ideal.span_le.mpr ?_)
  intro x hx
  obtain ⟨c, -, rfl⟩ := mem_coeffs_iff.mp hx
  by_cases hc : c < k + 2
  · exact Ideal.subset_span ⟨⟨c, hc⟩, mulCoeff_eq_coeff a b c⟩
  · rw [← mulCoeff_eq_coeff, mulCoeff, Finset.sum_eq_zero fun j _ ↦ by
      rw [ite_eq_right (by omega), ite_eq_right (by omega), add_zero]]
    exact zero_mem _

/-- **Binary forms factor over an algebraically closed field.** Every nonzero polynomial `V` of
degree at most `k + 1` over an algebraically closed field is, up to a nonzero scalar `κ`, the
product of a linear form `a₀ t + a₁` and a polynomial `∑ⱼ bⱼ tʲ` of degree at most `k`, with
normalised vectors `a` and `b`. -/
lemma exists_mulCoeff_eq {K : Type*} [Field K] [IsAlgClosed K] (V : K[X]) (hV : V ≠ 0)
    (hVdeg : V.natDegree ≤ k + 1) :
    ∃ (a : ULift.{u} (Fin 2) → K) (b : ULift.{u} (Fin (k + 1)) → K) (i : ULift.{u} (Fin 2))
      (j : ULift.{u} (Fin (k + 1))) (κ : K), a i = 1 ∧ b j = 1 ∧ κ ≠ 0 ∧
        ∀ c : ℕ, mulCoeff a b c = κ * V.coeff c := by
  obtain ⟨a, i, hai, Q, hQ, hVQ⟩ : ∃ (a : ULift.{u} (Fin 2) → K) (i : ULift.{u} (Fin 2)),
      a i = 1 ∧ ∃ Q : K[X], Q.natDegree < k + 1 ∧ V = (C (a ⟨0⟩) * X + C (a ⟨1⟩)) * Q := by
    by_cases hdeg : V.degree = 0
    · refine ⟨fun i ↦ ![0, 1] i.down, ⟨1⟩, rfl, V, ?_, ?_⟩
      · rw [natDegree_eq_of_degree_eq_some hdeg]
        exact Nat.succ_pos k
      · simp
    · obtain ⟨r, hr⟩ := IsAlgClosed.exists_root V hdeg
      refine ⟨fun i ↦ ![1, -r] i.down, ⟨0⟩, rfl, V /ₘ (X - C r), ?_, ?_⟩
      · rw [natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C]
        have : 0 < V.natDegree := natDegree_pos_iff_degree_pos.mpr
          (lt_of_le_of_ne (zero_le_degree_iff.mpr hV) (Ne.symm hdeg))
        omega
      · simp only [Fin.isValue, Matrix.cons_val_zero, map_one, one_mul, Matrix.cons_val_one,
          map_neg, ← sub_eq_add_neg]
        exact ((mul_divByMonic_eq_iff_isRoot).mpr hr).symm
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    exact hV (by simpa using hVQ)
  obtain ⟨j, hj⟩ : ∃ j : ULift.{u} (Fin (k + 1)), Q.coeff j.down ≠ 0 := by
    by_contra! h
    refine hQ0 (Polynomial.ext fun d ↦ ?_)
    by_cases hd : d < k + 1
    · simpa using h ⟨⟨d, hd⟩⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_zero]
  refine ⟨a, fun j' ↦ (Q.coeff j.down)⁻¹ * Q.coeff j'.down, i, j, (Q.coeff j.down)⁻¹, hai,
    inv_mul_cancel₀ hj, inv_ne_zero hj, fun c ↦ ?_⟩
  have hb : vecPoly (fun j' : ULift.{u} (Fin (k + 1)) ↦ (Q.coeff j.down)⁻¹ * Q.coeff j'.down) =
      C (Q.coeff j.down)⁻¹ * Q := by
    conv_rhs => enter [2]; rw [← vecPoly_coeff Q hQ]
    rw [vecPoly, vecPoly, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ ↦ ?_
    rw [C_mul, mul_assoc]
  rw [mulCoeff_eq_coeff, hb, mul_left_comm, coeff_C_mul, ← hVQ]

end Algebra

section Morphism

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : ℕ} {ι : Type u} (e : ι ≃ Fin (k + 2))

/-- The coefficient of `t^(e c)` in `(x₀ t + x₁) · ∑ⱼ yⱼ tʲ`, as a linear form in the Segre
coordinates `W_{i,j} = xᵢ yⱼ` of `ℙ¹ ×_ℤ ℙᵏ`. -/
def mulForm (c : ι) :
    MvPolynomial (ULift.{u} (Fin 2) × ULift.{u} (Fin (k + 1))) (ULift.{u} ℤ) :=
  ∑ j : ULift.{u} (Fin (k + 1)),
    ((if (e c : ℕ) = (j.down : ℕ) + 1 then MvPolynomial.X (⟨0⟩, j) else 0) +
      (if (e c : ℕ) = j.down then MvPolynomial.X (⟨1⟩, j) else 0))

/-- The forms `mulForm e c` are linear. -/
lemma mulForm_mem (c : ι) :
    mulForm e c ∈ MvPolynomial.homogeneousSubmodule _ (ULift.{u} ℤ) 1 := by
  refine Submodule.sum_mem _ fun j _ ↦ Submodule.add_mem _ ?_ ?_ <;> split_ifs <;>
    first
    | exact MvPolynomial.X_mem_homogeneousSubmodule_one _ _
    | exact Submodule.zero_mem _

/-- Evaluating the form `mulForm e c` at the products `aᵢ bⱼ` gives the coefficient
`mulCoeff a b (e c)`. -/
lemma eval₂_mulForm {R : Type*} [CommRing R] (a : ULift.{u} (Fin 2) → R)
    (b : ULift.{u} (Fin (k + 1)) → R) (c : ι) :
    MvPolynomial.eval₂ ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom)
      (fun kl ↦ a kl.1 * b kl.2) (mulForm e c) = mulCoeff a b (e c) := by
  rw [← MvPolynomial.coe_eval₂Hom, mulForm, map_sum, mulCoeff]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_add]
  split_ifs <;> simp

/-- **The coefficients of the product have no common zero** on the chart
`D₊(Xᵢ) ×_ℤ D₊(Yⱼ)` of `ℙ¹ ×_ℤ ℙᵏ`. -/
lemma span_range_bilinearChartSection_mulForm (i : ULift.{u} (Fin 2))
    (j : ULift.{u} (Fin (k + 1))) :
    Ideal.span (Set.range (Proj.bilinearChartSection (mulForm e) i j)) = ⊤ := by
  set α : ULift.{u} (Fin 2) → Γ((Proj.segreCover _ _).X (i, j), ⊤) := fun i' ↦
    ((Scheme.ΓSpecIso _).inv ≫ (Proj.segreCoverFst i j).appTop).hom
      (MvPolynomial.awayXRatio (ULift.{u} ℤ) i i')
  set β : ULift.{u} (Fin (k + 1)) → Γ((Proj.segreCover _ _).X (i, j), ⊤) := fun j' ↦
    ((Scheme.ΓSpecIso _).inv ≫ (Proj.segreCoverSnd i j).appTop).hom
      (MvPolynomial.awayXRatio (ULift.{u} ℤ) j j')
  have h (c : ι) : Proj.bilinearChartSection (mulForm e) i j c = mulCoeff α β (e c) :=
    eval₂_mulForm e α β c
  have hα : Ideal.span (Set.range α) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    exact Ideal.subset_span ⟨i, by simp [α]⟩
  have hβ : Ideal.span (Set.range β) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    exact Ideal.subset_span ⟨j, by simp [β]⟩
  have hrange : Set.range (Proj.bilinearChartSection (mulForm e) i j) =
      Set.range fun c : Fin (k + 2) ↦ mulCoeff α β c := by
    rw [funext h, ← e.symm.surjective.range_comp]
    simp [Function.comp_def]
  rw [hrange]
  exact span_range_mulCoeff α β hα hβ

/-- **The multiplication morphism of the integral models is surjective**: over an algebraically
closed field every binary form of degree `k + 1` is the product of a linear form and a binary
form of degree `k`. -/
lemma surjective_bilinear_mulForm :
    Surjective (Proj.bilinear _ _ (mulForm e) (mulForm_mem e)
      (span_range_bilinearChartSection_mulForm e)) := by
  refine Proj.surjective_bilinear _ _ _ fun K _ _ v ⟨c₀, hc₀⟩ ↦ ?_
  have : Fintype ι := Fintype.ofEquiv _ e.symm
  set V : K[X] := ∑ c, C (v c) * X ^ (e c : ℕ)
  have hV (c : ι) : V.coeff (e c) = v c := by
    rw [finsetSum_coeff, Finset.sum_eq_single c]
    · rw [coeff_C_mul_X_pow, ite_eq_left rfl]
    · intro c' _ hc'
      rw [coeff_C_mul_X_pow, ite_eq_right]
      intro h
      exact hc' (e.injective (Fin.ext h).symm)
    · simp
  have hV0 : V ≠ 0 := by
    intro h
    exact hc₀ (by rw [← hV c₀, h, coeff_zero])
  have hVdeg : V.natDegree ≤ k + 1 :=
    natDegree_sum_le_of_forall_le _ _ fun c _ ↦
      (natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ (e c).2)
  obtain ⟨a, b, i, j, κ, hai, hbj, hκ, hab⟩ := exists_mulCoeff_eq V hV0 hVdeg
  exact ⟨a, b, i, j, κ, hai, hbj, hκ, fun c ↦ by rw [eval₂_mulForm, hab, hV]⟩

variable (S : Scheme.{u})

/-- **The multiplication morphism** `ℙ¹_{ℙᵏ_S} ⟶ ℙ(ι; S)` (for `ι ≃ Fin (k + 2)`), sending a
linear form `a₀ t + a₁` and a polynomial `∑ⱼ bⱼ tʲ` of degree at most `k` to their product. -/
def projectiveLineMul : ProjectiveLine ℙ(ULift.{u} (Fin (k + 1)); S) ⟶ ℙ(ι; S) :=
  (isPullback_map (ULift.{u} (Fin 2)) (ℙ(ULift.{u} (Fin (k + 1)); S) ↘ S)).isoPullback.hom ≫
    bilinear (mulForm e) (mulForm_mem e) (span_range_bilinearChartSection_mulForm e) S

/-- The multiplication morphism is a morphism over `S`. -/
@[reassoc (attr := simp)]
lemma projectiveLineMul_over :
    projectiveLineMul e S ≫ ℙ(ι; S) ↘ S =
      (ProjectiveLine ℙ(ULift.{u} (Fin (k + 1)); S) ↘ ℙ(ULift.{u} (Fin (k + 1)); S)) ≫
        ℙ(ULift.{u} (Fin (k + 1)); S) ↘ S := by
  rw [projectiveLineMul, Category.assoc, bilinear_over, IsPullback.isoPullback_hom_fst_assoc,
    map_over]

/-- The multiplication morphism is finite. -/
instance isFinite_projectiveLineMul : IsFinite (projectiveLineMul e S) := by
  rw [projectiveLineMul]
  infer_instance

/-- The multiplication morphism is surjective. -/
instance surjective_projectiveLineMul : Surjective (projectiveLineMul e S) := by
  have := surjective_bilinear _ _ _ S (surjective_bilinear_mulForm e)
  rw [projectiveLineMul]
  infer_instance

end Morphism

end AlgebraicGeometry.ProjectiveSpace
