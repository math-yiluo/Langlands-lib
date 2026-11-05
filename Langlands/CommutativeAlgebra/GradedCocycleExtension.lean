import Langlands.CommutativeAlgebra.GradedDVRIntegrality
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Contracting cocycles of a graded coalgebra have no negative Laurent terms

Let `B` be a `k`-algebra with a `ℤ`-grading `c`, a counit `ε` killing the nonzero weights and a
comultiplication `Δ` respecting total weight. A contracting point `x : B → k[t, t⁻¹]` satisfying
the cocycle identity `x(st) = x(s) · (s · x(t))` in `k[t, t⁻¹][s, s⁻¹]` takes values in `k[t]`.
-/

noncomputable section

universe u

open TensorProduct

namespace Langlands.CommutativeAlgebra

namespace GradedCocycle

open GradedDVRIntegrality

variable {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B]

/-- `y` is homogeneous of weight `i` for the grading `c`. -/
def IsHomogeneous (c : B →+* LaurentPolynomial B) (i : ℤ) (y : B) : Prop :=
  c y = AddMonoidAlgebra.single i y

theorem IsHomogeneous.coeff_self {c : B →+* LaurentPolynomial B} {i : ℤ} {y : B}
    (h : IsHomogeneous c i y) : (c y).coeff i = y := by
  rw [h, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]

variable (k) in
/-- The span of the pure tensors `y₁ ⊗ y₂` of homogeneous elements of total weight `d`. -/
def tensorWeightSpan (c : B →+* LaurentPolynomial B) (d : ℤ) : Submodule k (B ⊗[k] B) :=
  Submodule.span k {w | ∃ y₁ y₂ i j, IsHomogeneous c i y₁ ∧ IsHomogeneous c j y₂ ∧ i + j = d ∧
    y₁ ⊗ₜ y₂ = w}

variable (k) in
/-- Laurent polynomials in two variables without negative exponents. -/
def polynomialPart : Submodule k (LaurentPolynomial (LaurentPolynomial k)) where
  carrier := {F | ∀ m n, (m < 0 ∨ n < 0) → (F.coeff m).coeff n = 0}
  add_mem' := by
    intro F G hF hG m n h
    change ((F + G).coeff m).coeff n = 0
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, hF m n h, hG m n h, add_zero]
  zero_mem' := by
    intro m n _
    rfl
  smul_mem' := by
    intro r F hF m n h
    change ((r • F).coeff m).coeff n = 0
    rw [AddMonoidAlgebra.coeff_smul_apply, AddMonoidAlgebra.coeff_smul_apply, hF m n h, smul_zero]

theorem productMap_comp_comp {A C : Type u} [CommRing A] [Algebra k A] [CommRing C]
    [Algebra k C] (f : A →ₐ[k] C) (g h : B →ₐ[k] A) :
    Algebra.TensorProduct.productMap (f.comp g) (f.comp h) =
      f.comp (Algebra.TensorProduct.productMap g h) :=
  Algebra.TensorProduct.ext' fun a b => by
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.productMap_apply_tmul, map_mul]

section Core

variable {c : B →+* LaurentPolynomial B} {ε : B →ₐ[k] k} {Δ : B →ₐ[k] B ⊗[k] B}
  {x : B →ₐ[k] LaurentPolynomial k} {P Q : B →ₐ[k] LaurentPolynomial (LaurentPolynomial k)}
  {X : B → LaurentPolynomial (LaurentPolynomial k)}

theorem eq_zero_of_neg (hx : IsContracting c ε x) {i : ℤ} {y : B} (hy : IsHomogeneous c i y)
    (hi : i < 0) : x y = 0 := by
  have h := hx.1 y i hi
  rwa [hy.coeff_self] at h

theorem eq_algebraMap_of_zero (hx : IsContracting c ε x) {y : B} (hy : IsHomogeneous c 0 y) :
    x y = algebraMap k _ (ε y) := by
  have h := hx.2 y
  rwa [hy.coeff_self] at h

theorem counit_eq_zero (hε : ∀ b n, ε ((c b).coeff n) = if n = 0 then ε b else 0) {i : ℤ}
    {y : B} (hy : IsHomogeneous c i y) (hi : i ≠ 0) : ε y = 0 := by
  have h := hε y i
  rwa [hy.coeff_self, if_neg hi] at h

theorem algebraMap_laurent_coeff (r : k) (n : ℤ) :
    (algebraMap k (LaurentPolynomial k) r).coeff n = if n = 0 then r else 0 := by
  rw [LaurentPolynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    LaurentPolynomial.C_apply]

/-- The values of `P` only depend on the values of `x`. -/
theorem P_eq_of_eq (hP : ∀ b m, (P b).coeff m = LaurentPolynomial.C ((x b).coeff m)) {b b' : B}
    (h : x b = x b') : P b = P b' :=
  LaurentPolynomial.ext fun m => by rw [hP, hP, h]

theorem productMap_ofId_right {A : Type u} [CommRing A] [Algebra k A] (φ : B →ₐ[k] A)
    (ε : B →ₐ[k] k) :
    Algebra.TensorProduct.productMap φ ((Algebra.ofId k A).comp ε) =
      φ.comp (Algebra.TensorProduct.productMap (AlgHom.id k B) ((Algebra.ofId k B).comp ε)) :=
  Algebra.TensorProduct.ext' fun a b => by
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.productMap_apply_tmul, map_mul,
      Algebra.ofId_apply, AlgHom.commutes, AlgHom.id_apply]

theorem productMap_ofId_left {A : Type u} [CommRing A] [Algebra k A] (φ : B →ₐ[k] A)
    (ε : B →ₐ[k] k) :
    Algebra.TensorProduct.productMap ((Algebra.ofId k A).comp ε) φ =
      φ.comp (Algebra.TensorProduct.productMap ((Algebra.ofId k B).comp ε) (AlgHom.id k B)) :=
  Algebra.TensorProduct.ext' fun a b => by
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.productMap_apply_tmul, map_mul,
      Algebra.ofId_apply, AlgHom.commutes, AlgHom.id_apply]

/-- The main theorem: a contracting cocycle has no negative Laurent terms. -/
theorem coeff_eq_zero_of_cocycle
    (hc : IsGrading k c)
    (hε : ∀ b n, ε ((c b).coeff n) = if n = 0 then ε b else 0)
    (hΔ : ∀ b d, IsHomogeneous c d b → Δ b ∈ tensorWeightSpan k c d)
    (hl : (Algebra.TensorProduct.productMap ((Algebra.ofId k B).comp ε) (AlgHom.id k B)).comp Δ =
      AlgHom.id k B)
    (hr : (Algebra.TensorProduct.productMap (AlgHom.id k B) ((Algebra.ofId k B).comp ε)).comp Δ =
      AlgHom.id k B)
    (hx : IsContracting c ε x)
    (hP : ∀ b m, (P b).coeff m = LaurentPolynomial.C ((x b).coeff m))
    (hQ : ∀ b j, IsHomogeneous c j b → Q b = AddMonoidAlgebra.single j (x b))
    (hX : ∀ b m, (X b).coeff m = AddMonoidAlgebra.single m ((x b).coeff m))
    (hcoc : ∀ b, X b = Algebra.TensorProduct.productMap P Q (Δ b)) :
    ∀ b, ∀ n < 0, (x b).coeff n = 0 := by
  set e : B →ₐ[k] LaurentPolynomial (LaurentPolynomial k) :=
    (Algebra.ofId k (LaurentPolynomial (LaurentPolynomial k))).comp ε with he
  -- the reduced bilinear form `(y₁, y₂) ↦ (P y₁ - ε y₁) (Q y₂ - ε y₂)`
  set D : B ⊗[k] B →ₗ[k] LaurentPolynomial (LaurentPolynomial k) :=
    (Algebra.TensorProduct.productMap P Q).toLinearMap -
      (Algebra.TensorProduct.productMap P e).toLinearMap -
      (Algebra.TensorProduct.productMap e Q).toLinearMap +
      (Algebra.TensorProduct.productMap e e).toLinearMap with hD
  have hDtmul : ∀ y₁ y₂, D (y₁ ⊗ₜ y₂) = (P y₁ - e y₁) * (Q y₂ - e y₂) := by
    intro y₁ y₂
    simp only [hD, LinearMap.add_apply, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
      Algebra.TensorProduct.productMap_apply_tmul]
    ring
  have hPe : (Algebra.TensorProduct.productMap P e).comp Δ = P := by
    rw [he, productMap_ofId_right, AlgHom.comp_assoc, hr, AlgHom.comp_id]
  have heQ : (Algebra.TensorProduct.productMap e Q).comp Δ = Q := by
    rw [he, productMap_ofId_left, AlgHom.comp_assoc, hl, AlgHom.comp_id]
  have hee : (Algebra.TensorProduct.productMap e e).comp Δ = e := by
    rw [he, productMap_ofId_right, AlgHom.comp_assoc, hr, AlgHom.comp_id]
  have hDΔ : ∀ b, D (Δ b) = X b - P b - Q b + e b := by
    intro b
    have h1 := congrArg (fun φ : B →ₐ[k] LaurentPolynomial (LaurentPolynomial k) => φ b) hPe
    have h2 := congrArg (fun φ : B →ₐ[k] LaurentPolynomial (LaurentPolynomial k) => φ b) heQ
    have h3 := congrArg (fun φ : B →ₐ[k] LaurentPolynomial (LaurentPolynomial k) => φ b) hee
    simp only [AlgHom.comp_apply] at h1 h2 h3
    simp only [hD, LinearMap.add_apply, LinearMap.sub_apply, AlgHom.toLinearMap_apply, h1, h2, h3,
      hcoc b]
  -- strong induction on the weight
  have key : ∀ d : ℕ, ∀ b, IsHomogeneous c d b → ∀ n < 0, (x b).coeff n = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
    intro b hb n hn
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [eq_algebraMap_of_zero hx (by exact_mod_cast hb), algebraMap_laurent_coeff,
        if_neg hn.ne]
    · have hmem : D (Δ b) ∈ polynomialPart k := by
        have hle : tensorWeightSpan k c d ≤ (polynomialPart k).comap D := by
          refine Submodule.span_le.2 ?_
          rintro w ⟨y₁, y₂, i, j, h₁, h₂, hij, rfl⟩
          change D (y₁ ⊗ₜ y₂) ∈ polynomialPart k
          rw [hDtmul]
          rcases le_or_gt i 0 with hi | hi
          · -- the first factor vanishes
            have h0 : P y₁ - e y₁ = 0 := by
              rcases hi.lt_or_eq with hi | rfl
              · have hx0 : x y₁ = x 0 := by rw [eq_zero_of_neg hx h₁ hi, map_zero]
                rw [P_eq_of_eq hP hx0, map_zero, he, AlgHom.comp_apply,
                  counit_eq_zero hε h₁ hi.ne, map_zero, sub_zero]
              · have hx0 : x y₁ = x (algebraMap k B (ε y₁)) := by
                  rw [eq_algebraMap_of_zero hx h₁, AlgHom.commutes]
                rw [P_eq_of_eq hP hx0, AlgHom.commutes, he, AlgHom.comp_apply,
                  Algebra.ofId_apply, sub_self]
            rw [h0, zero_mul]
            exact zero_mem _
          rcases le_or_gt j 0 with hj | hj
          · have h0 : Q y₂ - e y₂ = 0 := by
              rw [hQ y₂ j h₂]
              rcases hj.lt_or_eq with hj | rfl
              · rw [eq_zero_of_neg hx h₂ hj, AddMonoidAlgebra.single_zero, he, AlgHom.comp_apply,
                  counit_eq_zero hε h₂ hj.ne, map_zero, sub_zero]
              · rw [eq_algebraMap_of_zero hx h₂, he, AlgHom.comp_apply, Algebra.ofId_apply,
                  LaurentPolynomial.single_eq_C, sub_eq_zero]
                exact (LaurentPolynomial.algebraMap_apply (ε y₂)).symm
            rw [h0, mul_zero]
            exact zero_mem _
          -- both weights are positive, hence smaller than `d`
          have hid : i.toNat < d := by omega
          have hjd : j.toNat < d := by omega
          have h₁' : IsHomogeneous c (i.toNat : ℤ) y₁ := by rwa [Int.toNat_of_nonneg hi.le]
          have h₂' : IsHomogeneous c (j.toNat : ℤ) y₂ := by rwa [Int.toNat_of_nonneg hj.le]
          rw [he, AlgHom.comp_apply, AlgHom.comp_apply, counit_eq_zero hε h₁ hi.ne',
            counit_eq_zero hε h₂ hj.ne', map_zero, sub_zero, sub_zero, hQ y₂ j h₂]
          intro m n' hmn
          rw [AddMonoidAlgebra.coeff_mul_single_apply, hP, ← LaurentPolynomial.single_eq_C,
            AddMonoidAlgebra.coeff_single_mul_apply, neg_zero, zero_add]
          rcases hmn with hm | hn'
          · rw [ih i.toNat hid y₁ h₁' (m + -j) (by omega), zero_mul]
          · rw [ih j.toNat hjd y₂ h₂' n' hn', mul_zero]
        exact hle (hΔ b d hb)
      have h := hmem n n (Or.inl hn)
      rw [hDΔ b] at h
      have hXn : ((X b).coeff n).coeff n = (x b).coeff n := by
        rw [hX, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
      have hPn : ((P b).coeff n).coeff n = 0 := by
        rw [hP, LaurentPolynomial.C_apply, if_neg hn.ne]
      have hQn : ((Q b).coeff n).coeff n = 0 := by
        rw [hQ b d hb, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (by omega)]
        rfl
      have hen : ((e b).coeff n).coeff n = 0 := by
        rw [he, AlgHom.comp_apply, Algebra.ofId_apply, LaurentPolynomial.algebraMap_apply,
          LaurentPolynomial.C_apply, if_neg hn.ne]
        rfl
      rw [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_sub,
        Finsupp.add_apply, Finsupp.sub_apply, Finsupp.sub_apply, AddMonoidAlgebra.coeff_add,
        AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_sub, Finsupp.add_apply,
        Finsupp.sub_apply, Finsupp.sub_apply, hXn, hPn, hQn, hen] at h
      simpa using h
  intro b n hn
  have hb : x b = ∑ m ∈ (c b).coeff.support, x ((c b).coeff m) := by
    conv_lhs => rw [← hc.sum_coeff b]
    rw [Finsupp.sum, map_sum]
  rw [hb, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  have hm : IsHomogeneous c m ((c b).coeff m) := hc.coeff_coeff b m
  rcases lt_or_ge m 0 with hm0 | hm0
  · rw [eq_zero_of_neg hx hm hm0]
    rfl
  · exact key m.toNat _ (by rwa [Int.toNat_of_nonneg hm0]) n hn

/-- A comultiplication intertwining the grading with the product grading respects total
weight. -/
theorem comul_mem_tensorWeightSpan (hc : IsGrading k c)
    (φL φR : B →ₐ[k] LaurentPolynomial (B ⊗[k] B))
    (hL : ∀ b n, (φL b).coeff n = (c b).coeff n ⊗ₜ (1 : B))
    (hR : ∀ b n, (φR b).coeff n = (1 : B) ⊗ₜ (c b).coeff n)
    (hG : ∀ b n, (Algebra.TensorProduct.productMap φL φR (Δ b)).coeff n = Δ ((c b).coeff n))
    (b : B) (d : ℤ) (hb : IsHomogeneous c d b) : Δ b ∈ tensorWeightSpan k c d := by
  classical
  have key : ∀ w : B ⊗[k] B, ∀ d,
      (Algebra.TensorProduct.productMap φL φR w).coeff d ∈ tensorWeightSpan k c d := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul y₁ y₂ =>
      intro d
      rw [Algebra.TensorProduct.productMap_apply_tmul, AddMonoidAlgebra.coeff_mul]
      simp only [Finsupp.sum]
      refine Submodule.sum_mem _ fun m _ => Submodule.sum_mem _ fun n _ => ?_
      split_ifs with h
      · rw [hL, hR, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        exact Submodule.subset_span ⟨_, _, m, n, hc.coeff_coeff y₁ m, hc.coeff_coeff y₂ n, h, rfl⟩
      · exact zero_mem _
    | add w₁ w₂ h₁ h₂ =>
      intro d
      rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      exact add_mem (h₁ d) (h₂ d)
  have h := key (Δ b) d
  rwa [hG, hb.coeff_self] at h

variable (k) in
/-- The constant coefficient in the inner variable, coefficientwise. -/
def innerCoeffZeroFun (F : LaurentPolynomial (LaurentPolynomial k)) : LaurentPolynomial k :=
  AddMonoidAlgebra.ofCoeff (F.coeff.mapRange (fun f => f.coeff 0) rfl)

theorem coeff_innerCoeffZeroFun (F : LaurentPolynomial (LaurentPolynomial k)) (m : ℤ) :
    (innerCoeffZeroFun k F).coeff m = (F.coeff m).coeff 0 :=
  rfl

variable (k) in
/-- The constant coefficient in the inner variable, as a linear map. -/
def innerCoeffZero : LaurentPolynomial (LaurentPolynomial k) →ₗ[k] LaurentPolynomial k where
  toFun := innerCoeffZeroFun k
  map_add' F G := LaurentPolynomial.ext fun m => by
    rw [coeff_innerCoeffZeroFun, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      coeff_innerCoeffZeroFun, coeff_innerCoeffZeroFun]
  map_smul' r F := LaurentPolynomial.ext fun m => by
    rw [coeff_innerCoeffZeroFun, RingHom.id_apply, AddMonoidAlgebra.coeff_smul_apply,
      AddMonoidAlgebra.coeff_smul_apply, AddMonoidAlgebra.coeff_smul_apply,
      coeff_innerCoeffZeroFun]

theorem coeff_innerCoeffZero (F : LaurentPolynomial (LaurentPolynomial k)) (m : ℤ) :
    (innerCoeffZero k F).coeff m = (F.coeff m).coeff 0 :=
  rfl

/-- Setting the inner variable of the cocycle identity to `0` gives the fixed-point identity
`u = x(s) · (s · u)` for the constant coefficient `u` of `x`. -/
theorem algebraMap_eq_of_cocycle (hc : IsGrading k c)
    (u : B →ₐ[k] k) (hu : ∀ b, u b = (x b).coeff 0) (Qu : B →ₐ[k] LaurentPolynomial k)
    (hQu : ∀ b j, IsHomogeneous c j b → Qu b = AddMonoidAlgebra.single j (u b))
    (hP : ∀ b m, (P b).coeff m = LaurentPolynomial.C ((x b).coeff m))
    (hQ : ∀ b j, IsHomogeneous c j b → Q b = AddMonoidAlgebra.single j (x b))
    (hX : ∀ b m, (X b).coeff m = AddMonoidAlgebra.single m ((x b).coeff m))
    (hcoc : ∀ b, X b = Algebra.TensorProduct.productMap P Q (Δ b)) (b : B) :
    algebraMap k (LaurentPolynomial k) (u b) = Algebra.TensorProduct.productMap x Qu (Δ b) := by
  have h1 : innerCoeffZero k (X b) = algebraMap k (LaurentPolynomial k) (u b) := by
    refine LaurentPolynomial.ext fun m => ?_
    rw [coeff_innerCoeffZero, hX, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      algebraMap_laurent_coeff, hu]
    by_cases hm : m = 0
    · subst hm
      simp
    · rw [if_neg hm, if_neg hm]
  have h2 : innerCoeffZero k ∘ₗ (Algebra.TensorProduct.productMap P Q).toLinearMap =
      (Algebra.TensorProduct.productMap x Qu).toLinearMap := by
    refine TensorProduct.ext' fun y₁ y₂ => ?_
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      Algebra.TensorProduct.productMap_apply_tmul]
    have hy₂ : y₂ = ∑ j ∈ (c y₂).coeff.support, (c y₂).coeff j := hc.sum_coeff y₂ |>.symm
    rw [hy₂, map_sum, map_sum, Finset.mul_sum, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj : IsHomogeneous c j ((c y₂).coeff j) := hc.coeff_coeff y₂ j
    rw [hQ _ j hj, hQu _ j hj]
    refine LaurentPolynomial.ext fun m => ?_
    rw [coeff_innerCoeffZero, AddMonoidAlgebra.coeff_mul_single_apply,
      AddMonoidAlgebra.coeff_mul_single_apply, hP, ← LaurentPolynomial.single_eq_C,
      AddMonoidAlgebra.coeff_single_mul_apply, neg_zero, zero_add, hu]
  rw [← h1, hcoc b]
  exact congrArg (fun φ : B ⊗[k] B →ₗ[k] LaurentPolynomial k => φ (Δ b)) h2

end Core

end GradedCocycle

end Langlands.CommutativeAlgebra
