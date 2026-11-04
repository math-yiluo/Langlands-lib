import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-! # The grading defined by a bialgebra map to a group algebra

A bialgebra map `π : A → K[N]` to the group algebra of a commutative group makes `A` a
right `K[N]`-comodule algebra, `a ↦ ∑ a₁ ⊗ π a₂`. Its homogeneous components `grade π n`
form an `N`-grading of `A`. -/

noncomputable section

universe u v w

open TensorProduct Coalgebra

namespace Langlands.GroupAlgebraCoaction

section Coalgebra

variable {K : Type u} [CommRing K] {A : Type v} [AddCommGroup A] [Module K A] [Coalgebra K A]

/-- The right action `a ↦ ∑ f(a₂) a₁` of a linear form `f` on a coalgebra. -/
def ract (f : A →ₗ[K] K) : A →ₗ[K] A :=
  (TensorProduct.rid K A).toLinearMap ∘ₗ f.lTensor A ∘ₗ comul

/-- The left action `a ↦ ∑ f(a₁) a₂` of a linear form `f` on a coalgebra. -/
def lact (f : A →ₗ[K] K) : A →ₗ[K] A :=
  (TensorProduct.lid K A).toLinearMap ∘ₗ f.rTensor A ∘ₗ comul

/-- The convolution product `a ↦ ∑ f(a₁) g(a₂)` of two linear forms. -/
def conv (f g : A →ₗ[K] K) : A →ₗ[K] K :=
  (TensorProduct.lid K K).toLinearMap ∘ₗ TensorProduct.map f g ∘ₗ comul

theorem ract_apply {ι : Type*} {a : A} (𝓡 : Repr K a ι) (f : A →ₗ[K] K) :
    ract f a = ∑ i ∈ 𝓡.index, f (𝓡.right i) • 𝓡.left i := by
  simp [ract, ← 𝓡.eq, map_sum]

theorem lact_apply {ι : Type*} {a : A} (𝓡 : Repr K a ι) (f : A →ₗ[K] K) :
    lact f a = ∑ i ∈ 𝓡.index, f (𝓡.left i) • 𝓡.right i := by
  simp [lact, ← 𝓡.eq, map_sum]

theorem conv_apply {ι : Type*} {a : A} (𝓡 : Repr K a ι) (f g : A →ₗ[K] K) :
    conv f g a = ∑ i ∈ 𝓡.index, f (𝓡.left i) * g (𝓡.right i) := by
  simp [conv, ← 𝓡.eq, map_sum]

theorem ract_ract (f g : A →ₗ[K] K) (a : A) : ract f (ract g a) = ract (conv f g) a := by
  let 𝓡 := Repr.arbitrary K a
  have h := sum_tmul_tmul_eq 𝓡 (fun i => Repr.arbitrary K (𝓡.left i))
    (fun i => Repr.arbitrary K (𝓡.right i))
  apply_fun (TensorProduct.rid K A).toLinearMap ∘ₗ
    ((TensorProduct.lid K K).toLinearMap ∘ₗ TensorProduct.map f g).lTensor A at h
  simp only [LinearMap.coe_comp, Function.comp_apply, map_sum, LinearMap.lTensor_tmul,
    TensorProduct.map_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, smul_eq_mul,
    TensorProduct.rid_tmul] at h
  rw [ract_apply 𝓡, map_sum, ract_apply 𝓡]
  simp only [map_smul, ract_apply (Repr.arbitrary K (𝓡.left _)), conv_apply (Repr.arbitrary K _),
    Finset.smul_sum, smul_smul, Finset.sum_smul]
  simp only [mul_comm (g _)]
  exact h

theorem lTensor_ract_comul (f : A →ₗ[K] K) (a : A) :
    (ract f).lTensor A (comul a) = comul (ract f a) := by
  let 𝓡 := Repr.arbitrary K a
  have h := sum_tmul_tmul_eq 𝓡 (fun i => Repr.arbitrary K (𝓡.left i))
    (fun i => Repr.arbitrary K (𝓡.right i))
  apply_fun (TensorProduct.rid K (A ⊗[K] A)).toLinearMap ∘ₗ f.lTensor (A ⊗[K] A) ∘ₗ
    (TensorProduct.assoc K A A A).symm.toLinearMap at h
  simp only [LinearMap.coe_comp, Function.comp_apply, map_sum, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul, TensorProduct.rid_tmul] at h
  rw [← 𝓡.eq, map_sum, ract_apply 𝓡, map_sum]
  simp only [LinearMap.lTensor_tmul, ract_apply (Repr.arbitrary K (𝓡.right _)), map_smul,
    ← (Repr.arbitrary K (𝓡.left _)).eq, Finset.smul_sum, TensorProduct.tmul_sum,
    TensorProduct.tmul_smul]
  exact h.symm

theorem rTensor_lact_comul (f : A →ₗ[K] K) (a : A) :
    (lact f).rTensor A (comul a) = comul (lact f a) := by
  let 𝓡 := Repr.arbitrary K a
  have h := sum_tmul_tmul_eq 𝓡 (fun i => Repr.arbitrary K (𝓡.left i))
    (fun i => Repr.arbitrary K (𝓡.right i))
  apply_fun (TensorProduct.lid K (A ⊗[K] A)).toLinearMap ∘ₗ f.rTensor (A ⊗[K] A) at h
  simp only [LinearMap.coe_comp, Function.comp_apply, map_sum, LinearMap.rTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul] at h
  rw [← 𝓡.eq, map_sum, lact_apply 𝓡, map_sum]
  simp only [LinearMap.rTensor_tmul, lact_apply (Repr.arbitrary K (𝓡.left _)), map_smul,
    ← (Repr.arbitrary K (𝓡.right _)).eq, Finset.smul_sum, TensorProduct.sum_tmul,
    TensorProduct.smul_tmul']
  simp only [TensorProduct.smul_tmul'] at h
  exact h

theorem counit_ract (f : A →ₗ[K] K) (a : A) : counit (ract f a) = f a := by
  let 𝓡 := Repr.arbitrary K a
  rw [ract_apply 𝓡, map_sum]
  simp only [map_smul, smul_eq_mul]
  conv_rhs => rw [← sum_counit_smul 𝓡]
  simp [map_sum, mul_comm]

theorem ract_counit (a : A) : ract (counit : A →ₗ[K] K) a = a := by
  simp [ract]

end Coalgebra

section GroupAlgebra

variable {K : Type u} [CommRing K] {N : Type w} [AddCommGroup N]

/-- The `n`-th coefficient of an element of the group algebra `K[N]`, as a linear form. -/
def lcoeff (n : N) : AddMonoidAlgebra K N →ₗ[K] K :=
  Finsupp.lapply n ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

omit [AddCommGroup N] in
@[simp] theorem lcoeff_apply (n : N) (p : AddMonoidAlgebra K N) : lcoeff n p = p.coeff n := rfl

omit [AddCommGroup N] in
open Classical in
theorem conv_lcoeff (m n : N) :
    conv (lcoeff m : AddMonoidAlgebra K N →ₗ[K] K) (lcoeff n) =
      if m = n then lcoeff n else 0 := by
  classical
  ext k
  simp only [conv, LinearMap.coe_comp, Function.comp_apply]
  split_ifs with h
  · subst h
    simp [Finsupp.single_apply]
    intros; simp_all
  · simp [Finsupp.single_apply]
    intros; simp_all

omit [AddCommGroup N] in
theorem counit_eq_sum (p : AddMonoidAlgebra K N) :
    counit (R := K) p = p.coeff.sum fun _ b => b := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    rw [map_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index'] <;> simp
  | single n r => simp

variable {A : Type v} [CommRing A] [Algebra K A]

theorem coeff_scalarTensorEquiv (t : A ⊗[K] AddMonoidAlgebra K N) (n : N) :
    (AddMonoidAlgebra.scalarTensorEquiv K A t).coeff n =
      TensorProduct.rid K A ((lcoeff n).lTensor A t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a p => simp [Algebra.smul_def, Algebra.commutes]
  | add x y hx hy => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hy]

theorem sum_scalarTensorEquiv (t : A ⊗[K] AddMonoidAlgebra K N) :
    ((AddMonoidAlgebra.scalarTensorEquiv K A t).coeff.sum fun _ b => b) =
      TensorProduct.rid K A ((counit : AddMonoidAlgebra K N →ₗ[K] K).lTensor A t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a p =>
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq =>
      rw [TensorProduct.tmul_add, map_add, map_add, map_add, AddMonoidAlgebra.coeff_add,
        Finsupp.sum_add_index', hp, hq] <;> simp
    | single n r => simp [Algebra.smul_def, mul_comm]
  | add x y hx hy =>
    rw [map_add, map_add, map_add, AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index', hx, hy]
      <;> simp

end GroupAlgebra

section Bialgebra

variable {K : Type u} [CommRing K] {N : Type w} [AddCommGroup N]
variable {A : Type v} [CommRing A] [Bialgebra K A] (π : A →ₐc[K] AddMonoidAlgebra K N)

/-- The linear form `a ↦ (π a)ₙ`. -/
def coeffForm (n : N) : A →ₗ[K] K := lcoeff n ∘ₗ (π : A →ₗ[K] AddMonoidAlgebra K N)

@[simp] theorem coeffForm_apply (n : N) (a : A) : coeffForm π n a = (π a).coeff n := rfl

/-- The `n`-th homogeneous component `a ↦ ∑ (π a₂)ₙ • a₁`. -/
def proj (n : N) : A →ₗ[K] A := ract (coeffForm π n)

open Classical in
theorem conv_coeffForm (m n : N) :
    conv (coeffForm π m) (coeffForm π n) = if m = n then coeffForm π n else 0 := by
  have : conv (coeffForm π m) (coeffForm π n) =
      conv (lcoeff m : AddMonoidAlgebra K N →ₗ[K] K) (lcoeff n) ∘ₗ
        (π : A →ₗ[K] AddMonoidAlgebra K N) := by
    ext a
    simp only [conv, coeffForm, LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_comp]
    congr 2
    exact CoalgHomClass.map_comp_comul_apply π a
  rw [this, conv_lcoeff]
  split_ifs <;> rfl

open Classical in
theorem proj_proj (m n : N) (a : A) :
    proj π m (proj π n a) = if m = n then proj π n a else 0 := by
  rw [proj, proj, ract_ract, conv_coeffForm]
  split_ifs
  · rfl
  · simp [ract]

theorem counit_proj (n : N) (a : A) : counit (R := K) (proj π n a) = (π a).coeff n :=
  counit_ract _ a

theorem lTensor_proj_comul (n : N) (a : A) :
    (proj π n).lTensor A (comul a) = comul (proj π n a) :=
  lTensor_ract_comul _ a

/-- The coaction `A → A ⊗ K[N] ≅ A[N]`, `a ↦ ∑ a₁ ⊗ π a₂`, of `K[N]` on `A` through `π`. -/
def coaction : A →ₐ[K] AddMonoidAlgebra A N :=
  ((AddMonoidAlgebra.scalarTensorEquiv K A (M := N)).toAlgHom.restrictScalars K).comp
    ((Algebra.TensorProduct.map (AlgHom.id K A) (π : A →ₐ[K] AddMonoidAlgebra K N)).comp
      (Bialgebra.comulAlgHom K A))

theorem coaction_apply (a : A) :
    coaction π a = AddMonoidAlgebra.scalarTensorEquiv K A
      ((π : A →ₗ[K] AddMonoidAlgebra K N).lTensor A (comul a)) :=
  rfl

theorem coeff_coaction (a : A) (n : N) : (coaction π a).coeff n = proj π n a := by
  rw [coaction_apply, coeff_scalarTensorEquiv, proj, ract, coeffForm, LinearMap.lTensor_comp]
  rfl

theorem sum_coeff_coaction (a : A) : ((coaction π a).coeff.sum fun _ b => b) = a := by
  rw [coaction_apply, sum_scalarTensorEquiv, ← LinearMap.comp_apply (LinearMap.lTensor A _),
    ← LinearMap.lTensor_comp]
  simp

theorem sum_proj (a : A) : ∑ n ∈ (coaction π a).coeff.support, proj π n a = a := by
  conv_rhs => rw [← sum_coeff_coaction π a]
  simp [Finsupp.sum, coeff_coaction]

/-- The `n`-th homogeneous component of the grading defined by `π`. -/
def grade (n : N) : Submodule K A :=
  LinearMap.eqLocus (coaction π).toLinearMap
    ((AddMonoidAlgebra.lsingle n : A →ₗ[K] AddMonoidAlgebra A N))

theorem mem_grade_iff {n : N} {a : A} :
    a ∈ grade π n ↔ coaction π a = AddMonoidAlgebra.single n a :=
  Iff.rfl

open Classical in
theorem proj_of_mem {n : N} {a : A} (ha : a ∈ grade π n) (m : N) :
    proj π m a = if m = n then a else 0 := by
  classical
  rw [← coeff_coaction, (mem_grade_iff π).mp ha, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  rcases eq_or_ne m n with rfl | h
  · simp
  · simp [h, Ne.symm h]

theorem proj_self_of_mem {n : N} {a : A} (ha : a ∈ grade π n) : proj π n a = a := by
  simp [proj_of_mem π ha]

theorem proj_mem (n : N) (a : A) : proj π n a ∈ grade π n := by
  classical
  rw [mem_grade_iff]
  ext m
  rw [coeff_coaction, proj_proj, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rcases eq_or_ne m n with rfl | h
  · simp
  · simp [h, Ne.symm h]

theorem one_mem_grade_zero : (1 : A) ∈ grade π 0 := by
  rw [mem_grade_iff, map_one, AddMonoidAlgebra.one_def]

theorem mul_mem_grade {m n : N} {a b : A} (ha : a ∈ grade π m) (hb : b ∈ grade π n) :
    a * b ∈ grade π (m + n) := by
  rw [mem_grade_iff] at *
  rw [map_mul, ha, hb, AddMonoidAlgebra.single_mul_single]

theorem proj_mul_of_mem (n : N) {j : N} (a : A) {b : A} (hb : b ∈ grade π j) :
    proj π n (a * b) = proj π (n - j) a * b := by
  rw [← coeff_coaction, map_mul, (mem_grade_iff π).mp hb, AddMonoidAlgebra.coeff_mul_single_apply,
    coeff_coaction, sub_eq_add_neg]

theorem comul_of_mem {n : N} {a : A} (ha : a ∈ grade π n) :
    comul a = (proj π n).lTensor A (comul a) := by
  rw [lTensor_proj_comul, proj_self_of_mem π ha]

/-- The inverse of a unit of degree `n` has degree `-n`. -/
theorem inv_mem_grade {n : N} (u : Aˣ) (hu : (u : A) ∈ grade π n) :
    ((u⁻¹ : Aˣ) : A) ∈ grade π (-n) := by
  rw [mem_grade_iff] at *
  have h1 : coaction π u * AddMonoidAlgebra.single (-n) ((u⁻¹ : Aˣ) : A) = 1 := by
    rw [hu, AddMonoidAlgebra.single_mul_single, add_neg_cancel, u.mul_inv,
      AddMonoidAlgebra.one_def]
  have h2 : coaction π ((u⁻¹ : Aˣ) : A) * coaction π u = 1 := by
    rw [← map_mul, u.inv_mul, map_one]
  calc coaction π ((u⁻¹ : Aˣ) : A)
      = coaction π ((u⁻¹ : Aˣ) : A) *
          (coaction π u * AddMonoidAlgebra.single (-n) ((u⁻¹ : Aˣ) : A)) := by rw [h1, mul_one]
    _ = AddMonoidAlgebra.single (-n) ((u⁻¹ : Aˣ) : A) := by rw [← mul_assoc, h2, one_mul]

section Central

/-- `π` is central: the left and right coactions of `K[N]` on `A` through `π` agree. Geometrically,
the subgroup defined by `π` is central. -/
def IsCentral : Prop :=
  ∀ a : A, (π : A →ₗ[K] AddMonoidAlgebra K N).rTensor A (comul a) =
    TensorProduct.comm K A _ ((π : A →ₗ[K] AddMonoidAlgebra K N).lTensor A (comul a))

variable {π}

theorem IsCentral.lact_coeffForm (hπ : IsCentral π) (n : N) (a : A) :
    lact (coeffForm π n) a = proj π n a := by
  let 𝓡 := Repr.arbitrary K a
  have h := hπ a
  apply_fun (TensorProduct.lid K A).toLinearMap ∘ₗ (lcoeff n).rTensor A at h
  rw [← 𝓡.eq] at h
  simp only [LinearMap.coe_comp, Function.comp_apply, map_sum, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, TensorProduct.comm_tmul, LinearEquiv.coe_coe,
    TensorProduct.lid_tmul] at h
  rw [proj, ract_apply 𝓡, lact_apply 𝓡]
  exact h

theorem IsCentral.rTensor_proj_comul (hπ : IsCentral π) (n : N) (a : A) :
    (proj π n).rTensor A (comul a) = comul (proj π n a) := by
  have : proj π n = lact (coeffForm π n) := LinearMap.ext fun b => (hπ.lact_coeffForm n b).symm
  rw [this, rTensor_lact_comul]

/-- For a central `π`, the comultiplication maps the component of degree `n` into
`A_n ⊗ A_n`. -/
theorem IsCentral.comul_of_mem (hπ : IsCentral π) {n : N} {a : A} (ha : a ∈ grade π n) :
    comul a = TensorProduct.map (proj π n) (proj π n) (comul a) := by
  rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, lTensor_proj_comul,
    hπ.rTensor_proj_comul, proj_self_of_mem π (proj_mem π n a), proj_self_of_mem π ha]

end Central

end Bialgebra

section Hopf

variable {K : Type u} [CommRing K] {N : Type w} [AddCommGroup N]
variable {A : Type v} [CommRing A] [HopfAlgebra K A] (π : A →ₐc[K] AddMonoidAlgebra K N)

/-- The grading defined by `π` is strong in degree `n` as soon as there is an element of
degree `n` with counit one: `1` is a sum of products of elements of degrees `-n` and `n`. -/
theorem one_mem_grade_neg_mul_grade {n : N} {a : A} (ha : a ∈ grade π n)
    (h1 : counit (R := K) a = 1) : (1 : A) ∈ grade π (-n) * grade π n := by
  have key : ∀ t : A ⊗[K] A,
      proj π 0 (LinearMap.mul' K A (TensorProduct.map (HopfAlgebra.antipode K) (proj π n) t)) ∈
        grade π (-n) * grade π n := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      rw [TensorProduct.map_tmul, LinearMap.mul'_apply, proj_mul_of_mem π 0 _ (proj_mem π n y),
        zero_sub]
      exact Submodule.mul_mem_mul (proj_mem π _ _) (proj_mem π n y)
    | add x y hx hy => rw [map_add, map_add, map_add]; exact add_mem hx hy
  have h := key (comul a)
  rwa [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, ← comul_of_mem π ha,
    HopfAlgebra.mul_antipode_rTensor_comul_apply, h1, map_one,
    proj_self_of_mem π (one_mem_grade_zero π)] at h

end Hopf

end Langlands.GroupAlgebraCoaction
