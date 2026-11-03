import Langlands.AlgebraicGeometry.TensorLinearKernel
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Finite linear models of kernels between finite projective modules -/

noncomputable section

universe u v w

open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Picard.LineHom

open FiniteLinearEquations

variable {R : Type u} [CommRing R]

/-- Every finite projective module is a retract of a finite coordinate module. -/
lemma exists_retract_fin (P : Type u) [AddCommGroup P] [Module R P] [Module.Finite R P]
    [Module.Projective R P] :
    ∃ (n : ℕ) (i : P →ₗ[R] (Fin n → R)) (π : (Fin n → R) →ₗ[R] P),
      π ∘ₗ i = LinearMap.id := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R P
  obtain ⟨i, hi⟩ := Module.projective_lifting_property π LinearMap.id hπ
  exact ⟨n, i, π, hi⟩

/-- Coordinates on a product of two finite coordinate modules. -/
def prodCoordinates (n₁ n₀ : ℕ) :
    ((Fin n₁ → R) × (Fin n₀ → R)) ≃ₗ[R] (Fin (n₁ + n₀) → R) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin n₁) (Fin n₀) R R).symm ≪≫ₗ
    LinearEquiv.funCongrLeft R R finSumFinEquiv.symm

section Replacement

variable {P Q F₀ F₁ : Type u} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
  [AddCommGroup F₀] [Module R F₀] [AddCommGroup F₁] [Module R F₁]

/-- The replacement of `f` by a map out of the module `F₀` retracting onto `P`:
its first component is `f` read through the retraction `π₀` and the section `i₁`,
its second the complementary idempotent `1 - i₀ π₀`. -/
def replacement (f : P →ₗ[R] Q) (i₀ : P →ₗ[R] F₀) (π₀ : F₀ →ₗ[R] P)
    (i₁ : Q →ₗ[R] F₁) : F₀ →ₗ[R] F₁ × F₀ :=
  LinearMap.prod (i₁ ∘ₗ f ∘ₗ π₀) (LinearMap.id - i₀ ∘ₗ π₀)

variable {i₀ : P →ₗ[R] F₀} {π₀ : F₀ →ₗ[R] P} {i₁ : Q →ₗ[R] F₁} {π₁ : F₁ →ₗ[R] Q}

lemma lTensor_retract (h : π₀ ∘ₗ i₀ = LinearMap.id)
    {A : Type v} [AddCommGroup A] [Module R A] (x : A ⊗[R] P) :
    π₀.lTensor A (i₀.lTensor A x) = x := by
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h, LinearMap.lTensor_id,
    LinearMap.id_apply]

/-- After any coefficient change, the replacement kills a tensor exactly when `f`
kills its retraction and the tensor is fixed by the idempotent `i₀ π₀`. -/
lemma lTensor_replacement_eq_zero_iff (f : P →ₗ[R] Q) (h₁ : π₁ ∘ₗ i₁ = LinearMap.id)
    {A : Type v} [AddCommGroup A] [Module R A] (z : A ⊗[R] F₀) :
    (replacement f i₀ π₀ i₁).lTensor A z = 0 ↔
      f.lTensor A (π₀.lTensor A z) = 0 ∧ i₀.lTensor A (π₀.lTensor A z) = z := by
  have hprod : replacement f i₀ π₀ i₁ =
      LinearMap.inl R F₁ F₀ ∘ₗ (i₁ ∘ₗ f ∘ₗ π₀) +
        LinearMap.inr R F₁ F₀ ∘ₗ (LinearMap.id - i₀ ∘ₗ π₀) := by
    ext x <;> simp [replacement]
  have hfst : (i₁ ∘ₗ f ∘ₗ π₀).lTensor A z = i₁.lTensor A (f.lTensor A (π₀.lTensor A z)) := by
    simp only [LinearMap.lTensor_comp, LinearMap.comp_apply]
  have hsnd : (LinearMap.id - i₀ ∘ₗ π₀).lTensor A z = z - i₀.lTensor A (π₀.lTensor A z) := by
    simp only [LinearMap.lTensor_sub, LinearMap.lTensor_id, LinearMap.lTensor_comp,
      LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
  constructor
  · intro hz
    have h1 := congrArg ((LinearMap.fst R F₁ F₀).lTensor A) hz
    have h2 := congrArg ((LinearMap.snd R F₁ F₀).lTensor A) hz
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, replacement, LinearMap.fst_prod,
      map_zero, hfst] at h1
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, replacement, LinearMap.snd_prod,
      map_zero, hsnd, sub_eq_zero] at h2
    refine ⟨?_, h2.symm⟩
    have := congrArg (π₁.lTensor A) h1
    rwa [lTensor_retract h₁, map_zero] at this
  · rintro ⟨h1, h2⟩
    have hg : (i₁ ∘ₗ f ∘ₗ π₀).lTensor A z = 0 := by rw [hfst, h1, map_zero]
    have hh : (LinearMap.id - i₀ ∘ₗ π₀).lTensor A z = 0 := by rw [hsnd, h2, sub_self]
    rw [hprod, LinearMap.lTensor_add, LinearMap.add_apply,
      LinearMap.lTensor_comp_apply (M := A) (g := LinearMap.inl R F₁ F₀),
      LinearMap.lTensor_comp_apply (M := A) (g := LinearMap.inr R F₁ F₀), hg, hh, map_zero,
      map_zero, add_zero]

/-- The tensor kernels of the replacement and of `f` agree, via the retraction
`π₀` and the section `i₀`, after every coefficient change. -/
def replacementKernelEquiv (f : P →ₗ[R] Q) (h₀ : π₀ ∘ₗ i₀ = LinearMap.id)
    (h₁ : π₁ ∘ₗ i₁ = LinearMap.id) (A : Type v) [AddCommGroup A] [Module R A] :
    (TensorProduct.map (LinearMap.id : A →ₗ[R] A) (replacement f i₀ π₀ i₁)).ker ≃
      (TensorProduct.map (LinearMap.id : A →ₗ[R] A) f).ker where
  toFun z := ⟨π₀.lTensor A z.val, LinearMap.mem_ker.2
    ((lTensor_replacement_eq_zero_iff f h₁ z.val).1 (LinearMap.mem_ker.1 z.property)).1⟩
  invFun x := ⟨i₀.lTensor A x.val, LinearMap.mem_ker.2
    ((lTensor_replacement_eq_zero_iff f h₁ _).2
      ⟨by rw [lTensor_retract h₀]; exact LinearMap.mem_ker.1 x.property,
        by rw [lTensor_retract h₀]⟩)⟩
  left_inv z := Subtype.ext
    ((lTensor_replacement_eq_zero_iff f h₁ z.val).1 (LinearMap.mem_ker.1 z.property)).2
  right_inv x := Subtype.ext (lTensor_retract h₀ x.val)

/-- The inverse comparison commutes with coefficient changes. -/
lemma replacementKernelEquiv_symm_mapKernel (f : P →ₗ[R] Q) (h₀ : π₀ ∘ₗ i₀ = LinearMap.id)
    (h₁ : π₁ ∘ₗ i₁ = LinearMap.id)
    {A : Type v} [AddCommGroup A] [Module R A] {B : Type w} [AddCommGroup B] [Module R B]
    (q : A →ₗ[R] B) (z : (TensorProduct.map (LinearMap.id : A →ₗ[R] A) f).ker) :
    (replacementKernelEquiv f h₀ h₁ B).symm (TensorKernel.mapKernel f q z) =
      TensorKernel.mapKernel (replacement f i₀ π₀ i₁) q
        ((replacementKernelEquiv f h₀ h₁ A).symm z) := by
  apply Subtype.ext
  change (i₀.lTensor B ∘ₗ q.rTensor P) z.val = (q.rTensor F₀ ∘ₗ i₀.lTensor A) z.val
  rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]

end Replacement

/-- For a map between finite projective modules, the kernels after all coefficient
changes are, naturally in the coefficient algebra, the solutions of one finite
homogeneous linear system. -/
theorem exists_kernel_solutions_model {R : Type u} [CommRing R]
    {P Q : Type u} [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Projective R Q]
    (f : P →ₗ[R] Q) :
    ∃ (m n : ℕ) (a : Fin m → Fin n → R)
      (E : ∀ (S : Type u) [CommRing S] [Algebra R S],
        (TensorProduct.map (LinearMap.id : S →ₗ[R] S) f).ker ≃ Solutions a S),
      ∀ (S S' : Type u) [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
        (q : S →ₐ[R] S') (z : (TensorProduct.map (LinearMap.id : S →ₗ[R] S) f).ker),
        E S' (TensorKernel.mapKernel f q.toLinearMap z) = mapSolutions a q (E S z) := by
  obtain ⟨n₀, i₀, π₀, h₀⟩ := exists_retract_fin (R := R) P
  obtain ⟨n₁, i₁, π₁, h₁⟩ := exists_retract_fin (R := R) Q
  refine ⟨n₁ + n₀, n₀,
    TensorKernel.matrix (replacement f i₀ π₀ i₁) (LinearEquiv.refl R _) (prodCoordinates n₁ n₀),
    fun S ↦ (replacementKernelEquiv f h₀ h₁ S).symm.trans
      (TensorKernel.kernelEquiv (replacement f i₀ π₀ i₁) (LinearEquiv.refl R _)
        (prodCoordinates n₁ n₀) S), ?_⟩
  intro S S' _ _ _ _ q z
  simp only [Equiv.trans_apply]
  rw [replacementKernelEquiv_symm_mapKernel, TensorKernel.kernelEquiv_naturality]

end Langlands.AlgebraicGeometry.Picard.LineHom
