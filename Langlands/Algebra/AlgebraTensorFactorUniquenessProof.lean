import Langlands.Algebra.AlgebraTensorSimpleModuleStatements
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas

open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraTensorUniqueness

universe uK uA uV uY uW uZ

variable {K : Type uK} [Field K] {A : Type uA} [Ring A] [Algebra K A]
  {V : Type uV} {Y : Type uY} {W : Type uW} {Z : Type uZ}
  [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower K A V]
  [AddCommGroup Y] [Module K Y]
  [AddCommGroup W] [Module K W] [Module A W] [IsScalarTower K A W]
  [AddCommGroup Z] [Module K Z]

/-- An intertwining tensor equivalence detects an isomorphism of simple left factors. -/
theorem left_factor [IsSimpleModule A V] [IsSimpleModule A W] [Nontrivial Y]
    (e : V ⊗[K] Y ≃ₗ[K] W ⊗[K] Z)
    (he : ∀ (a : A) (t : V ⊗[K] Y), e (a • t) = a • e t) :
    Nonempty (V ≃ₗ[A] W) := by
  classical
  have := IsSimpleModule.nontrivial A V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hy
  have hxy : v ⊗ₜ[K] y ≠ 0 := by
    intro h
    have := congrArg (fun t => TensorProduct.rid K V (φ.lTensor V t)) h
    simp [hφ] at this
    exact hv this
  have ht : e (v ⊗ₜ[K] y) ≠ 0 := by
    intro h
    exact hxy (e.injective (by simpa using h))
  let b := Module.Basis.ofVectorSpace K Z
  let c := TensorProduct.equivFinsuppOfBasisRight (M := W) b
  have hc : c (e (v ⊗ₜ[K] y)) ≠ 0 := by
    intro h
    exact ht (c.injective (by simpa using h))
  obtain ⟨i, hi⟩ : ∃ i, c (e (v ⊗ₜ[K] y)) i ≠ 0 := by
    by_contra! h
    exact hc (Finsupp.ext h)
  let p : W ⊗[K] Z →ₗ[A] W :=
    { toFun := fun t => c t i
      map_add' := by intro s t; simp
      map_smul' := by
        intro a t
        induction t with
        | tmul w z =>
          simp only [c, TensorProduct.smul_tmul',
            TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
          exact smul_comm _ _ _
        | add s t hs ht =>
          simp only [map_add, Finsupp.add_apply, smul_add, hs, ht] }
  let j : V →ₗ[A] V ⊗[K] Y :=
    { toFun := fun x => x ⊗ₜ[K] y
      map_add' := fun x x' => TensorProduct.add_tmul x x' y
      map_smul' := fun a x => (TensorProduct.smul_tmul' a x y).symm }
  let eA : V ⊗[K] Y →ₗ[A] W ⊗[K] Z :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := he }
  let f := p.comp (eA.comp j)
  have hf : f ≠ 0 := by
    intro h
    exact hi (congrArg (fun g : V →ₗ[A] W => g v) h)
  exact ⟨LinearEquiv.ofBijective f (LinearMap.bijective_of_ne_zero hf)⟩

section ExternalAction

universe uB
variable {B : Type uB} [Ring B] [Algebra K B]
  [Module B Y] [IsScalarTower K B Y]

theorem left_action (a : A) (t : V ⊗[K] Y) :
    ((Module.endTensorEndAlgHom (R := K) (S := K) (A := K)).comp
      (Algebra.TensorProduct.map (Algebra.lsmul K K V) (Algebra.lsmul K K Y)))
      (a ⊗ₜ[K] (1 : B)) t = a • t := by
  induction t with
  | tmul v y => simp [Module.endTensorEndAlgHom_apply, TensorProduct.smul_tmul']
  | add s t hs ht => simp only [map_add, smul_add, hs, ht]

theorem comm_right_action (b : B) (t : V ⊗[K] Y) :
    TensorProduct.comm K V Y
      (((Module.endTensorEndAlgHom (R := K) (S := K) (A := K)).comp
        (Algebra.TensorProduct.map (Algebra.lsmul K K V) (Algebra.lsmul K K Y)))
        ((1 : A) ⊗ₜ[K] b) t) = b • TensorProduct.comm K V Y t := by
  induction t with
  | tmul v y => simp [Module.endTensorEndAlgHom_apply, TensorProduct.smul_tmul']
  | add s t hs ht => simp only [map_add, smul_add, hs, ht]

end ExternalAction

end Langlands.AlgebraTensorUniqueness

namespace Langlands

universe u₁ u₂ v₁ v₂ w₁ w₂

/-- The simple factors of isomorphic external tensor products are isomorphic. -/
theorem algebraTensorFactorUniqueness :
    AlgebraTensorFactorUniquenessStatement.{u₁, u₂, v₁, v₂, w₁, w₂} := by
  intro A₁ A₂ _ _ _ _ V₁ V₂ W₁ W₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ sV₁ _ sV₂ _ sW₁ _ sW₂
  have := sV₁
  have := sV₂
  have := sW₁
  have := sW₂
  have := IsSimpleModule.nontrivial A₁ V₁
  have := IsSimpleModule.nontrivial A₂ V₂
  dsimp only
  intro e he
  constructor
  · apply AlgebraTensorUniqueness.left_factor e
    intro a t
    simpa only [AlgebraTensorUniqueness.left_action] using
      he (a ⊗ₜ[ℂ] (1 : A₂)) t
  · let e' : V₂ ⊗[ℂ] V₁ ≃ₗ[ℂ] W₂ ⊗[ℂ] W₁ :=
      (TensorProduct.comm ℂ V₂ V₁).trans (e.trans (TensorProduct.comm ℂ W₁ W₂))
    apply AlgebraTensorUniqueness.left_factor e'
    intro a t
    have hsource :
        ((Module.endTensorEndAlgHom (R := ℂ) (S := ℂ) (A := ℂ)).comp
          (Algebra.TensorProduct.map (Algebra.lsmul ℂ ℂ V₁) (Algebra.lsmul ℂ ℂ V₂)))
          ((1 : A₁) ⊗ₜ[ℂ] a) (TensorProduct.comm ℂ V₂ V₁ t) =
          TensorProduct.comm ℂ V₂ V₁ (a • t) := by
      apply (TensorProduct.comm ℂ V₁ V₂).injective
      simp only [AlgebraTensorUniqueness.comm_right_action, TensorProduct.comm_comm]
    have h := congrArg (TensorProduct.comm ℂ W₁ W₂)
      (he ((1 : A₁) ⊗ₜ[ℂ] a) (TensorProduct.comm ℂ V₂ V₁ t))
    rw [hsource, AlgebraTensorUniqueness.comm_right_action] at h
    exact h

end Langlands
