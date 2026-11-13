import Langlands.Representation.Smooth.Factorization.TwoFactorStatement
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Fixed vectors in an external tensor product -/

noncomputable section
open scoped TensorProduct

namespace Langlands.TwoFactorFixedVectors

universe uG uV uW uI

variable {G : Type uG} [Group G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem mem_fixed_iff {ρ : Representation ℂ G V} {K : Subgroup G} {v : V} :
    v ∈ fixedVectors ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  rw [fixedVectors, Representation.mem_invariants]
  exact ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k k.prop⟩

theorem coefficient_right_map {I : Type uI} [DecidableEq I]
    (b : Module.Basis I ℂ W) (f : V →ₗ[ℂ] V) (t : V ⊗[ℂ] W) (i : I) :
    TensorProduct.equivFinsuppOfBasisRight b
        (TensorProduct.map f LinearMap.id t) i =
      f (TensorProduct.equivFinsuppOfBasisRight b t i) := by
  induction t with
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]
  | add t s ht hs => simp [ht, hs]

theorem coefficient_left_map {I : Type uI} [DecidableEq I]
    (b : Module.Basis I ℂ V) (f : W →ₗ[ℂ] W) (t : V ⊗[ℂ] W) (i : I) :
    TensorProduct.equivFinsuppOfBasisLeft b
        (TensorProduct.map LinearMap.id f t) i =
      f (TensorProduct.equivFinsuppOfBasisLeft b t i) := by
  induction t with
  | tmul x y =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, map_smul]
  | add t s ht hs => simp [ht, hs]

/-- A split projection onto the first fixed space fixes a tensor invariant
under the first group. -/
theorem projection_first (ρ : Representation ℂ G V) (K : Subgroup G)
    (t : V ⊗[ℂ] W)
    (ht : ∀ k ∈ K, TensorProduct.map (ρ k) LinearMap.id t = t) :
    TensorProduct.map
      ((fixedVectors ρ K).subtype.comp (fixedVectors ρ K).subtype.leftInverse)
      LinearMap.id t = t := by
  classical
  let b := Module.Free.chooseBasis ℂ W
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  apply Finsupp.ext
  intro i
  rw [coefficient_right_map]
  have hi : TensorProduct.equivFinsuppOfBasisRight b t i ∈ fixedVectors ρ K := by
    apply mem_fixed_iff.mpr
    intro k hk
    rw [← coefficient_right_map, ht k hk]
  exact congrArg (fixedVectors ρ K).subtype
    (LinearMap.leftInverse_apply_of_inj (fixedVectors ρ K).ker_subtype
      ⟨_, hi⟩)

/-- The corresponding projection on the second factor. -/
theorem projection_second (ρ : Representation ℂ G W) (K : Subgroup G)
    (t : V ⊗[ℂ] W)
    (ht : ∀ k ∈ K, TensorProduct.map LinearMap.id (ρ k) t = t) :
    TensorProduct.map LinearMap.id
      ((fixedVectors ρ K).subtype.comp (fixedVectors ρ K).subtype.leftInverse)
      t = t := by
  classical
  let b := Module.Free.chooseBasis ℂ V
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  apply Finsupp.ext
  intro i
  rw [coefficient_left_map]
  have hi : TensorProduct.equivFinsuppOfBasisLeft b t i ∈ fixedVectors ρ K := by
    apply mem_fixed_iff.mpr
    intro k hk
    rw [← coefficient_left_map, ht k hk]
  exact congrArg (fixedVectors ρ K).subtype
    (LinearMap.leftInverse_apply_of_inj (fixedVectors ρ K).ker_subtype
      ⟨_, hi⟩)

end Langlands.TwoFactorFixedVectors

namespace Langlands

universe uG₁ uG₂ uV₁ uV₂

/-- Tensoring the fixed-subspace inclusions identifies their tensor product
with the vectors fixed by the product subgroup. -/
theorem productFixedVectors :
    ProductFixedVectorsStatement.{uG₁, uG₂, uV₁, uV₂} := by
  intro G₁ G₂ _ _ V₁ V₂ _ _ _ _ ρ₁ ρ₂ K₁ K₂
  dsimp only
  let P := fixedVectors ρ₁ K₁
  let Q := fixedVectors ρ₂ K₂
  let r₁ := P.subtype.leftInverse
  let r₂ := Q.subtype.leftInverse
  have hr₁ : r₁.comp P.subtype = LinearMap.id :=
    LinearMap.leftInverse_comp_of_inj P.ker_subtype
  have hr₂ : r₂.comp Q.subtype = LinearMap.id :=
    LinearMap.leftInverse_comp_of_inj Q.ker_subtype
  constructor
  · have hleft : Function.LeftInverse (TensorProduct.map r₁ r₂)
        (TensorProduct.map P.subtype Q.subtype) := by
      intro t
      simp only [TensorProduct.map_map, hr₁, hr₂, TensorProduct.map_id,
        LinearMap.id_apply]
    exact hleft.injective
  · apply le_antisymm
    · rintro t ⟨s, rfl⟩
      apply TwoFactorFixedVectors.mem_fixed_iff.mpr
      intro g hg
      change TensorProduct.map (ρ₁ g.1) (ρ₂ g.2)
        (TensorProduct.map P.subtype Q.subtype s) =
          TensorProduct.map P.subtype Q.subtype s
      induction s with
      | tmul x y =>
        simp only [TensorProduct.map_tmul, Submodule.subtype_apply]
        rw [TwoFactorFixedVectors.mem_fixed_iff.mp x.prop g.1 hg.1,
          TwoFactorFixedVectors.mem_fixed_iff.mp y.prop g.2 hg.2]
      | add s t hs ht => simp [hs, ht]
    · intro t ht
      have h₁ : TensorProduct.map (P.subtype.comp r₁) LinearMap.id t = t := by
        apply TwoFactorFixedVectors.projection_first ρ₁ K₁ t
        intro k hk
        simpa [Representation.tprod_apply, Module.End.one_eq_id] using
          TwoFactorFixedVectors.mem_fixed_iff.mp ht (k, 1) ⟨hk, K₂.one_mem⟩
      have h₂ : TensorProduct.map LinearMap.id (Q.subtype.comp r₂) t = t := by
        apply TwoFactorFixedVectors.projection_second ρ₂ K₂ t
        intro k hk
        simpa [Representation.tprod_apply, Module.End.one_eq_id] using
          TwoFactorFixedVectors.mem_fixed_iff.mp ht (1, k) ⟨K₁.one_mem, hk⟩
      refine ⟨TensorProduct.map r₁ r₂ t, ?_⟩
      calc
        TensorProduct.map P.subtype Q.subtype (TensorProduct.map r₁ r₂ t) =
            TensorProduct.map (P.subtype.comp r₁) LinearMap.id
              (TensorProduct.map LinearMap.id (Q.subtype.comp r₂) t) := by
          simp only [TensorProduct.map_map, LinearMap.comp_id, LinearMap.id_comp]
        _ = t := by rw [h₂, h₁]

end Langlands
