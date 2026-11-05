import Langlands.GroupScheme.Unipotent.ScalarExtension
import Langlands.GroupScheme.Torus.DiagonalizableHopf
import Langlands.GroupScheme.AffineHopfCoordinates

/-! # Diagonalizable averaging on coordinate coalgebras -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra Module

namespace Langlands.GroupScheme.Chevalley

open AffineLinearEmbedding

section Coalgebra

variable {k B Λ : Type*} [Field k] [AddCommGroup B] [Module k B] [Coalgebra k B]
  [AddCommGroup Λ]

/-- The trivial-character component for a coalgebra map to a diagonalizable
coordinate algebra. -/
def diagonalizableReynolds (r : B →ₗc[k] AddMonoidAlgebra k Λ) : B →ₗ[k] B :=
  leftAct ((AddMonoidAlgebra.basis Λ k).coord 0 ∘ₗ (r : B →ₗ[k] AddMonoidAlgebra k Λ))

omit [AddCommGroup Λ] in
private theorem groupAlgebra_basis_comul (i : Λ) :
    comul (R := k) (AddMonoidAlgebra.basis Λ k i) =
      AddMonoidAlgebra.basis Λ k i ⊗ₜ[k] AddMonoidAlgebra.basis Λ k i := by
  simpa only [AddMonoidAlgebra.basis_apply] using
    (AddMonoidAlgebra.isGroupLikeElem_single_one (R := k) (A := k) i).comul_eq_tmul_self

private theorem groupAlgebra_zero_coord_one :
    (AddMonoidAlgebra.basis Λ k).coord 0 (1 : AddMonoidAlgebra k Λ) = 1 := by
  change (1 : AddMonoidAlgebra k Λ).coeff 0 = 1
  simp

/-- Every left translation acts on the averaged coordinate by its value at one. -/
theorem diagonalizableReynolds_leftAct (r : B →ₗc[k] AddMonoidAlgebra k Λ)
    (φ : Module.Dual k (AddMonoidAlgebra k Λ)) (b : B) :
    leftAct (φ ∘ₗ (r : B →ₗ[k] AddMonoidAlgebra k Λ)) (diagonalizableReynolds r b) =
      φ 1 • diagonalizableReynolds r b := by
  rw [diagonalizableReynolds, Unipotent.leftAct_leftAct]
  have hfun :
      (φ ∘ₗ (r : B →ₗ[k] AddMonoidAlgebra k Λ)) ∘ₗ
          leftAct ((AddMonoidAlgebra.basis Λ k).coord 0 ∘ₗ (r : B →ₗ[k] AddMonoidAlgebra k Λ)) =
        φ 1 • ((AddMonoidAlgebra.basis Λ k).coord 0 ∘ₗ (r : B →ₗ[k] AddMonoidAlgebra k Λ)) := by
    ext x
    change φ (r (leftAct
      ((AddMonoidAlgebra.basis Λ k).coord 0 ∘ₗ (r : B →ₗ[k] AddMonoidAlgebra k Λ)) x)) = _
    have hr := Unipotent.map_leftAct r ((AddMonoidAlgebra.basis Λ k).coord 0) x
    rw [hr,
      Unipotent.leftAct_coord_of_grouplike (AddMonoidAlgebra.basis Λ k)
        groupAlgebra_basis_comul, map_smul]
    simp only [AddMonoidAlgebra.basis_apply, ← AddMonoidAlgebra.one_def,
      LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, mul_comm]
    rfl
  rw [hfun, Unipotent.leftAct_smul]

/-- The image satisfies the full torus covariance equation in the tensor product. -/
theorem diagonalizableReynolds_covariant (r : B →ₗc[k] AddMonoidAlgebra k Λ) (b : B) :
    (r : B →ₗ[k] AddMonoidAlgebra k Λ).rTensor B (comul (diagonalizableReynolds r b)) =
      (1 : AddMonoidAlgebra k Λ) ⊗ₜ[k] diagonalizableReynolds r b := by
  apply sub_eq_zero.mp
  apply Unipotent.tensor_ext_left
  intro φ
  rw [map_sub, map_sub, ← LinearMap.rTensor_comp_apply]
  change leftAct (φ ∘ₗ (r : B →ₗ[k] AddMonoidAlgebra k Λ)) (diagonalizableReynolds r b) -
    φ 1 • diagonalizableReynolds r b = 0
  rw [diagonalizableReynolds_leftAct, sub_self]

/-- Averaging fixes each coordinate satisfying the trivial-character covariance equation. -/
theorem diagonalizableReynolds_fixed (r : B →ₗc[k] AddMonoidAlgebra k Λ) {b : B}
    (hb : (r : B →ₗ[k] AddMonoidAlgebra k Λ).rTensor B (comul b) =
      (1 : AddMonoidAlgebra k Λ) ⊗ₜ[k] b) :
    diagonalizableReynolds r b = b := by
  rw [diagonalizableReynolds, leftAct_apply, LinearMap.rTensor_comp_apply, hb]
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
    groupAlgebra_zero_coord_one, one_smul]

/-- Its range is exactly the trivial-character covariant subspace. -/
theorem mem_range_diagonalizableReynolds_iff
    (r : B →ₗc[k] AddMonoidAlgebra k Λ) (b : B) :
    b ∈ LinearMap.range (diagonalizableReynolds r) ↔
      (r : B →ₗ[k] AddMonoidAlgebra k Λ).rTensor B (comul b) = (1 : AddMonoidAlgebra k Λ) ⊗ₜ[k] b := by
  constructor
  · rintro ⟨a, rfl⟩
    exact diagonalizableReynolds_covariant r a
  · intro hb
    exact ⟨b, diagonalizableReynolds_fixed r hb⟩

/-- The projection is idempotent. -/
theorem diagonalizableReynolds_idempotent (r : B →ₗc[k] AddMonoidAlgebra k Λ) (b : B) :
    diagonalizableReynolds r (diagonalizableReynolds r b) =
      diagonalizableReynolds r b :=
  diagonalizableReynolds_fixed r (diagonalizableReynolds_covariant r b)

/-- Averaging commutes with every right translation; no centrality is required. -/
theorem diagonalizableReynolds_rightAct (r : B →ₗc[k] AddMonoidAlgebra k Λ)
    (ψ : Module.Dual k B) (b : B) :
    diagonalizableReynolds r (rightAct ψ b) =
      rightAct ψ (diagonalizableReynolds r b) :=
  (rightAct_leftAct ψ _ b).symm

/-- The image of a right-translation-stable subspace remains stable. -/
theorem rightAct_mem_map_diagonalizableReynolds
    (r : B →ₗc[k] AddMonoidAlgebra k Λ) (V : Submodule k B)
    (hV : ∀ (ψ : Module.Dual k B) (b : B), b ∈ V → rightAct ψ b ∈ V)
    (ψ : Module.Dual k B) {b : B} (hb : b ∈ V.map (diagonalizableReynolds r)) :
    rightAct ψ b ∈ V.map (diagonalizableReynolds r) := by
  obtain ⟨a, ha, rfl⟩ := hb
  exact ⟨rightAct ψ a, hV ψ a ha, diagonalizableReynolds_rightAct r ψ a⟩

end Coalgebra

section Bialgebra

variable {k B Λ : Type*} [Field k] [Ring B] [Bialgebra k B] [AddCommGroup Λ]

/-- Averaging fixes the unit, in every characteristic. -/
theorem diagonalizableReynolds_one (r : B →ₐc[k] AddMonoidAlgebra k Λ) :
    diagonalizableReynolds r.toCoalgHom (1 : B) = 1 := by
  rw [diagonalizableReynolds, Unipotent.leftAct_one]
  change (AddMonoidAlgebra.basis Λ k).coord 0 (r 1) • (1 : B) = 1
  rw [map_one, groupAlgebra_zero_coord_one, one_smul]

end Bialgebra

end Langlands.GroupScheme.Chevalley

namespace Langlands.GroupScheme.AffineCoordinates

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
  {Λ : Type u} [AddCommGroup Λ]

/-- The actual diagonalizable group homomorphism gives restriction to its standard
group-algebra Hopf coordinates. -/
def diagonalizableRestriction
    (j : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G) :
    hopfAlgebra G →ₐc[k] AddMonoidAlgebra k Λ :=
  (hopfSpec.fullyFaithful.preimage
    ((Diagonalizable.hopfSpecIso (CommRingCat.of k) Λ).hom ≫ j ≫
      (hopfSpecIso G).inv)).unop.hom

/-- The averaging operator on the actual chosen Hopf coordinates of an affine group. -/
def diagonalizableReynolds
    (j : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G) :
    hopfAlgebra G →ₗ[k] hopfAlgebra G :=
  Chevalley.diagonalizableReynolds (diagonalizableRestriction j).toCoalgHom

theorem diagonalizableReynolds_one
    (j : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G) :
    diagonalizableReynolds j 1 = 1 :=
  Chevalley.diagonalizableReynolds_one (diagonalizableRestriction j)

end Langlands.GroupScheme.AffineCoordinates
