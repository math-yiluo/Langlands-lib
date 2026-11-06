import Langlands.GroupScheme.Torus.InducedPermutationBasis

/-! # Coordinates for a finite permutation basis -/

noncomputable section

namespace Langlands.PermutationBasis

variable {R Γ V I J : Type*} [CommRing R] [Group Γ]
  [AddCommGroup V] [Module R V]

/-- The inverse coordinate map intertwines inverse pullback with a basis permutation. -/
theorem equivFun_symm_equivariant [Finite I]
    (ρ : Representation R Γ V) (b : Module.Basis I R V)
    (a : Γ →* Equiv.Perm I)
    (hb : ∀ g i, ρ g (b i) = b (a g i))
    (g : Γ) (m : I → R) :
    b.equivFun.symm (fun i => m (a g⁻¹ i)) = ρ g (b.equivFun.symm m) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply]
  simp only [map_sum, map_smul, hb]
  symm
  apply Fintype.sum_equiv (a g)
  intro i
  have h : a g⁻¹ (a g i) = i := by
    change (a g⁻¹ * a g) i = i
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [h]

/-- Coordinates indexed by an equivalent finite set, interpreted in a chosen basis. -/
def coordinateEquiv [Finite J] (b : Module.Basis I R V) (e : J ≃ I) :
    (J → R) ≃ₗ[R] V :=
  (b.reindex e.symm).equivFun.symm

/-- The coordinate equivalence is the finite sum in the reindexed basis. -/
theorem coordinateEquiv_apply [Fintype J]
    (b : Module.Basis I R V) (e : J ≃ I) (m : J → R) :
    coordinateEquiv b e m = ∑ j, m j • b (e j) := by
  simp only [coordinateEquiv, Module.Basis.equivFun_symm_apply,
    Module.Basis.reindex_apply, Equiv.symm_symm]

/-- Equivariant reindexing gives the expected inverse-pullback action on coordinates. -/
theorem coordinateEquiv_equivariant [Finite J]
    (ρ : Representation R Γ V) (b : Module.Basis I R V)
    (e : J ≃ I) (a : Γ →* Equiv.Perm J)
    (hb : ∀ g j, ρ g (b (e j)) = b (e (a g j)))
    (g : Γ) (m : J → R) :
    coordinateEquiv b e (fun j => m (a g⁻¹ j)) =
      ρ g (coordinateEquiv b e m) := by
  apply equivFun_symm_equivariant ρ (b.reindex e.symm) a
  intro h j
  simpa only [Module.Basis.reindex_apply, Equiv.symm_symm] using hb h j

/-- The index action induced by a permuted basis can be compared to any
equivariantly equivalent coordinate set. -/
theorem coordinateEquiv_equivariant_of_permuted [Nontrivial R] [Finite J]
    (ρ : Representation R Γ V) (b : Module.Basis I R V)
    (hb : ∀ g i, ∃ i', ρ g (b i) = b i')
    (e : J ≃ I) (a : Γ →* Equiv.Perm J)
    (he : ∀ g j, e (a g j) = indexAction ρ b hb g (e j))
    (g : Γ) (m : J → R) :
    coordinateEquiv b e (fun j => m (a g⁻¹ j)) =
      ρ g (coordinateEquiv b e m) := by
  apply coordinateEquiv_equivariant ρ b e a
  intro h j
  exact (apply_basis ρ b hb h (e j)).trans (congrArg b (he h j).symm)

end Langlands.PermutationBasis
