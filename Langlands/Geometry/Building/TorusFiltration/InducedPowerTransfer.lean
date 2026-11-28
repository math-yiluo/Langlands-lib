import Langlands.GroupScheme.Torus.GaloisLatticeRealizationProof
import Langlands.GroupScheme.Torus.InducedBasisTransport
import Langlands.GroupScheme.Torus.LatticeGaloisScalarExtension
import Langlands.GroupScheme.Torus.SurjectionIsogenySectionProof
import Mathlib.FieldTheory.SeparableDegree

/-! # Degree powers through permutation tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace InducedPowerTransfer

section Representation

variable {Γ A I : Type u} [Group Γ] [AddCommGroup A]
  (ρ : Representation ℤ Γ A) (a : Γ →* Equiv.Perm I)

private def coordinateAction : Representation ℤ Γ (I → A) where
  toFun σ := LinearMap.pi fun i => (ρ σ).comp (LinearMap.proj (a σ⁻¹ i))
  map_one' := by
    ext x i
    simp
  map_mul' σ τ := by
    apply LinearMap.ext
    intro x
    funext i
    change ρ (σ * τ) (x (a (σ * τ)⁻¹ i)) = ρ σ (ρ τ (x (a τ⁻¹ (a σ⁻¹ i))))
    rw [mul_inv_rev, map_mul a, Equiv.Perm.mul_apply, map_mul ρ, Module.End.mul_apply]

private theorem coordinateAction_apply (σ : Γ) (x : I → A) (i : I) :
    coordinateAction ρ a σ x i = ρ σ (x (a σ⁻¹ i)) := rfl

private def constantHom : A →+ (I → A) where
  toFun x _ := x
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem constantHom_equivariant (σ : Γ) (x : A) :
    constantHom (I := I) (ρ σ x) = coordinateAction ρ a σ (constantHom x) := rfl

variable [Fintype I]

private def sumHom : (I → A) →+ A where
  toFun x := ∑ i, x i
  map_zero' := Finset.sum_const_zero
  map_add' _ _ := Finset.sum_add_distrib

private theorem sumHom_equivariant (σ : Γ) (x : I → A) :
    sumHom (coordinateAction ρ a σ x) = ρ σ (sumHom x) := by
  change (∑ i, ρ σ (x (a σ⁻¹ i))) = ρ σ (∑ i, x i)
  rw [map_sum]
  exact Equiv.sum_comp (a σ⁻¹) (fun i => ρ σ (x i))

private theorem sumHom_constantHom (x : A) :
    sumHom (constantHom (I := I) x) = Fintype.card I • x := by
  simp [sumHom, constantHom]

private def coordinateBasis {J : Type u} (g : I → Γ) (b : Module.Basis J ℤ A) :
    Module.Basis (Σ _ : I, J) ℤ (I → A) :=
  Pi.basis fun i => b.map (LinearEquiv.ofBijective (ρ (g i)) (ρ.apply_bijective (g i)))

private theorem coordinateBasis_permuted {J : Type u} (i₀ : I) (g : I → Γ)
    (hg : ∀ i, a (g i) i₀ = i) (b : Module.Basis J ℤ A)
    (hb : ∀ σ, a σ i₀ = i₀ → ∀ j, ∃ j', ρ σ (b j) = b j') (σ : Γ) (c : Σ _ : I, J) :
    ∃ c', coordinateAction ρ a σ (coordinateBasis ρ g b c) = coordinateBasis ρ g b c' := by
  classical
  let t := a σ c.1
  have hback : ∀ (τ : Γ) (i : I), a τ⁻¹ (a τ i) = i := by
    intro τ i
    rw [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  let δ := (g t)⁻¹ * σ * (g c.1)
  have hδ : a δ i₀ = i₀ := by
    simp only [δ, map_mul, Equiv.Perm.mul_apply, hg]
    change a (g t)⁻¹ t = i₀
    exact (congrArg (a (g t)⁻¹) (hg t).symm).trans (hback (g t) i₀)
  obtain ⟨j, hj⟩ := hb δ hδ c.2
  have hvalue : ρ σ (ρ (g c.1) (b c.2)) = ρ (g t) (b j) := by
    rw [← hj, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    simp [δ, mul_assoc]
  refine ⟨⟨t, j⟩, ?_⟩
  funext i
  simp only [coordinateAction_apply, coordinateBasis, Pi.basis_apply, Module.Basis.map_apply,
    LinearEquiv.ofBijective_apply]
  by_cases h : i = t
  · subst i
    rw [show a σ⁻¹ t = c.1 from hback σ c.1, Pi.single_eq_same, Pi.single_eq_same]
    exact hvalue
  · have hne : a σ⁻¹ i ≠ c.1 := fun he => h ((a σ⁻¹).injective (he.trans (hback σ c.1).symm))
    rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne h, map_zero]

end Representation

section Embeddings

variable (k L E : Type u) [Field k] [Field L] [Field E] [Algebra k L] [Algebra k E]

private def embeddingAction : (E ≃ₐ[k] E) →* Equiv.Perm (L →ₐ[k] E) where
  toFun σ :=
    { toFun := fun i => σ.toAlgHom.comp i
      invFun := fun i => σ.symm.toAlgHom.comp i
      left_inv := fun i => AlgHom.ext fun x => σ.symm_apply_apply (i x)
      right_inv := fun i => AlgHom.ext fun x => σ.apply_symm_apply (i x) }
  map_one' := by ext i x; rfl
  map_mul' σ τ := by ext i x; rfl

variable [Algebra L E] [IsScalarTower k L E]

private theorem exists_move_embedding [Normal k E] (i : L →ₐ[k] E) :
    ∃ σ : E ≃ₐ[k] E, embeddingAction k L E σ (IsScalarTower.toAlgHom k L E) = i := by
  let σ := AlgEquiv.ofBijective (i.liftNormal E) ((i.liftNormal E).normal_bijective k E E)
  exact ⟨σ, AlgHom.ext fun x => i.liftNormal_commutes E x⟩

private def stabilizerLift {σ : E ≃ₐ[k] E}
    (hσ : embeddingAction k L E σ (IsScalarTower.toAlgHom k L E) =
      IsScalarTower.toAlgHom k L E) : E ≃ₐ[L] E :=
  AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => DFunLike.congr_fun hσ x

private theorem stabilizerLift_restrict {σ : E ≃ₐ[k] E}
    (hσ : embeddingAction k L E σ (IsScalarTower.toAlgHom k L E) =
      IsScalarTower.toAlgHom k L E) : (stabilizerLift k L E hσ).restrictScalars k = σ :=
  AlgEquiv.ext fun _ => rfl

private theorem natCard_embeddings [FiniteDimensional k L] [Algebra.IsSeparable k L]
    [Normal k E] : Nat.card (L →ₐ[k] E) = Module.finrank k L := by
  rw [← Field.finSepDegree_eq_finrank_of_isSeparable k L]
  symm
  apply Field.finSepDegree_eq_of_adjoin_splits k L E (IntermediateField.adjoin_univ k L)
  intro x _
  refine ⟨Algebra.IsIntegral.isIntegral x, ?_⟩
  rw [← minpoly.algebraMap_eq (algebraMap L E).injective x]
  exact Normal.splits (inferInstance : Normal k E) (algebraMap L E x)

end Embeddings

section Tori

variable (k L E : Type u) [Field k] [Field L] [Field E]
  [Algebra k L] [Algebra k E] [Algebra L E] [IsScalarTower k L E]
  [FiniteDimensional k L] [Algebra.IsSeparable k L]
  [FiniteDimensional k E] [IsGalois k E]

set_option maxHeartbeats 1800000 in
/-- If a torus becomes induced over `L`, its degree-power endomorphism factors
through an induced torus over the ground field. -/
theorem exists_degree_power_factorization
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hInd : IsInducedTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T))
    (hSplit : IsSplitTorus (GaloisPointComparison.baseChanged k E T.toGrp)) :
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : T ⟶ S) (j : S ⟶ T),
      IsInducedTorus S ∧ i ≫ j = (Module.finrank k L : ℤ) • 𝟙 T := by
  classical
  let : FiniteDimensional L E := FiniteDimensional.right k L E
  let : IsGalois L E := IsGalois.tower_top_of_isGalois k L E
  let bc := CommGroupScheme.baseChange (algebraBaseMap k E)
  let TL := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T
  let A := characterLattice (bc.obj T)
  let ρ := characterLattice.galoisRepresentation k E T
  have hSplitL : IsSplitTorus (GaloisPointComparison.baseChanged L E TL.toGrp) :=
    (IsSplitTorus.baseChange_fieldTower_iff k L E T.toGrp).mp hSplit
  obtain ⟨J, hJ, b, hb⟩ := hInd.exists_permuted_basis E hSplitL
  have hTower : algebraBaseMap L E ≫ algebraBaseMap k L = algebraBaseMap k E := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq k L E]
  let e := characterLattice.scalarExtensionGaloisEquiv hTower T
  let b₀ : Module.Basis J ℤ A := b.map e.toLinearEquiv.symm
  let I := L →ₐ[k] E
  let a := embeddingAction k L E
  let i₀ : I := IsScalarTower.toAlgHom k L E
  let g : I → (E ≃ₐ[k] E) := fun i => (exists_move_embedding k L E i).choose
  have hg : ∀ i, a (g i) i₀ = i := fun i => (exists_move_embedding k L E i).choose_spec
  have hb₀ : ∀ σ, a σ i₀ = i₀ → ∀ j, ∃ j', ρ σ (b₀ j) = b₀ j' := by
    intro σ hσ j
    let τ := stabilizerLift k L E hσ
    obtain ⟨j', hj'⟩ := hb τ j
    refine ⟨j', e.toLinearEquiv.injective ?_⟩
    change e.toLinearEquiv (ρ σ (e.toLinearEquiv.symm (b j))) =
      e.toLinearEquiv (e.toLinearEquiv.symm (b j'))
    rw [← stabilizerLift_restrict k L E hσ]
    have h := congrArg (fun f : A →ₗ[ℤ] _ => f (e.toLinearEquiv.symm (b j)))
      (e.toIntertwiningMap.isIntertwining' τ)
    refine h.trans ?_
    change characterLattice.galoisRepresentation L E TL τ
        (e.toLinearEquiv (e.toLinearEquiv.symm (b j))) =
      e.toLinearEquiv (e.toLinearEquiv.symm (b j'))
    simpa only [LinearEquiv.apply_symm_apply] using hj'
  let : Fintype I := Fintype.ofFinite I
  let B := coordinateBasis ρ g b₀
  let : Module.Free ℤ (I → A) := Module.Free.of_basis B
  let : Module.Finite ℤ (I → A) := Module.Finite.of_basis B
  let ρ' := coordinateAction ρ a
  obtain ⟨S, c, hS, hc⟩ := torusGaloisLatticeRealization k E (I → A) ρ'
  have hIndS : IsInducedTorus S :=
    isInducedTorus_of_equivariant_basis S E hS ρ' B c.toIntLinearEquiv hc
      (coordinateBasis_permuted ρ a i₀ g hg b₀ hb₀)
  let f : characterLattice (bc.obj S) →+ A := sumHom.comp c.symm.toAddMonoidHom
  let m : A →+ characterLattice (bc.obj S) := c.toAddMonoidHom.comp constantHom
  have hf (σ : E ≃ₐ[k] E) (χ : characterLattice (bc.obj S)) :
      f (characterLattice.galoisRepresentation k E S σ χ) = ρ σ (f χ) := by
    obtain ⟨x, rfl⟩ := c.surjective χ
    change sumHom (c.symm (characterLattice.galoisRepresentation k E S σ (c x))) =
      ρ σ (sumHom (c.symm (c x)))
    rw [← hc, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    exact sumHom_equivariant ρ a σ x
  have hm (σ : E ≃ₐ[k] E) (χ : A) :
      m (ρ σ χ) = characterLattice.galoisRepresentation k E S σ (m χ) := by
    change c (constantHom (ρ σ χ)) =
      characterLattice.galoisRepresentation k E S σ (c (constantHom χ))
    rw [← hc]
    exact congrArg c (constantHom_equivariant ρ a σ χ)
  obtain ⟨i, hi, -⟩ := hS.existsUnique_hom_of_equivariant_characterMap f hf
  obtain ⟨j, hj, -⟩ := hSplit.existsUnique_hom_of_equivariant_characterMap m hm
  refine ⟨S, i, j, hIndS, ?_⟩
  let n := Module.finrank k L
  obtain ⟨p, -, hp⟩ := hSplit.existsUnique_hom_of_equivariant_characterMap (T := T)
    ((n : ℤ) • AddMonoidHom.id A) (fun σ χ => by
      change (n : ℤ) • (ρ σ χ) = ρ σ ((n : ℤ) • χ)
      rw [map_zsmul])
  have hn : Fintype.card I = n := (Nat.card_eq_fintype_card.symm).trans
    (natCard_embeddings k L E)
  have hcomp : i ≫ j = p := hp _ fun χ => by
    change bc.map (i ≫ j) ≫ χ = _
    rw [Functor.map_comp, Category.assoc, hj, hi]
    change sumHom (c.symm (c (constantHom χ))) = (n : ℤ) • χ
    rw [AddEquiv.symm_apply_apply, sumHom_constantHom, hn, natCast_zsmul]
  have hpow : (n : ℤ) • 𝟙 T = p := hp _ fun χ => by
    rw [TorusSurjectionIsogenySection.baseChange_map_zsmul_id, Preadditive.zsmul_comp,
      Category.id_comp]
    rfl
  exact hcomp.trans hpow.symm

end Tori

end InducedPowerTransfer
end Langlands.GroupScheme
