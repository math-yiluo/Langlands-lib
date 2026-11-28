import Langlands.BaseChange.RegularCentralizerAlgebraConjugacyStatement

/-! # Conjugacy of regular matrix centralizer algebras -/

noncomputable section

open Matrix Polynomial

namespace Langlands.BaseChange

universe u

private def cyclicVectorEquiv {F : Type u} [Field F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F) (hv : IsUnit (cyclicBasisMatrix A v)) :
    AdjoinRoot A.charpoly ≃ₗ[F] (Fin n → F) := by
  let eval := charpolyRootEvaluation A
  let f := ((Matrix.mulVecBilin F F).flip v).comp eval.toLinearMap
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro a ha
    apply charpolyRootEvaluation_injective A v hv
    rw [map_zero]
    apply eq_of_commute_mulVec_eq hv
    · simpa only [eval, charpolyRootEvaluation_root] using
        (Commute.all a (AdjoinRoot.root A.charpoly)).map eval
    · exact Commute.zero_left A
    · rw [zero_mulVec]
      exact ha
  have : FiniteDimensional F (AdjoinRoot A.charpoly) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis A.charpoly_monic.ne_zero).basis
  have hdim :
      Module.finrank F (AdjoinRoot A.charpoly) = Module.finrank F (Fin n → F) := by
    change Module.finrank F (F[X] ⧸ Ideal.span {A.charpoly}) = _
    rw [finrank_quotient_span_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Module.finrank_fin_fun]
    exact Fintype.card_fin n
  exact LinearEquiv.ofBijective f
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

/-- Transport the two cyclic representations by the algebra isomorphism. -/
theorem regularCentralizerAlgebraConjugacy : RegularCentralizerAlgebraConjugacyStatement.{u} := by
  intro F _ n A B hA hB e
  obtain ⟨v, hv⟩ := regularCyclicBasis F n A hA
  obtain ⟨w, hw⟩ := regularCyclicBasis F n B hB
  let vA := cyclicVectorEquiv A v hv
  let vB := cyclicVectorEquiv B w hw
  let φ := vA.symm.trans (e.toLinearEquiv.trans vB)
  let g : GeneralLinear n F := Matrix.GeneralLinearGroup.toLin.symm
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin n → F)).symm φ)
  have hg (x : Fin n → F) : (g : Matrix (Fin n) (Fin n) F) *ᵥ x = φ x := by
    change (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin n → F)
      (Matrix.GeneralLinearGroup.toLin g)) x = φ x
    simp only [g, MulEquiv.apply_symm_apply]
  have hφ (a : AdjoinRoot A.charpoly) : φ (vA a) = vB (e a) := by
    simp [φ]
  refine ⟨g, fun a => ?_⟩
  have heq :
      (g : Matrix (Fin n) (Fin n) F) * charpolyRootEvaluation A a =
        charpolyRootEvaluation B (e a) * (g : Matrix (Fin n) (Fin n) F) := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    obtain ⟨b, rfl⟩ := vA.surjective x
    change (_ * _) *ᵥ vA b = (_ * _) *ᵥ vA b
    rw [← mulVec_mulVec, ← mulVec_mulVec, hg, hg, hφ]
    have hactA : charpolyRootEvaluation A a *ᵥ vA b = vA (a * b) := by
      change _ = charpolyRootEvaluation A (a * b) *ᵥ v
      rw [map_mul, ← mulVec_mulVec]
      rfl
    rw [hactA, hφ, map_mul]
    change charpolyRootEvaluation B (e a * e b) *ᵥ w = _
    rw [map_mul, ← mulVec_mulVec]
    rfl
  rw [heq, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

end Langlands.BaseChange
