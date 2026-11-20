import Langlands.ClassField.Global.TensorUnitCochains
import Langlands.GroupScheme.Torus.WeilRestrictionSeparableNorm
import Langlands.ClassFieldTheory.Local.Norms

/-! # Norms of tensor units and torsion lifts -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.ClassField.Global.TensorUnitShapiro

open Langlands.Algebra GroupScheme.WeilGm

set_option backward.isDefEq.respectTransparency false

variable {F B L : Type u} [Field F] [Field B] [Field L] [Algebra F B] [Algebra F L]

/-- Extend a unit of the left factor to the tensor algebra. -/
def leftTensorUnit : Bˣ →* (B ⊗[F] L)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeft : B →ₐ[F] B ⊗[F] L).toMonoidHom

/-- The coefficient automorphisms fix units extended from the left factor. -/
theorem tensorAction_leftTensorUnit (σ : Gal(L/F)) (x : Bˣ) :
    tensorAction F B L σ (leftTensorUnit x) = leftTensorUnit x := by
  apply Units.ext
  change (x : B) ⊗ₜ[F] σ (1 : L) = (x : B) ⊗ₜ[F] (1 : L)
  rw [map_one]

/-- Extension on the right factor respects units from the left factor. -/
theorem extendTensorUnit_leftTensorUnit (M : Type u) [Field M] [Algebra F M] [Algebra L M]
    [IsScalarTower F L M] (x : Bˣ) :
    extendTensorUnit M (leftTensorUnit (F := F) (L := L) x) = leftTensorUnit x := by
  apply Units.ext
  change (x : B) ⊗ₜ[F] algebraMap L M (1 : L) = (x : B) ⊗ₜ[F] (1 : M)
  rw [map_one]

variable [FiniteDimensional F B]

/-- The determinant tensor norm is equivariant for the coefficient field action. -/
theorem tensorNormUnits_action (σ : Gal(L/F)) (x : (B ⊗[F] L)ˣ) :
    tensorNormUnits F B L (tensorAction F B L σ x) = σ • tensorNormUnits F B L x :=
  tensorNormUnits_naturality σ.toAlgHom x

/-- The norm commutes with coefficient extension. -/
theorem tensorNormUnits_extend (M : Type u) [Field M] [Algebra F M] [Algebra L M]
    [IsScalarTower F L M] (x : (B ⊗[F] L)ˣ) :
    tensorNormUnits F B M (extendTensorUnit M x) =
      Units.map (algebraMap L M) (tensorNormUnits F B L x) :=
  tensorNormUnits_naturality (IsScalarTower.toAlgHom F L M) x

/-- The tensor norm on a unit of the left factor is the base field norm after extension. -/
theorem tensorNormUnits_left (x : Bˣ) :
    tensorNormUnits F B L (leftTensorUnit x) =
      Units.map (algebraMap F L) (LocalClassField.normUnits F B x) := by
  apply Units.ext
  have h := tensorNorm_naturality (Algebra.ofId F L) ((x : B) ⊗ₜ[F] (1 : F))
  change tensorNorm F B L ((x : B) ⊗ₜ[F] algebraMap F L (1 : F)) =
    algebraMap F L (Algebra.norm F ((1 : F) ⊗ₜ[F] (x : B))) at h
  rw [map_one] at h
  have hnorm := Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.lid F B)
    ((1 : F) ⊗ₜ[F] (x : B))
  rw [Algebra.TensorProduct.lid_tmul, one_smul] at hnorm
  exact h.trans (congrArg (algebraMap F L) hnorm.symm)

variable [Algebra B L] [IsScalarTower F B L] [Normal F L] [Algebra.IsSeparable F B]

/-- Over the splitting coefficient field, the determinant norm multiplies the canonical
unit coordinates. -/
theorem tensorNormUnits_eq_prod (x : (B ⊗[F] L)ˣ) :
    tensorNormUnits F B L x = ∏ j : B →ₐ[F] L, unitEmbeddingEquiv F B L x j := by
  classical
  let hs (b : B) : ((minpoly F b).map (algebraMap F L)).Splits := by
    rw [← minpoly.algHom_eq (IsScalarTower.toAlgHom F B L) (algebraMap B L).injective b]
    exact (inferInstance : Normal F L).splits (algebraMap B L b)
  apply Units.ext
  change _ = Units.coeHom L (∏ j : B →ₐ[F] L, unitEmbeddingEquiv F B L x j)
  rw [map_prod]
  change tensorNorm F B L (x : B ⊗[F] L) = ∏ j : B →ₐ[F] L,
    tensorEmbeddingEquiv F B L (x : B ⊗[F] L) j
  rw [separableEmbedding_tensorNorm F B L hs L]
  apply Finset.prod_congr rfl
  intro j _
  generalize (x : B ⊗[F] L) = t
  induction t using TensorProduct.inductionOn with
  | tmul b l =>
    rw [tensorEmbeddingEquiv_tmul]
    change j b * l = l * j b
    exact mul_comm _ _
  | add t s ht hs => simp only [map_add, Pi.add_apply, ht, hs]

/-- Every scalar of `n`-th power one has a tensor norm lift of `n`-th power one. -/
theorem exists_tensorNorm_torsion_lift (n : ℕ) (a : Lˣ) (ha : a ^ n = 1) :
    ∃ x : (B ⊗[F] L)ˣ, x ^ n = 1 ∧ tensorNormUnits F B L x = a := by
  classical
  let i := IsScalarTower.toAlgHom F B L
  let e := unitEmbeddingEquiv F B L
  let x := e.symm (Pi.mulSingle i a)
  have hx : e x = Pi.mulSingle i a := e.apply_symm_apply _
  refine ⟨x, e.injective ?_, ?_⟩
  · rw [map_pow, hx, map_one]
    funext j
    by_cases h : j = i
    · subst j
      simpa only [Pi.pow_apply, Pi.mulSingle_eq_same, Pi.one_apply] using ha
    · simp only [Pi.pow_apply, Pi.mulSingle_eq_of_ne h, one_pow, Pi.one_apply]
  · rw [tensorNormUnits_eq_prod]
    change ∏ j, e x j = _
    rw [hx]
    let c : (B →ₐ[F] L) → Lˣ := Pi.mulSingle i a
    change ∏ j, c j = a
    calc
      _ = c i := Finset.prod_eq_single_of_mem i (Finset.mem_univ i)
        (fun j _ h => by simp [c, h])
      _ = a := by simp [c]

end Langlands.ClassField.Global.TensorUnitShapiro
