import Langlands.BaseChange.CyclicAlgebraStructure
import Langlands.BaseChange.RegularNormTensorAlgebra
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.TensorProduct.Free

/-! # Scalar extension of a cyclic algebra -/

noncomputable section

namespace Langlands.BaseChange

open scoped TensorProduct

universe u v w

variable {F : Type u} [Field F] (B : Type w) [Field B] [Algebra F B]
  {E : Type v} [CommRing E] [Algebra F E]

local notation "T" => B ⊗[F] E

private def tensorFactorAutHom : (E ≃ₐ[F] E) →* (T ≃ₐ[B] T) where
  toFun := tensorFactorAut B
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply Algebra.TensorProduct.ext'
    intro a x
    rfl
  map_mul' σ τ := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply Algebra.TensorProduct.ext'
    intro a x
    rfl

private theorem tensorFactorAutHom_injective :
    Function.Injective (tensorFactorAutHom (F := F) (E := E) B) := by
  intro σ τ h
  ext x
  let m : E →ₐ[F] T := Algebra.TensorProduct.includeRight
  apply Algebra.TensorProduct.includeRight_injective (algebraMap F B).injective (B := E)
  change m (σ x) = m (τ x)
  change (1 : B) ⊗ₜ[F] σ x = (1 : B) ⊗ₜ[F] τ x
  exact congrArg (fun e : T ≃ₐ[B] T => e ((1 : B) ⊗ₜ x)) h

private theorem tensorFactorAut_fixed {σ : E ≃ₐ[F] E} {l : ℕ}
    (hσ : IsCyclicAlgebra σ l) (x : T) (hx : tensorFactorAut B σ x = x) :
    x ∈ (algebraMap B T).range := by
  let i := Algebra.linearMap F E
  let d : E →ₗ[F] E := σ.toLinearMap - LinearMap.id
  have he : Function.Exact i d := by
    intro y
    change σ y - y = 0 ↔ ∃ a, algebraMap F E a = y
    rw [sub_eq_zero]
    exact ⟨hσ.2.2.2.2 y, fun ⟨a, ha⟩ => by rw [← ha, σ.commutes]⟩
  have hd : d.lTensor B = ((tensorFactorAut B σ).restrictScalars F).toLinearMap - LinearMap.id := by
    apply TensorProduct.ext'
    intro b y
    simp [d]
  have hz : (d.lTensor B) x = 0 := by
    rw [hd]
    exact sub_eq_zero.mpr hx
  obtain ⟨z, hz⟩ := (Module.Flat.lTensor_exact B he x).mp hz
  let r := TensorProduct.rid F B
  have hr : i.lTensor B = (Algebra.linearMap B T).restrictScalars F ∘ₗ r.toLinearMap := by
    apply TensorProduct.ext'
    intro b a
    simp only [i, LinearMap.lTensor_tmul, Algebra.linearMap_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, r, TensorProduct.rid_tmul]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  exact ⟨r z, (DFunLike.congr_fun hr z).symm.trans hz⟩

/-- A formally unramified cyclic algebra keeps the same cyclic degree after
scalar extension to any field. The fixed subspace is transported by flatness. -/
theorem IsCyclicAlgebra.scalarExtension {σ : E ≃ₐ[F] E} {l : ℕ}
    [Algebra.FormallyUnramified F E] (hσ : IsCyclicAlgebra σ l) :
    IsCyclicAlgebra (tensorFactorAut B σ) l := by
  let : Module.Finite F E := hσ.1
  let b := Module.finBasis F E
  let bt := Algebra.TensorProduct.basis B b
  refine ⟨Module.Finite.of_basis bt, ?_, Algebra.FormallyUnramified.isReduced_of_field B T, ?_,
    tensorFactorAut_fixed B hσ⟩
  · rw [Module.finrank_eq_card_basis bt, ← Module.finrank_eq_card_basis b, hσ.2.1]
  · exact (orderOf_injective (tensorFactorAutHom B) (tensorFactorAutHom_injective B)
      σ).trans hσ.2.2.2.1

/-- The residue-field decomposition of a cyclic algebra in characteristic
zero makes it formally étale. -/
theorem IsCyclicAlgebra.formallyEtale [CharZero F] {σ : E ≃ₐ[F] E} {l : ℕ}
    (hσ : IsCyclicAlgebra σ l) : Algebra.FormallyEtale F E := by
  obtain ⟨c⟩ := CyclicAlgebraStructure.exists_coordinates hσ
  let : c.m.asIdeal.IsMaximal := c.m.isMaximal
  let L := E ⧸ c.m.asIdeal
  let : Field L := Ideal.Quotient.field c.m.asIdeal
  let : Module.Finite F L := c.cyclic.1
  let : Algebra.IsSeparable F L := inferInstance
  have hL : Algebra.FormallyEtale F L := Algebra.FormallyEtale.of_isSeparable F L
  let : Algebra.FormallyEtale F (Fin c.r → L) :=
    (Algebra.FormallyEtale.pi_iff (fun _ : Fin c.r => L)).mpr fun _ => hL
  exact Algebra.FormallyEtale.of_equiv c.coords.symm

/-- A commutative cyclic algebra over a characteristic-zero field remains a
cyclic algebra of the same degree after extension to any field. -/
def CyclicAlgebraBaseChangeStatement : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (E : Type v) [CommRing E] [Algebra F E]
    (B : Type w) [Field B] [Algebra F B] (σ : E ≃ₐ[F] E) (l : ℕ),
    IsCyclicAlgebra σ l → IsCyclicAlgebra (tensorFactorAut B σ) l

theorem cyclicAlgebraBaseChange : CyclicAlgebraBaseChangeStatement.{u, v, w} := by
  intro F _ _ E _ _ B _ _ σ l hσ
  let : Algebra.FormallyEtale F E := hσ.formallyEtale
  exact hσ.scalarExtension B

end Langlands.BaseChange
