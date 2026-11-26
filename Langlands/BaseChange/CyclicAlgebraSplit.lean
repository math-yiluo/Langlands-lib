import Langlands.BaseChange.CyclicAlgebraBaseChange
import Langlands.BaseChange.CyclicNormDeterminant
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Cyclic algebras over a splitting field -/

noncomputable section

namespace Langlands.BaseChange

open scoped TensorProduct

universe u v w

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {l : ℕ}

/-- Finite reduced cyclic algebras are formally étale in every characteristic. -/
theorem IsCyclicAlgebra.formallyEtale_of_cyclic (hσ : IsCyclicAlgebra σ l) :
    Algebra.FormallyEtale F E := by
  obtain ⟨c⟩ := CyclicAlgebraStructure.exists_coordinates hσ
  let : c.m.asIdeal.IsMaximal := c.m.isMaximal
  let L := E ⧸ c.m.asIdeal
  let : Field L := Ideal.Quotient.field c.m.asIdeal
  let : Module.Finite F L := c.cyclic.1
  let : IsGalois F L := c.cyclic.isGalois
  let : Algebra.FormallyEtale F L := Algebra.FormallyEtale.of_isSeparable F L
  let : Algebra.FormallyEtale F (Fin c.r → L) :=
    (Algebra.FormallyEtale.pi_iff (fun _ : Fin c.r => L)).mpr fun _ => inferInstance
  exact Algebra.FormallyEtale.of_equiv c.coords.symm

/-- Over an algebraically closed base, a cyclic algebra is a product of copies
of the base field, and the generator acts by rotation in those coordinates. -/
theorem IsCyclicAlgebra.exists_splitCoordinates [IsAlgClosed F] (hσ : IsCyclicAlgebra σ l) :
    ∃ e : E ≃ₐ[F] (Fin l → F), ∀ x i, e (σ x) i = e x (finRotate l i) := by
  obtain ⟨c⟩ := CyclicAlgebraStructure.exists_coordinates hσ
  let : c.m.asIdeal.IsMaximal := c.m.isMaximal
  let L := E ⧸ c.m.asIdeal
  let : Field L := Ideal.Quotient.field c.m.asIdeal
  let : Module.Finite F L := c.cyclic.1
  let e₀ : F ≃ₐ[F] L := AlgEquiv.ofBijective (Algebra.ofId F L)
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := F) (K := L))
  have hτ : c.τ = 1 := by
    ext x
    obtain ⟨a, rfl⟩ := e₀.surjective x
    exact c.τ.commutes a
  have hd : c.d = 1 := c.cyclic.2.2.2.1.symm.trans (by simp [hτ])
  have hr : c.r = l := by simpa only [hd, mul_one] using c.degree_eq.symm
  suffices hc : ∃ e : E ≃ₐ[F] (Fin c.r → F),
      ∀ x i, e (σ x) i = e x (finRotate c.r i) from hr ▸ hc
  refine ⟨c.coords.trans (AlgEquiv.piCongrRight (fun _ : Fin c.r => e₀.symm)), ?_⟩
  intro x i
  change e₀.symm (c.coords (σ x) i) = e₀.symm (c.coords x (finRotate c.r i))
  congr 1
  rw [c.coords_apply, c.coords_apply, ← AlgEquiv.mul_apply, ← pow_succ]
  by_cases hi : i.val + 1 < c.r
  · have hrot : (finRotate c.r i).val = i.val + 1 := by
      rw [finRotate_apply]
      exact Fin.val_add_one_of_lt' hi
    rw [hrot]
  · have hi' : i.val + 1 = c.r := by omega
    have hrot : (finRotate c.r i).val = 0 := by
      rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod, hi', Nat.mod_self]
    rw [hi', hrot, pow_zero, AlgEquiv.one_apply, c.wrap, hτ, AlgEquiv.one_apply]

/-- After extension to an algebraically closed field, the cyclic algebra
and its generator admit split cyclic coordinates. -/
theorem IsCyclicAlgebra.exists_splitCoordinates_baseChange
    (B : Type w) [Field B] [Algebra F B] [IsAlgClosed B] (hσ : IsCyclicAlgebra σ l) :
    ∃ e : (B ⊗[F] E) ≃ₐ[B] (Fin l → B),
      ∀ x i, e (tensorFactorAut B σ x) i = e x (finRotate l i) := by
  let : Algebra.FormallyEtale F E := hσ.formallyEtale_of_cyclic
  exact (hσ.scalarExtension B).exists_splitCoordinates

end Langlands.BaseChange
