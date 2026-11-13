import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Algebra.Algebra.Pi

/-! # Tensor decomposition from separated algebra automorphisms -/

noncomputable section

universe u v

open scoped TensorProduct

namespace Langlands.GroupScheme.Descent.AutomorphismTensor

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    {I : Type v} (s : I → S ≃ₐ[R] S)

/-- Evaluation of the second tensor factor at the specified automorphism. -/
def evaluation (i : I) : S ⊗[R] S →ₐ[S] S :=
  Algebra.TensorProduct.lift (AlgHom.id S S) (s i).toAlgHom
    (fun _ _ => Commute.all _ _)

@[simp]
theorem evaluation_tmul (i : I) (a b : S) :
    evaluation R S s i (a ⊗ₜ[R] b) = a * s i b := rfl

/-- The tensor evaluation map with all automorphism components. -/
def hom : S ⊗[R] S →ₐ[S] (I → S) :=
  AlgHom.pi (evaluation R S s)

@[simp]
theorem hom_tmul (a b : S) (i : I) :
    hom R S s (a ⊗ₜ[R] b) i = a * s i b := rfl

/-- Unit separation of two automorphisms makes the corresponding kernels
comaximal. -/
theorem kernels_isCoprime (i j : I)
    (h : ∃ b : S, IsUnit (s i b - s j b)) :
    IsCoprime (RingHom.ker (evaluation R S s i).toRingHom)
      (RingHom.ker (evaluation R S s j).toRingHom) := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨c, hc⟩ := hb.exists_right_inv
  let t : S ⊗[R] S :=
    (1 ⊗ₜ[R] b - (s j b) ⊗ₜ[R] 1) * (c ⊗ₜ[R] 1)
  have hi : evaluation R S s i t = 1 := by
    simpa only [t, map_mul, map_sub, evaluation_tmul, one_mul, map_one,
      mul_one] using hc
  have hj : evaluation R S s j t = 0 := by
    simp only [t, map_mul, map_sub, evaluation_tmul, one_mul, map_one,
      mul_one, sub_self, zero_mul]
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨1 - t, ?_, t, hj, sub_add_cancel _ _⟩
  change evaluation R S s i (1 - t) = 0
  rw [map_sub, map_one, hi, sub_self]

/-- Chinese remainder surjectivity for a finite unit-separated family. -/
theorem hom_surjective [Finite I]
    (hsep : ∀ i j : I, i ≠ j → ∃ b : S, IsUnit (s i b - s j b)) :
    Function.Surjective (hom R S s) := by
  have hcop : Pairwise (fun i j =>
      IsCoprime (RingHom.ker (evaluation R S s i).toRingHom)
        (RingHom.ker (evaluation R S s j).toRingHom)) :=
    fun i j hij => kernels_isCoprime R S s i j (hsep i j hij)
  intro y
  obtain ⟨x, hx⟩ := Ideal.exists_forall_sub_mem_ideal hcop
    (fun i => (y i) ⊗ₜ[R] (1 : S))
  refine ⟨x, funext fun i => ?_⟩
  have hxi : evaluation R S s i (x - (y i) ⊗ₜ[R] (1 : S)) = 0 := hx i
  change evaluation R S s i x = y i
  simpa only [map_sub, evaluation_tmul, map_one, mul_one, sub_eq_zero] using hxi

/-- A finite free algebra has the expected tensor decomposition when the
unit-separated family has exactly its rank. -/
theorem hom_bijective [Nontrivial S] [Finite I]
    [Module.Finite R S] [Module.Free R S]
    (hsep : ∀ i j : I, i ≠ j → ∃ b : S, IsUnit (s i b - s j b))
    (hcard : Nat.card I = Module.finrank R S) :
    Function.Bijective (hom R S s) := by
  let : Fintype I := Fintype.ofFinite I
  have : Nontrivial R := (algebraMap R S).domain_nontrivial
  have hd : Module.finrank S (S ⊗[R] S) = Module.finrank S (I → S) := by
    rw [Module.finrank_baseChange, Module.finrank_fintype_fun_eq_card,
      Fintype.card_eq_nat_card, hcard]
  exact OrzechProperty.bijective_of_surjective_of_finrank_le
    (hom R S s).toLinearMap (hom_surjective R S s hsep) hd.le

/-- The canonical algebra equivalence furnished by the tensor evaluation map. -/
def equiv [Nontrivial S] [Finite I]
    [Module.Finite R S] [Module.Free R S]
    (hsep : ∀ i j : I, i ≠ j → ∃ b : S, IsUnit (s i b - s j b))
    (hcard : Nat.card I = Module.finrank R S) :
    (S ⊗[R] S) ≃ₐ[S] (I → S) :=
  AlgEquiv.ofBijective (hom R S s) (hom_bijective R S s hsep hcard)

@[simp]
theorem equiv_tmul [Nontrivial S] [Finite I]
    [Module.Finite R S] [Module.Free R S]
    (hsep : ∀ i j : I, i ≠ j → ∃ b : S, IsUnit (s i b - s j b))
    (hcard : Nat.card I = Module.finrank R S) (a b : S) (i : I) :
    equiv R S s hsep hcard (a ⊗ₜ[R] b) i = a * s i b := rfl

end Langlands.GroupScheme.Descent.AutomorphismTensor
