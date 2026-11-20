import Langlands.Algebra.EnvelopingTensorProjection
import Langlands.Algebra.LieEnvelopingEquiv
import Mathlib.Algebra.Lie.Prod
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Enveloping algebras of products of Lie algebras -/

noncomputable section
universe u v w s

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Algebra.LieEnvelopingEquiv

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type u} [CommRing R]

private theorem commute_enveloping_map_of_generators
    {L : Type v} [LieRing L] [LieAlgebra R L]
    {A : Type s} [Ring A] [Algebra R A]
    (f : UniversalEnvelopingAlgebra R L →ₐ[R] A) (x : A)
    (hx : ∀ Y, Commute x (f (UniversalEnvelopingAlgebra.ι R Y)))
    (a : UniversalEnvelopingAlgebra R L) : Commute x (f a) := by
  refine Quotient.inductionOn a ?_
  intro t
  change Commute x (f ((UniversalEnvelopingAlgebra.mkAlgHom R L) t))
  induction t using TensorAlgebra.induction with
  | algebraMap c =>
    rw [AlgHom.commutes, AlgHom.commutes]
    exact (Algebra.commutes c x).symm
  | ι Y => exact hx Y
  | mul a b ha hb => simpa only [map_mul] using ha.mul_right hb
  | add a b ha hb => simpa only [map_add] using ha.add_right hb

variable (R) (L : Type v) (M : Type w) [LieRing L] [LieAlgebra R L]
  [LieRing M] [LieAlgebra R M]

local notation "UL" => UniversalEnvelopingAlgebra R L
local notation "UM" => UniversalEnvelopingAlgebra R M
local notation "UP" => UniversalEnvelopingAlgebra R (L × M)

private theorem commute_product_enveloping (a : UL) (b : UM) :
    Commute (map (LieHom.inl R L M) a) (map (LieHom.inr R L M) b) := by
  refine commute_enveloping_map_of_generators (map (LieHom.inr R L M)) _ (fun Y => ?_) b
  refine (commute_enveloping_map_of_generators (map (LieHom.inl R L M)) _
    (fun X => ?_) a).symm
  rw [map_generator, map_generator]
  have h : ⁅LieHom.inr R L M Y, LieHom.inl R L M X⁆ = 0 := by
    change (⁅(0 : L), X⁆, ⁅Y, (0 : M)⁆) = (0, 0)
    simp
  apply sub_eq_zero.mp
  rw [← LieRing.of_associative_ring_bracket, ← LieHom.map_lie, h, map_zero]

private def envelopingProductForward : UP →ₐ[R] UL ⊗[R] UM :=
  EnvelopingTensor.lift R ((UniversalEnvelopingAlgebra.ι R).comp (LieHom.fst R L M))
    ((UniversalEnvelopingAlgebra.ι R).comp (LieHom.snd R L M))

private def envelopingProductBackward : UL ⊗[R] UM →ₐ[R] UP :=
  Algebra.TensorProduct.lift (map (LieHom.inl R L M)) (map (LieHom.inr R L M))
    (commute_product_enveloping R L M)

private theorem envelopingProductForward_inl :
    (envelopingProductForward R L M).comp (map (LieHom.inl R L M)) =
      Algebra.TensorProduct.includeLeft := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change envelopingProductForward R L M (map (LieHom.inl R L M) (UniversalEnvelopingAlgebra.ι R X)) =
    Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := UL) (B := UM)
      (UniversalEnvelopingAlgebra.ι R X)
  rw [map_generator, envelopingProductForward, EnvelopingTensor.lift_generator]
  simp only [LieHom.comp_apply, LieHom.inl_apply, LieHom.fst_apply, LieHom.snd_apply, map_zero,
    TensorProduct.tmul_zero, add_zero, Algebra.TensorProduct.includeLeft_apply]

private theorem envelopingProductForward_inr :
    (envelopingProductForward R L M).comp (map (LieHom.inr R L M)) =
      Algebra.TensorProduct.includeRight := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change envelopingProductForward R L M (map (LieHom.inr R L M) (UniversalEnvelopingAlgebra.ι R X)) =
    Algebra.TensorProduct.includeRight (UniversalEnvelopingAlgebra.ι R X)
  rw [map_generator, envelopingProductForward, EnvelopingTensor.lift_generator]
  simp only [LieHom.comp_apply, LieHom.inr_apply, LieHom.fst_apply, LieHom.snd_apply, map_zero,
    TensorProduct.zero_tmul, zero_add, Algebra.TensorProduct.includeRight_apply]

/-- The enveloping algebra of the product Lie algebra is the tensor product
of the two actual enveloping algebras. -/
def envelopingProduct : UP ≃ₐ[R] (UL ⊗[R] UM) := by
  refine AlgEquiv.ofAlgHom (envelopingProductForward R L M) (envelopingProductBackward R L M) ?_ ?_
  · apply Algebra.TensorProduct.ext
    · rw [AlgHom.comp_assoc, envelopingProductBackward, Algebra.TensorProduct.lift_comp_includeLeft,
        envelopingProductForward_inl, AlgHom.id_comp]
    · change ((envelopingProductForward R L M).comp (envelopingProductBackward R L M)).comp
        Algebra.TensorProduct.includeRight = (AlgHom.id R (UL ⊗[R] UM)).comp
          Algebra.TensorProduct.includeRight
      rw [AlgHom.comp_assoc, envelopingProductBackward,
        Algebra.TensorProduct.lift_comp_includeRight', envelopingProductForward_inr, AlgHom.id_comp]
  · apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    rintro ⟨X, Y⟩
    change envelopingProductBackward R L M (envelopingProductForward R L M
      (UniversalEnvelopingAlgebra.ι R (X, Y))) = UniversalEnvelopingAlgebra.ι R (X, Y)
    rw [envelopingProductForward, EnvelopingTensor.lift_generator, map_add]
    simp only [LieHom.comp_apply, LieHom.fst_apply, LieHom.snd_apply]
    rw [envelopingProductBackward, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul,
      map_one, map_one, one_mul, mul_one, map_generator, map_generator, ← map_add,
      LieHom.inl_apply, LieHom.inr_apply]
    simp only [Prod.mk_add_mk, add_zero, zero_add]

@[simp]
theorem envelopingProduct_generator (p : L × M) :
    envelopingProduct R L M (UniversalEnvelopingAlgebra.ι R p) =
      UniversalEnvelopingAlgebra.ι R p.1 ⊗ₜ[R] 1 +
        1 ⊗ₜ[R] UniversalEnvelopingAlgebra.ι R p.2 :=
  EnvelopingTensor.lift_generator R _ _ p

@[simp]
theorem envelopingProduct_symm_tmul (a : UL) (b : UM) :
    (envelopingProduct R L M).symm (a ⊗ₜ[R] b) =
      map (LieHom.inl R L M) a * map (LieHom.inr R L M) b :=
  Algebra.TensorProduct.lift_tmul _ _ (commute_product_enveloping R L M) a b

end Langlands.Algebra.LieEnvelopingEquiv
