import Langlands.Algebra.CentralSimpleScalarExtension
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.TensorProduct.Opposite

/-! # Tensor products and opposite algebras of central simple algebras -/

noncomputable section

namespace Langlands.CentralSimple

universe uK uA uB

open scoped TensorProduct
open MulOpposite

variable (K : Type uK) [Field K]
variable (A : Type uA) [Ring A] [Algebra K A]
variable (B : Type uB) [Ring B] [Algebra K B]

/-- The canonical enveloping map of a finite CSA is an algebra equivalence. -/
def envelopingEquiv [FiniteDimensional K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] : A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] Module.End K A :=
  AlgEquiv.ofBijective (AlgHom.mulLeftRight K A) <| by
    have hs := mulLeftRight_surjective K A
    refine ⟨?_, hs⟩
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (AlgHom.mulLeftRight K A).toLinearMap) ?_).mpr hs
    simp [Module.finrank_tensorProduct, Module.finrank_linearMap,
      (opLinearEquiv K : A ≃ₗ[K] Aᵐᵒᵖ).finrank_eq.symm]

@[simp] theorem envelopingEquiv_apply [FiniteDimensional K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] (t : A ⊗[K] Aᵐᵒᵖ) :
    envelopingEquiv K A t = AlgHom.mulLeftRight K A t := rfl

/-- Endomorphisms of a tensor product of finite vector spaces. -/
def endTensorEquiv [FiniteDimensional K A] [FiniteDimensional K B] :
    Module.End K A ⊗[K] Module.End K B ≃ₐ[K] Module.End K (A ⊗[K] B) :=
  AlgEquiv.ofBijective
    (Module.endTensorEndAlgHom (R := K) (S := K) (A := K) (M := A) (N := B))
    (homTensorHomEquiv K A B A B).bijective

@[simp] theorem endTensorEquiv_tmul [FiniteDimensional K A] [FiniteDimensional K B]
    (f : Module.End K A) (g : Module.End K B) (a : A) (b : B) :
    endTensorEquiv K A B (f ⊗ₜ[K] g) (a ⊗ₜ[K] b) = f a ⊗ₜ[K] g b := rfl

/-- The enveloping equivalence for a tensor product, constructed factor by factor. -/
def tensorEnvelopingEquiv [FiniteDimensional K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K B] [Algebra.IsCentral K B] [IsSimpleRing B] :
    (A ⊗[K] B) ⊗[K] (A ⊗[K] B)ᵐᵒᵖ ≃ₐ[K] Module.End K (A ⊗[K] B) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : A ⊗[K] B ≃ₐ[K] A ⊗[K] B)
    (Algebra.TensorProduct.opAlgEquiv K K A B).symm).trans <|
  (Algebra.TensorProduct.tensorTensorTensorComm K K K K A B Aᵐᵒᵖ Bᵐᵒᵖ).trans <|
  (Algebra.TensorProduct.congr (envelopingEquiv K A) (envelopingEquiv K B)).trans <|
  endTensorEquiv K A B

theorem tensorEnvelopingEquiv_toAlgHom [FiniteDimensional K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K B] [Algebra.IsCentral K B] [IsSimpleRing B] :
    (tensorEnvelopingEquiv K A B).toAlgHom = AlgHom.mulLeftRight K (A ⊗[K] B) := by
  let s := Algebra.TensorProduct.congr
    (AlgEquiv.refl : A ⊗[K] B ≃ₐ[K] A ⊗[K] B)
    (Algebra.TensorProduct.opAlgEquiv K K A B)
  apply (AlgHom.cancel_right s.surjective).mp
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.ext_fourfold'
  intro a b c d
  apply TensorProduct.ext'
  intro x y
  simp [tensorEnvelopingEquiv, Algebra.TensorProduct.tmul_mul_tmul,
    AlgHom.mulLeftRight_apply]

/-- Surjectivity of two-sided multiplication forces simplicity. -/
theorem isSimpleRing_of_enveloping_surjective [Nontrivial A]
    (h : Function.Surjective (AlgHom.mulLeftRight K A)) : IsSimpleRing A := by
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro J
  rw [or_iff_not_imp_left, ← J.one_mem_iff]
  intro hJ
  obtain ⟨x, hxJ, hx0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hJ)
  have hx : x ≠ 0 := by simpa using hx0
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K hx
  obtain ⟨t, ht⟩ := h (f.smulRight (1 : A))
  have hm : ∀ t : A ⊗[K] Aᵐᵒᵖ, AlgHom.mulLeftRight K A t x ∈ J := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      simpa only [AlgHom.mulLeftRight_apply] using
        J.mul_mem_right _ _ (J.mul_mem_left _ _ hxJ)
    | add t s ht hs => simpa using J.add_mem ht hs
  simpa [ht, hf] using hm t

/-- Surjectivity of two-sided multiplication forces centrality. -/
theorem isCentral_of_enveloping_surjective [Nontrivial A]
    (h : Function.Surjective (AlgHom.mulLeftRight K A)) : Algebra.IsCentral K A := by
  refine ⟨fun z hz => ?_⟩
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : A) ≠ 0)
  obtain ⟨t, ht⟩ := h (f.smulRight (1 : A))
  have he : ∀ t : A ⊗[K] Aᵐᵒᵖ,
      AlgHom.mulLeftRight K A t z = AlgHom.mulLeftRight K A t 1 * z := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [AlgHom.mulLeftRight_apply, mul_one]
      rw [mul_assoc, ← (Subalgebra.mem_center_iff.mp hz b.unop), ← mul_assoc]
    | add t s ht hs => simp [ht, hs, add_mul]
  have hz' : f z • (1 : A) = z := by simpa [ht, hf] using he t
  rw [Algebra.mem_bot]
  exact ⟨f z, by simpa [Algebra.algebraMap_eq_smul_one] using hz'⟩

theorem isSimpleRing_tensor [FiniteDimensional K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K B] [Algebra.IsCentral K B] [IsSimpleRing B] :
    IsSimpleRing (A ⊗[K] B) := by
  have : Nontrivial (A ⊗[K] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left K A B
      (algebraMap K B).injective
  apply isSimpleRing_of_enveloping_surjective K (A ⊗[K] B)
  rw [← tensorEnvelopingEquiv_toAlgHom]
  exact (tensorEnvelopingEquiv K A B).surjective

theorem isCentral_tensor [FiniteDimensional K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K B] [Algebra.IsCentral K B] [IsSimpleRing B] :
    Algebra.IsCentral K (A ⊗[K] B) := by
  have : Nontrivial (A ⊗[K] B) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left K A B
      (algebraMap K B).injective
  apply isCentral_of_enveloping_surjective K (A ⊗[K] B)
  rw [← tensorEnvelopingEquiv_toAlgHom]
  exact (tensorEnvelopingEquiv K A B).surjective

end Langlands.CentralSimple

namespace Langlands.Brauer

universe u v w

open scoped TensorProduct

variable {K : Type u} [Field K]

/-- The ground field as an actual central simple algebra. -/
def groundField (K : Type u) [Field K] : CSA.{u, u} K where
  toAlgCat := AlgCat.of K K

/-- Tensor product of actual central simple algebras. -/
def tensor (A : CSA.{u, v} K) (B : CSA.{u, w} K) : CSA.{u, max v w} K := by
  letI := CentralSimple.isSimpleRing_tensor K A B
  letI := CentralSimple.isCentral_tensor K A B
  exact { toAlgCat := AlgCat.of K (A ⊗[K] B) }

/-- The multiplicative opposite of an actual central simple algebra. -/
def opposite (A : CSA.{u, v} K) : CSA.{u, v} K where
  toAlgCat := AlgCat.of K Aᵐᵒᵖ

/-- Scalar extension along any field extension, with the extension field first. -/
def baseChange (L : Type w) [Field L] [Algebra K L] (A : CSA.{u, v} K) :
    CSA.{w, max w v} L := by
  letI := CentralSimple.isSimpleRing_baseChange K A L
  letI := CentralSimple.isCentral_baseChange K A L
  exact { toAlgCat := AlgCat.of L (L ⊗[K] A) }

/-- Positive-size matrices over an actual central simple algebra. -/
def matrix (A : CSA.{u, v} K) (n : ℕ) [NeZero n] : CSA.{u, v} K where
  toAlgCat := AlgCat.of K (Matrix (Fin n) (Fin n) A)

end Langlands.Brauer
