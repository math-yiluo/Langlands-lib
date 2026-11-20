import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! The associative center of a tensor product of algebras over a field. -/

noncomputable section

open scoped Classical TensorProduct
open TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Algebra.TensorProductCenter

variable {K A B : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]

local notation "Z" => Subalgebra.center K
local notation "tmap" => Algebra.TensorProduct.map (R := K) (S := K)
local notation "swap" => Algebra.TensorProduct.comm K

private theorem exists_from_leftCenter {z : A ⊗[K] B}
    (hz : ∀ a : A, Commute (a ⊗ₜ[K] (1 : B)) z) :
    ∃ y : Z A ⊗[K] B, tmap (Z A).val (AlgHom.id K B) y = z := by
  let b := Module.Basis.ofVectorSpace K B
  let e := TensorProduct.equivFinsuppOfBasisRight (M := A) b
  have hmul (a : A) (i : Module.Basis.ofVectorSpaceIndex K B) (x : A ⊗[K] B) :
      e ((a ⊗ₜ[K] (1 : B)) * x) i = a * e x i ∧
      e (x * (a ⊗ₜ[K] (1 : B))) i = e x i * a := by
    induction x using TensorProduct.inductionOn with
    | tmul c d =>
      simp [e, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp [mul_add, add_mul, hx.1, hx.2, hy.1, hy.2]
  have hc (i : Module.Basis.ofVectorSpaceIndex K B) : e z i ∈ Z A := by
    rw [Subalgebra.mem_center_iff]
    intro a
    rw [← (hmul a i z).1, ← (hmul a i z).2, (hz a).eq]
  refine ⟨∑ i ∈ (e z).support, ((⟨e z i, hc i⟩ : Z A) ⊗ₜ[K] b i), ?_⟩
  calc
    _ = (e z).sum (fun i a => a ⊗ₜ[K] b i) := by
      simp [Finsupp.sum, Algebra.TensorProduct.map_tmul]
    _ = z := (TensorProduct.equivFinsuppOfBasisRight_symm_apply b (e z)).symm.trans
      (e.symm_apply_apply z)

private theorem exists_from_rightCenter {z : A ⊗[K] B}
    (hz : ∀ b : B, Commute ((1 : A) ⊗ₜ[K] b) z) :
    ∃ y : A ⊗[K] Z B, tmap (AlgHom.id K A) (Z B).val y = z := by
  have h (b : B) : Commute (b ⊗ₜ[K] (1 : A)) (swap A B z) := by
    simpa only [Algebra.TensorProduct.comm_tmul] using (hz b).map (swap A B)
  obtain ⟨y, hy⟩ := exists_from_leftCenter h
  refine ⟨swap (Z B) A y, ?_⟩
  apply (swap A B).injective
  calc
    _ = tmap (Z B).val (AlgHom.id K A) y := by
      clear hy
      induction y using TensorProduct.inductionOn with
      | tmul b a => simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul]
      | add x y hx hy => simp [hx, hy]
    _ = _ := hy

private theorem map_injective {P Q : Type*} [Ring P] [Algebra K P] [Ring Q] [Algebra K Q]
    (f : P →ₐ[K] A) (g : Q →ₐ[K] B) (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (tmap f g) :=
  TensorProduct.map_injective_of_flat_flat f.toLinearMap g.toLinearMap hf hg

/-- The tensor of the inclusions of the two centers, landing in the actual tensor-product center. -/
def fromCenters : (Z A ⊗[K] Z B) →ₐ[K] Z (A ⊗[K] B) :=
  (tmap (Z A).val (Z B).val).codRestrict (Z (A ⊗[K] B)) fun y => by
    induction y using TensorProduct.inductionOn with
    | tmul a b =>
      rw [Algebra.TensorProduct.map_tmul, Subalgebra.mem_center_iff]
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul c d =>
        exact (Commute.tmul (Subalgebra.mem_center_iff.mp a.property c)
          (Subalgebra.mem_center_iff.mp b.property d)).eq
      | add x y hx hy => rw [add_mul, mul_add, hx, hy]
    | add x y hx hy => simpa only [map_add] using (Z (A ⊗[K] B)).add_mem hx hy

private theorem fromCenters_surjective : Function.Surjective (fromCenters (K := K) (A := A) (B := B)) := by
  intro z
  obtain ⟨y, hy⟩ := exists_from_leftCenter (fun a => Subalgebra.mem_center_iff.mp z.property
    (a ⊗ₜ[K] (1 : B)))
  let f : Z A ⊗[K] B →ₐ[K] A ⊗[K] B := tmap (Z A).val (AlgHom.id K B)
  have hf : Function.Injective f :=
    map_injective _ _ Subtype.val_injective Function.injective_id
  have hc (b : B) : Commute ((1 : Z A) ⊗ₜ[K] b) y := by
    change ((1 : Z A) ⊗ₜ[K] b) * y = y * ((1 : Z A) ⊗ₜ[K] b)
    apply hf
    dsimp only [f]
    simpa only [map_mul, Algebra.TensorProduct.map_tmul, Subalgebra.coe_val, Subalgebra.coe_one,
      AlgHom.id_apply, hy] using
      (Subalgebra.mem_center_iff.mp z.property ((1 : A) ⊗ₜ[K] b))
  obtain ⟨w, hw⟩ := exists_from_rightCenter hc
  refine ⟨w, Subtype.ext ?_⟩
  change tmap (Z A).val (Z B).val w = z.val
  rw [← hy, ← hw, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
  rfl

/-- Over a field the center of the algebra tensor product is the tensor product of the centers. -/
def centerEquiv : (Z A ⊗[K] Z B) ≃ₐ[K] Z (A ⊗[K] B) :=
  AlgEquiv.ofBijective fromCenters
    ⟨fun _ _ h => map_injective _ _ Subtype.val_injective Subtype.val_injective
        (congrArg Subtype.val h), fromCenters_surjective⟩

@[simp] theorem centerEquiv_tmul (a : Z A) (b : Z B) :
    (centerEquiv (K := K) (A := A) (B := B) (a ⊗ₜ[K] b)).val =
      (a.val ⊗ₜ[K] b.val) :=
  Algebra.TensorProduct.map_tmul (Z A).val (Z B).val a b

end Langlands.Algebra.TensorProductCenter
