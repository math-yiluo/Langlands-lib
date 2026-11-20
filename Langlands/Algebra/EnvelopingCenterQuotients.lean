import Langlands.Algebra.TensorProductCenter
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Quotients of centers of product enveloping algebras -/

noncomputable section

universe u v w

open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Algebra

section Quotient

variable {K : Type u} [Field K] {A : Type v} {B : Type w}
  [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

/-- Contraction of an ideal with finite-dimensional quotient has finite-dimensional quotient. -/
theorem quotientFinite_comap (f : A →ₐ[K] B) (I : Ideal B)
    [Module.Finite K (B ⧸ I)] : Module.Finite K (A ⧸ I.comap f.toRingHom) :=
  Module.Finite.of_injective (Ideal.quotientMapₐ I f le_rfl).toLinearMap
    Ideal.quotientMap_injective

/-- Extension along a module-finite algebra map preserves finite-dimensional quotients. -/
theorem quotientFinite_map (f : A →ₐ[K] B) (hf : f.Finite) (I : Ideal A)
    [Module.Finite K (A ⧸ I)] : Module.Finite K (B ⧸ I.map f.toRingHom) := by
  let J := I.map f.toRingHom
  let : Algebra A B := f.toRingHom.toAlgebra
  have : Module.Finite A B := hf
  have hIJ : I ≤ J.comap (algebraMap A B) := Ideal.le_comap_map
  let : Algebra (A ⧸ I) (B ⧸ J) := Ideal.Quotient.algebraQuotientOfLEComap hIJ
  have : IsScalarTower A (A ⧸ I) (B ⧸ J) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K (A ⧸ I) (B ⧸ J) := IsScalarTower.of_algebraMap_eq fun c => by
    change Ideal.Quotient.mk J (algebraMap K B c) =
      Ideal.Quotient.mk J (f (algebraMap K A c))
    rw [f.commutes]
  have : Module.Finite A (B ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A J).toLinearMap Ideal.Quotient.mk_surjective
  have : Module.Finite (A ⧸ I) (B ⧸ J) := Module.Finite.of_restrictScalars_finite A _ _
  exact Module.Finite.trans (A ⧸ I) (B ⧸ J)

/-- A quotient of a tensor product is finite-dimensional if its contractions to both factors have
finite-dimensional quotients. -/
theorem quotientFinite_tensorProduct (I : Ideal (A ⊗[K] B))
    (hA : Module.Finite K (A ⧸ I.comap
      (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] B).toRingHom))
    (hB : Module.Finite K (B ⧸ I.comap
      (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B).toRingHom)) :
    Module.Finite K ((A ⊗[K] B) ⧸ I) := by
  let l : A →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeLeft
  let r : B →ₐ[K] A ⊗[K] B := Algebra.TensorProduct.includeRight
  let IA := I.comap l.toRingHom
  let IB := I.comap r.toRingHom
  have : Module.Finite K (A ⧸ IA) := hA
  have : Module.Finite K (B ⧸ IB) := hB
  let fa := Ideal.quotientMapₐ I l (I := IA) le_rfl
  let fb := Ideal.quotientMapₐ I r (I := IB) le_rfl
  let f := Algebra.TensorProduct.lift fa fb (fun _ _ => Commute.all _ _)
  refine Module.Finite.of_surjective f.toLinearMap ?_
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    refine ⟨Ideal.Quotient.mk IA x ⊗ₜ[K] Ideal.Quotient.mk IB y, ?_⟩
    simp only [AlgHom.toLinearMap_apply, f, fa, fb]
    rw [Algebra.TensorProduct.lift_tmul, Ideal.quotient_map_mkₐ, Ideal.quotient_map_mkₐ, ← map_mul]
    exact congrArg (Ideal.Quotient.mk I) (by
      change (x ⊗ₜ[K] (1 : B)) * ((1 : A) ⊗ₜ[K] y) = x ⊗ₜ[K] y
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul])
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add, hx', hy', map_add]⟩

end Quotient

namespace LieEnvelopingEquiv

attribute [local instance 100] LieRing.ofAssociativeRing

section Functor

variable {K : Type u} [CommRing K]
  {A B C : Type*} [LieRing A] [LieRing B] [LieRing C]
  [LieAlgebra K A] [LieAlgebra K B] [LieAlgebra K C]

theorem map_comp (f : B →ₗ⁅K⁆ C) (g : A →ₗ⁅K⁆ B) :
    (map f).comp (map g) = map (f.comp g) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro X
  change map f (map g (UniversalEnvelopingAlgebra.ι K X)) =
    map (f.comp g) (UniversalEnvelopingAlgebra.ι K X)
  simp only [map_generator, LieHom.comp_apply]

private theorem commute_enveloping_of_generators {D : Type*} [Ring D] [Algebra K D]
    (f : UniversalEnvelopingAlgebra K A →ₐ[K] D) (d : D)
    (h : ∀ X, Commute d (f (UniversalEnvelopingAlgebra.ι K X)))
    (u : UniversalEnvelopingAlgebra K A) : Commute d (f u) := by
  refine Quotient.inductionOn u ?_
  intro t
  change Commute d (f ((UniversalEnvelopingAlgebra.mkAlgHom K A) t))
  induction t using TensorAlgebra.induction with
  | algebraMap k =>
    rw [AlgHom.commutes, AlgHom.commutes]
    exact (Algebra.commutes k d).symm
  | ι X => exact h X
  | mul x y hx hy => simpa only [map_mul] using hx.mul_right hy
  | add x y hx hy => simpa only [map_add] using hx.add_right hy

/-- An inclusion with a commuting complementary direction carries the enveloping center to
the enveloping center. -/
def centerMapOfComplement (f : A →ₗ⁅K⁆ B) (p : B → A)
    (hf : ∀ X Y, ⁅X - f (p X), f Y⁆ = 0) :
    Subalgebra.center K (UniversalEnvelopingAlgebra K A) →ₐ[K]
      Subalgebra.center K (UniversalEnvelopingAlgebra K B) :=
  (map f).comp (Subalgebra.center K (UniversalEnvelopingAlgebra K A)).val |>.codRestrict _
    (fun z => by
      apply Subalgebra.mem_center_iff.mpr
      intro u
      change u * map f z.val = map f z.val * u
      suffices h : ∀ X, Commute (map f z.val) (UniversalEnvelopingAlgebra.ι K X) from
        (commute_enveloping_of_generators (AlgHom.id K _) _ h u).symm.eq
      intro X
      have hp := (Commute.symm (Subalgebra.mem_center_iff.mp z.property
        (UniversalEnvelopingAlgebra.ι K (p X)) : Commute _ _)).map (map f)
      rw [map_generator] at hp
      have hc : ∀ Y, Commute (UniversalEnvelopingAlgebra.ι K (X - f (p X)))
          (map f (UniversalEnvelopingAlgebra.ι K Y)) := by
        intro Y
        apply sub_eq_zero.mp
        rw [map_generator, ← Ring.lie_def, ← LieHom.map_lie, hf, map_zero]
      have h := (commute_enveloping_of_generators (map f) _ hc z.val).symm.add_right hp
      rw [← map_add, sub_add_cancel] at h
      exact h)

@[simp]
theorem centerMapOfComplement_val (f : A →ₗ⁅K⁆ B) (p : B → A)
    (hf : ∀ X Y, ⁅X - f (p X), f Y⁆ = 0)
    (z : Subalgebra.center K (UniversalEnvelopingAlgebra K A)) :
    (centerMapOfComplement f p hf z).val = map f z.val :=
  rfl

end Functor

section Product

variable (K : Type u) [Field K] (A : Type v) (B : Type w)
  [LieRing A] [LieRing B] [LieAlgebra K A] [LieAlgebra K B]

local notation "UA" => UniversalEnvelopingAlgebra K A
local notation "UB" => UniversalEnvelopingAlgebra K B
local notation "ZA" => Subalgebra.center K UA
local notation "ZB" => Subalgebra.center K UB

theorem envelopingProductCenter_symm_tmul_val (x : ZA) (y : ZB) :
    ((envelopingProductCenter K A B).symm (x ⊗ₜ[K] y)).val =
      map (LieHom.inl K A B) x.val * map (LieHom.inr K A B) y.val := by
  rw [← envelopingProduct_symm_tmul]
  apply (envelopingProduct K A B).injective
  rw [AlgEquiv.apply_symm_apply, ← center_apply]
  change (center (envelopingProduct K A B)
    ((center (envelopingProduct K A B)).symm (tensorProductCenter K UA UB (x ⊗ₜ[K] y)))).val = _
  rw [AlgEquiv.apply_symm_apply, tensorProductCenter_tmul]

theorem envelopingProductCenter_symm_left_val (x : ZA) :
    ((envelopingProductCenter K A B).symm (x ⊗ₜ[K] (1 : ZB))).val =
      map (LieHom.inl K A B) x.val := by
  rw [envelopingProductCenter_symm_tmul_val]
  simp only [Subalgebra.coe_one, map_one, mul_one]

theorem envelopingProductCenter_symm_right_val (y : ZB) :
    ((envelopingProductCenter K A B).symm ((1 : ZA) ⊗ₜ[K] y)).val =
      map (LieHom.inr K A B) y.val := by
  rw [envelopingProductCenter_symm_tmul_val]
  simp only [Subalgebra.coe_one, map_one, one_mul]

end Product

end LieEnvelopingEquiv

end Langlands.Algebra
