/-
Copyright (c) 2026 The Tau Ceti contributors and the Langlands project contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Worker 16

The range-closure argument is adapted from TauCeti's Subcoalgebra/Map.lean
at commit 8428d6217f74afa72531df0bc85d7b57ab72810f.
The carrier coalgebra maps and scalar extension are new constructions.
-/
import Langlands.RingTheory.Coalgebra.Subcoalgebra.Basic
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Scalar extension of field subcoalgebras

The image of a coalgebra map is a subcoalgebra. Applying this to the
base change of a subcoalgebra inclusion gives its scalar extension.
-/

open scoped TensorProduct

namespace Langlands
namespace Subcoalgebra

universe u v w x

variable {k : Type u} [Field k]
variable {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
variable {E : Type w} [AddCommGroup E] [Module k E] [Coalgebra k E]

/-- The range of a coalgebra homomorphism, with its comultiplication closure. -/
def range (f : C →ₗc[k] E) : Subcoalgebra k E where
  carrier := LinearMap.range f.toLinearMap
  comul_mem' := by
    rintro _ ⟨c, rfl⟩
    refine ⟨TensorProduct.map f.toLinearMap.rangeRestrict
      f.toLinearMap.rangeRestrict (Coalgebra.comul (R := k) c), ?_⟩
    rw [TensorProduct.map_map]
    exact CoalgHomClass.map_comp_comul_apply f c

@[simp]
theorem range_toSubmodule (f : C →ₗc[k] E) :
    (range f).toSubmodule = LinearMap.range f.toLinearMap := rfl

@[simp]
theorem mem_range {f : C →ₗc[k] E} {e : E} :
    e ∈ range f ↔ ∃ c, f c = e := Iff.rfl

/-- Restrict the codomain of a coalgebra map to a subcoalgebra containing its image. -/
noncomputable def codRestrict (D : Subcoalgebra k E) (f : C →ₗc[k] E)
    (h : ∀ c, f c ∈ D) : C →ₗc[k] D where
  toLinearMap := f.toLinearMap.codRestrict D.toSubmodule h
  counit_comp := by
    ext c
    exact CoalgHomClass.counit_comp_apply f c
  map_comp_comul := by
    ext c
    apply D.tensorSquareInclusion_injective
    change TensorProduct.map D.toSubmodule.subtype D.toSubmodule.subtype
        (TensorProduct.map (f.toLinearMap.codRestrict D.toSubmodule h)
          (f.toLinearMap.codRestrict D.toSubmodule h) (Coalgebra.comul c)) =
      TensorProduct.map D.toSubmodule.subtype D.toSubmodule.subtype
        (Coalgebra.comul (R := k) (A := D) (⟨f c, h c⟩ : D))
    rw [TensorProduct.map_map]
    exact (CoalgHomClass.map_comp_comul_apply f c).trans
      (CoalgHomClass.map_comp_comul_apply D.subtype (⟨f c, h c⟩ : D)).symm

@[simp]
theorem codRestrict_apply (D : Subcoalgebra k E) (f : C →ₗc[k] E)
    (h : ∀ c, f c ∈ D) (c : C) :
    (codRestrict D f h c : E) = f c := rfl

@[simp]
theorem subtype_comp_codRestrict (D : Subcoalgebra k E) (f : C →ₗc[k] E)
    (h : ∀ c, f c ∈ D) :
    D.subtype.comp (codRestrict D f h) = f := by
  ext c
  rfl

/-- A coalgebra homomorphism with codomain restricted to its range. -/
noncomputable def rangeRestrict (f : C →ₗc[k] E) : C →ₗc[k] range f :=
  codRestrict (range f) f (fun c => ⟨c, rfl⟩)

@[simp]
theorem rangeRestrict_apply (f : C →ₗc[k] E) (c : C) :
    (rangeRestrict f c : E) = f c := rfl

theorem rangeRestrict_surjective (f : C →ₗc[k] E) :
    Function.Surjective (rangeRestrict f) := by
  rintro ⟨e, c, hc⟩
  exact ⟨c, Subtype.ext hc⟩

theorem rangeRestrict_injective (f : C →ₗc[k] E) (hf : Function.Injective f) :
    Function.Injective (rangeRestrict f) := by
  intro c d h
  exact hf (congrArg Subtype.val h)

/-- An injective coalgebra homomorphism identifies its source with its range. -/
noncomputable def equivRange (f : C →ₗc[k] E) (hf : Function.Injective f) :
    C ≃ₗc[k] range f :=
  CoalgEquiv.ofBijective
    ⟨rangeRestrict_injective f hf, rangeRestrict_surjective f⟩

@[simp]
theorem equivRange_apply (f : C →ₗc[k] E) (hf : Function.Injective f) (c : C) :
    (equivRange f hf c : E) = f c := rfl

variable (K : Type x) [Field K] [Algebra k K]

/-- The scalar extension of the inclusion of a subcoalgebra. -/
noncomputable def baseChangeMap (D : Subcoalgebra k C) :
    K ⊗[k] D →ₗc[K] K ⊗[k] C :=
  Coalgebra.TensorProduct.map (CoalgHom.id K K) D.subtype

@[simp]
theorem baseChangeMap_toLinearMap (D : Subcoalgebra k C) :
    (baseChangeMap K D).toLinearMap = D.toSubmodule.subtype.baseChange K := rfl

@[simp]
theorem baseChangeMap_tmul (D : Subcoalgebra k C) (a : K) (d : D) :
    baseChangeMap K D (a ⊗ₜ[k] d) = a ⊗ₜ[k] (d : C) := rfl

theorem baseChangeMap_injective (D : Subcoalgebra k C) :
    Function.Injective (baseChangeMap K D) :=
  Module.Flat.lTensor_preserves_injective_linearMap
    D.toSubmodule.subtype D.toSubmodule.subtype_injective

/-- Scalar extension as a subcoalgebra of the actual tensor-product coalgebra. -/
noncomputable def baseChange (D : Subcoalgebra k C) : Subcoalgebra K (K ⊗[k] C) :=
  range (baseChangeMap K D)

@[simp]
theorem baseChange_toSubmodule (D : Subcoalgebra k C) :
    (baseChange K D).toSubmodule = D.toSubmodule.baseChange K := rfl

theorem mem_baseChange (D : Subcoalgebra k C) (z : K ⊗[k] C) :
    z ∈ baseChange K D ↔ ∃ t : K ⊗[k] D, baseChangeMap K D t = z := Iff.rfl

theorem tmul_mem_baseChange (D : Subcoalgebra k C) (a : K) {c : C} (hc : c ∈ D) :
    a ⊗ₜ[k] c ∈ baseChange K D :=
  ⟨a ⊗ₜ[k] (⟨c, hc⟩ : D), rfl⟩

/-- The canonical coalgebra map to the carrier of the scalar-extended subcoalgebra. -/
noncomputable def toBaseChange (D : Subcoalgebra k C) :
    K ⊗[k] D →ₗc[K] baseChange K D :=
  rangeRestrict (baseChangeMap K D)

@[simp]
theorem toBaseChange_apply (D : Subcoalgebra k C) (z : K ⊗[k] D) :
    (toBaseChange K D z : K ⊗[k] C) = baseChangeMap K D z := rfl

@[simp]
theorem toBaseChange_tmul (D : Subcoalgebra k C) (a : K) (d : D) :
    (toBaseChange K D (a ⊗ₜ[k] d) : K ⊗[k] C) = a ⊗ₜ[k] (d : C) := rfl

theorem toBaseChange_bijective (D : Subcoalgebra k C) :
    Function.Bijective (toBaseChange K D) :=
  ⟨rangeRestrict_injective _ (baseChangeMap_injective K D), rangeRestrict_surjective _⟩

/-- Scalar extension of the carrier agrees with the carrier of scalar extension. -/
noncomputable def baseChangeEquiv (D : Subcoalgebra k C) :
    K ⊗[k] D ≃ₗc[K] baseChange K D :=
  equivRange (baseChangeMap K D) (baseChangeMap_injective K D)

@[simp]
theorem baseChangeEquiv_toCoalgHom (D : Subcoalgebra k C) :
    (baseChangeEquiv K D).toCoalgHom = toBaseChange K D := rfl

@[simp]
theorem baseChangeEquiv_apply (D : Subcoalgebra k C) (z : K ⊗[k] D) :
    (baseChangeEquiv K D z : K ⊗[k] C) = baseChangeMap K D z := rfl

@[simp]
theorem baseChangeEquiv_tmul (D : Subcoalgebra k C) (a : K) (d : D) :
    (baseChangeEquiv K D (a ⊗ₜ[k] d) : K ⊗[k] C) = a ⊗ₜ[k] (d : C) := rfl

@[simp]
theorem subtype_comp_toBaseChange (D : Subcoalgebra k C) :
    (baseChange K D).subtype.comp (toBaseChange K D) = baseChangeMap K D := by
  ext z
  rfl

@[simp]
theorem baseChange_bot :
    baseChange K (⊥ : Subcoalgebra k C) = ⊥ := by
  apply SetLike.coe_injective
  change ((⊥ : Submodule k C).baseChange K : Set (K ⊗[k] C)) =
    ((⊥ : Submodule K (K ⊗[k] C)) : Set (K ⊗[k] C))
  rw [Submodule.baseChange_bot]

@[simp]
theorem baseChange_top :
    baseChange K (⊤ : Subcoalgebra k C) = ⊤ := by
  apply SetLike.coe_injective
  change ((⊤ : Submodule k C).baseChange K : Set (K ⊗[k] C)) =
    ((⊤ : Submodule K (K ⊗[k] C)) : Set (K ⊗[k] C))
  rw [Submodule.baseChange_top]

theorem baseChange_mono {D F : Subcoalgebra k C} (h : D ≤ F) :
    baseChange K D ≤ baseChange K F :=
  Submodule.baseChange_mono K h

/-- Finite dimensionality is preserved by arbitrary extension of the field. -/
noncomputable instance instFiniteDimensionalBaseChange (D : Subcoalgebra k C)
    [FiniteDimensional k D] : FiniteDimensional K (baseChange K D) :=
  Module.Finite.of_surjective (toBaseChange K D).toLinearMap
    (toBaseChange_bijective K D).surjective

end Subcoalgebra
end Langlands
