/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Coalgebra.Hom
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Subcoalgebras

This file defines subcoalgebras by comultiplication closure. Over a field the carrier
inherits a coalgebra, constructed using injectivity of the tensor-square inclusion.
The inclusion is a coalgebra homomorphism. The closure-only interface is adapted from
TauCeti at commit 8428d621; the field carrier construction is new to this module.

## Main definitions

* `Langlands.Subcoalgebra`: a submodule stable under comultiplication.
* `Langlands.Subcoalgebra.toSubmodule`: the underlying submodule.
* `⊤` and `⊥`: the full and zero subcoalgebras.

## References

Milne, *Algebraic Groups* (2017), proof of Theorem 12.18, pp. 237–238:
`Δ(D) ⊆ D ⊗ D`. See the paired Markdown for source correspondence and derivation.
-/

public section

open scoped TensorProduct

namespace Langlands

universe u v

namespace Subcoalgebra

section CoalgebraStruct

variable {R : Type u} {C : Type v}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]

/-- The comultiplication of any element lies in the tensor square of the top submodule,
because the inclusion of `⊤` is surjective.

Only the comultiplication map is involved, not the coalgebra axioms, so this is stated over
`CoalgebraStruct`; it is what makes `⊤` a subcoalgebra. -/
theorem comul_mem_tensorSquare_top (c : C) :
    Coalgebra.comul (R := R) c ∈
      LinearMap.range (TensorProduct.map (⊤ : Submodule R C).subtype
        (⊤ : Submodule R C).subtype) :=
  LinearMap.mem_range.mpr
    (TensorProduct.map_surjective (fun c ↦ ⟨⟨c, Submodule.mem_top⟩, rfl⟩)
      (fun c ↦ ⟨⟨c, Submodule.mem_top⟩, rfl⟩) _)

end CoalgebraStruct

end Subcoalgebra

variable (R : Type u) (C : Type v)
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- A subcoalgebra of an `R`-coalgebra `C`.

It is an `R`-submodule `carrier` such that the comultiplication of every element of
`carrier` lies in the range of `carrier ⊗ carrier → C ⊗ C`. -/
structure Subcoalgebra where
  /-- The underlying submodule of a subcoalgebra. -/
  carrier : Submodule R C
  /-- The comultiplication of an element of the submodule lies in its tensor square. -/
  comul_mem' :
    ∀ ⦃c : C⦄, c ∈ carrier →
      Coalgebra.comul (R := R) c ∈
        LinearMap.range (TensorProduct.map carrier.subtype carrier.subtype)

namespace Subcoalgebra

variable {R C}

instance : SetLike (Subcoalgebra R C) C where
  coe D := D.carrier
  coe_injective D E h := by
    cases D with
    | mk carrier hD =>
    cases E with
    | mk carrier' hE =>
    congr
    exact SetLike.ext' h

instance : AddSubmonoidClass (Subcoalgebra R C) C where
  add_mem {D} := D.carrier.add_mem
  zero_mem D := D.carrier.zero_mem

instance : SMulMemClass (Subcoalgebra R C) R C where
  smul_mem {D} r {_} hc := D.carrier.smul_mem r hc

instance : PartialOrder (Subcoalgebra R C) :=
  .ofSetLike (Subcoalgebra R C) C

/-- The underlying submodule of a subcoalgebra. -/
@[expose] def toSubmodule (D : Subcoalgebra R C) : Submodule R C :=
  D.carrier

@[simp]
theorem mem_carrier {D : Subcoalgebra R C} {c : C} : c ∈ D.carrier ↔ c ∈ D :=
  Iff.rfl

@[simp]
theorem mem_toSubmodule {D : Subcoalgebra R C} {c : C} : c ∈ D.toSubmodule ↔ c ∈ D :=
  Iff.rfl

theorem toSubmodule_carrier (D : Subcoalgebra R C) : D.toSubmodule = D.carrier :=
  rfl

theorem le_def {D E : Subcoalgebra R C} : D ≤ E ↔ ∀ ⦃c : C⦄, c ∈ D → c ∈ E :=
  Iff.rfl

theorem toSubmodule_le_toSubmodule {D E : Subcoalgebra R C} :
    D.toSubmodule ≤ E.toSubmodule ↔ D ≤ E :=
  Iff.rfl

/-- Two subcoalgebras are equal when they contain the same elements. -/
@[ext]
theorem ext {D E : Subcoalgebra R C} (h : ∀ c : C, c ∈ D ↔ c ∈ E) : D = E :=
  SetLike.ext h

/-- The comultiplication of an element of a subcoalgebra belongs to its tensor square. -/
theorem comul_mem (D : Subcoalgebra R C) {c : C} (hc : c ∈ D) :
    Coalgebra.comul (R := R) (A := C) c ∈
      LinearMap.range (TensorProduct.map D.carrier.subtype D.carrier.subtype) :=
  D.comul_mem' hc

/-- Constructor from a submodule and the tensor-square stability condition. -/
@[expose] def ofSubmodule (D : Submodule R C) (hD :
      ∀ ⦃c : C⦄, c ∈ D →
        Coalgebra.comul (R := R) (A := C) c ∈
          LinearMap.range (TensorProduct.map D.subtype D.subtype)) :
    Subcoalgebra R C where
  carrier := D
  comul_mem' := hD

@[simp]
theorem ofSubmodule_carrier (D : Submodule R C) (hD) :
    (ofSubmodule (R := R) (C := C) D hD).carrier = D :=
  rfl

@[simp]
theorem mem_ofSubmodule {D : Submodule R C} {hD} {c : C} :
    c ∈ ofSubmodule (R := R) (C := C) D hD ↔ c ∈ D :=
  Iff.rfl

/-- The full coalgebra as a subcoalgebra. -/
instance instTop : Top (Subcoalgebra R C) where
  top :=
    { carrier := ⊤
      comul_mem' := fun c _ ↦ comul_mem_tensorSquare_top c }

@[simp]
theorem top_toSubmodule : (⊤ : Subcoalgebra R C).toSubmodule = (⊤ : Submodule R C) :=
  rfl

@[simp]
theorem mem_top (c : C) : c ∈ (⊤ : Subcoalgebra R C) :=
  Submodule.mem_top

instance : OrderTop (Subcoalgebra R C) where
  top := ⊤
  le_top _ _ _ := Submodule.mem_top

/-- The zero submodule as a subcoalgebra. -/
instance instBot : Bot (Subcoalgebra R C) where
  bot :=
    { carrier := ⊥
      comul_mem' := by
        intro c hc
        rw [Submodule.mem_bot] at hc
        subst c
        exact ⟨0, by simp⟩ }

@[simp]
theorem bot_toSubmodule : (⊥ : Subcoalgebra R C).toSubmodule = (⊥ : Submodule R C) :=
  rfl

@[simp]
theorem mem_bot {c : C} : c ∈ (⊥ : Subcoalgebra R C) ↔ c = 0 :=
  Submodule.mem_bot (R := R) (M := C)

/-- The zero subcoalgebra is contained in every subcoalgebra. -/
instance : OrderBot (Subcoalgebra R C) where
  bot := ⊥
  bot_le D c hc := by
    rw [mem_bot] at hc
    rw [hc]
    exact zero_mem D

end Subcoalgebra

end Langlands

namespace Langlands.Subcoalgebra

universe u' v'

/-- Inherit the coalgebra laws along an injective map preserving the two structure maps. -/
abbrev coalgebraOfInjective {k A B : Type*} [Field k]
    [AddCommGroup A] [Module k A] [CoalgebraStruct k A]
    [AddCommGroup B] [Module k B] [Coalgebra k B]
    (f : A →ₗ[k] B) (hf : Function.Injective f)
    (he : ∀ x : A, Coalgebra.counit (R := k) (f x) = Coalgebra.counit (R := k) x)
    (hd : ∀ x : A, TensorProduct.map f f (Coalgebra.comul (R := k) x) =
      Coalgebra.comul (R := k) (f x)) :
    Coalgebra k A where
  toCoalgebraStruct := inferInstance
  rTensor_counit_comp_comul := by
    have h : TensorProduct.map (LinearMap.id : k →ₗ[k] k) f ∘ₗ
        (Coalgebra.counit (R := k) (A := A)).rTensor A =
        (Coalgebra.counit (R := k) (A := B)).rTensor B ∘ₗ TensorProduct.map f f := by
      ext a b
      change Coalgebra.counit (R := k) a ⊗ₜ[k] f b =
        Coalgebra.counit (R := k) (f a) ⊗ₜ[k] f b
      rw [he a]
    apply LinearMap.ext
    intro x
    apply TensorProduct.map_injective_of_flat_flat
      (LinearMap.id : k →ₗ[k] k) f Function.injective_id hf
    change (TensorProduct.map LinearMap.id f ∘ₗ
      (Coalgebra.counit (R := k) (A := A)).rTensor A) (Coalgebra.comul x) = _
    rw [h]
    change (Coalgebra.counit (R := k) (A := B)).rTensor B
      (TensorProduct.map f f (Coalgebra.comul x)) =
        TensorProduct.map LinearMap.id f (1 ⊗ₜ[k] x)
    rw [hd, Coalgebra.rTensor_counit_comul, TensorProduct.map_tmul, LinearMap.id_apply]
  lTensor_counit_comp_comul := by
    have h : TensorProduct.map f (LinearMap.id : k →ₗ[k] k) ∘ₗ
        (Coalgebra.counit (R := k) (A := A)).lTensor A =
        (Coalgebra.counit (R := k) (A := B)).lTensor B ∘ₗ TensorProduct.map f f := by
      ext a b
      change f a ⊗ₜ[k] Coalgebra.counit (R := k) b =
        f a ⊗ₜ[k] Coalgebra.counit (R := k) (f b)
      rw [he b]
    apply LinearMap.ext
    intro x
    apply TensorProduct.map_injective_of_flat_flat
      f (LinearMap.id : k →ₗ[k] k) hf Function.injective_id
    change (TensorProduct.map f LinearMap.id ∘ₗ
      (Coalgebra.counit (R := k) (A := A)).lTensor A) (Coalgebra.comul x) = _
    rw [h]
    change (Coalgebra.counit (R := k) (A := B)).lTensor B
      (TensorProduct.map f f (Coalgebra.comul x)) =
        TensorProduct.map f LinearMap.id (x ⊗ₜ[k] 1)
    rw [hd, Coalgebra.lTensor_counit_comul, TensorProduct.map_tmul, LinearMap.id_apply]
  coassoc := by
    have hl : TensorProduct.map f (TensorProduct.map f f) ∘ₗ
        TensorProduct.assoc k A A A ∘ₗ (Coalgebra.comul (R := k) (A := A)).rTensor A =
        TensorProduct.assoc k B B B ∘ₗ (Coalgebra.comul (R := k) (A := B)).rTensor B ∘ₗ
          TensorProduct.map f f := by
      ext a b
      change TensorProduct.map f (TensorProduct.map f f)
        (TensorProduct.assoc k A A A (Coalgebra.comul a ⊗ₜ[k] b)) =
        TensorProduct.assoc k B B B (Coalgebra.comul (f a) ⊗ₜ[k] f b)
      rw [TensorProduct.map_map_assoc, TensorProduct.map_tmul]
      rw [hd a]
    have hr : TensorProduct.map f (TensorProduct.map f f) ∘ₗ
        (Coalgebra.comul (R := k) (A := A)).lTensor A =
        (Coalgebra.comul (R := k) (A := B)).lTensor B ∘ₗ TensorProduct.map f f := by
      ext a b
      change f a ⊗ₜ[k] TensorProduct.map f f (Coalgebra.comul b) =
        f a ⊗ₜ[k] Coalgebra.comul (f b)
      rw [hd b]
    apply LinearMap.ext
    intro x
    apply TensorProduct.map_injective_of_flat_flat f (TensorProduct.map f f) hf
      (TensorProduct.map_injective_of_flat_flat f f hf hf)
    change (TensorProduct.map f (TensorProduct.map f f) ∘ₗ
      TensorProduct.assoc k A A A ∘ₗ (Coalgebra.comul (R := k) (A := A)).rTensor A)
        (Coalgebra.comul x) =
      (TensorProduct.map f (TensorProduct.map f f) ∘ₗ
        (Coalgebra.comul (R := k) (A := A)).lTensor A) (Coalgebra.comul x)
    rw [hl, hr]
    simpa only [LinearMap.comp_apply, hd x, LinearEquiv.coe_coe]
      using Coalgebra.coassoc_apply (R := k) (f x)

section Field

variable {k : Type u'} {C : Type v'}
variable [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

instance : AddSubgroupClass (Subcoalgebra k C) C where
  neg_mem {D} := D.carrier.neg_mem

instance (D : Subcoalgebra k C) : AddCommGroup D :=
  inferInstanceAs (AddCommGroup D.carrier)

instance (D : Subcoalgebra k C) : Module k D :=
  inferInstanceAs (Module k D.carrier)

/-- The actual inclusion of the tensor square of a subcoalgebra. -/
@[expose] def tensorSquareInclusion (D : Subcoalgebra k C) : D ⊗[k] D →ₗ[k] C ⊗[k] C :=
  TensorProduct.map D.carrier.subtype D.carrier.subtype

/-- Over a field, the tensor-square inclusion is injective. -/
theorem tensorSquareInclusion_injective (D : Subcoalgebra k C) :
    Function.Injective D.tensorSquareInclusion :=
  TensorProduct.map_injective_of_flat_flat _ _
    D.carrier.subtype_injective D.carrier.subtype_injective

/-- The tensor square is linearly equivalent to its image in the ambient tensor square. -/
@[expose] noncomputable def tensorSquareEquivRange (D : Subcoalgebra k C) :
    D ⊗[k] D ≃ₗ[k] LinearMap.range D.tensorSquareInclusion :=
  LinearEquiv.ofInjective D.tensorSquareInclusion D.tensorSquareInclusion_injective

/-- Comultiplication induced by closure and the injectivity of the tensor-square inclusion. -/
@[expose] noncomputable def carrierComul (D : Subcoalgebra k C) : D →ₗ[k] D ⊗[k] D :=
  D.tensorSquareEquivRange.symm.toLinearMap ∘ₗ
    (Coalgebra.comul ∘ₗ D.carrier.subtype).codRestrict
      (LinearMap.range D.tensorSquareInclusion) (fun x => D.comul_mem x.property)

/-- The carrier counit is the ambient counit restricted to the submodule. -/
noncomputable instance instCoalgebraStruct (D : Subcoalgebra k C) : CoalgebraStruct k D where
  comul := D.carrierComul
  counit := Coalgebra.counit ∘ₗ D.carrier.subtype

@[simp]
theorem map_comul_subtype (D : Subcoalgebra k C) (x : D) :
    TensorProduct.map D.carrier.subtype D.carrier.subtype (Coalgebra.comul (R := k) (A := D) x) =
      Coalgebra.comul (R := k) (x : C) := by
  change D.tensorSquareInclusion (D.tensorSquareEquivRange.symm _) = _
  exact LinearEquiv.ofInjective_symm_apply _ _

@[simp]
theorem counit_subtype (D : Subcoalgebra k C) (x : D) :
    Coalgebra.counit (R := k) x = Coalgebra.counit (R := k) (x : C) := rfl

theorem map_comul_subtype_comp (D : Subcoalgebra k C) :
    TensorProduct.map D.carrier.subtype D.carrier.subtype ∘ₗ (Coalgebra.comul (R := k) (A := D)) =
      Coalgebra.comul ∘ₗ D.carrier.subtype :=
  LinearMap.ext (D.map_comul_subtype)

/-- The carrier coalgebra is determined by comultiplication closure; its laws are inherited
through the injective inclusions into the ambient tensor powers. -/
noncomputable instance instCoalgebra (D : Subcoalgebra k C) : Coalgebra k D :=
  coalgebraOfInjective (A := D) D.carrier.subtype D.carrier.subtype_injective
    (fun _ => rfl) (map_comul_subtype D)

/-- The inclusion into the ambient coalgebra, with the actual submodule inclusion underneath. -/
@[expose] def subtype (D : Subcoalgebra k C) : D →ₗc[k] C where
  toLinearMap := D.carrier.subtype
  counit_comp := rfl
  map_comp_comul := D.map_comul_subtype_comp

@[simp]
theorem subtype_toLinearMap (D : Subcoalgebra k C) :
    D.subtype.toLinearMap = D.toSubmodule.subtype := rfl

@[simp]
theorem subtype_apply (D : Subcoalgebra k C) (x : D) : D.subtype x = (x : C) := rfl

theorem subtype_injective (D : Subcoalgebra k C) : Function.Injective D.subtype :=
  Subtype.val_injective

end Field

end Langlands.Subcoalgebra
