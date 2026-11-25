module

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Coalgebra.Hom
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Subcoalgebras

A subcoalgebra of an `R`-coalgebra `C` is an `R`-submodule `D` of `C` with `Δ(D) ⊆ D ⊗ D`.
Over a commutative semiring the map `D ⊗[R] D → C ⊗[R] C` need not be injective, so the
condition is stated as: `Δ c` lies in the range of that map for every `c ∈ D`. Nothing else
is part of the data.

Over a field `k` the map `D ⊗[k] D → C ⊗[k] C` is injective, so `Δ` restricts to a unique
map `D → D ⊗[k] D`. With the restricted counit this makes `D` a coalgebra, and the inclusion
`D → C` a homomorphism of coalgebras.

## Main definitions

* `Langlands.Subcoalgebra R C`: the type of subcoalgebras of `C`, with its `SetLike`
  structure, its order, and the subcoalgebras `⊥` and `⊤`.
* `Langlands.Subcoalgebra.toSubmodule`, `Langlands.Subcoalgebra.ofSubmodule`: passage to
  and from submodules.
* `Langlands.Subcoalgebra.coalgebraOfInjective`: the coalgebra axioms pulled back along an
  injective linear map of vector spaces that respects comultiplication and counit.
* `Langlands.Subcoalgebra.instCoalgebra`: over a field, the coalgebra structure on a
  subcoalgebra.
* `Langlands.Subcoalgebra.subtype`: over a field, the inclusion as a coalgebra homomorphism.

## References

Milne, *Algebraic Groups* (2017), proof of Theorem 12.18, pp. 237–238, where a subcoalgebra
is a subspace `D` with `Δ(D) ⊆ D ⊗ D`. The paired Markdown page describes the proofs.
-/

public section

open scoped TensorProduct

namespace Langlands

universe u v

namespace Subcoalgebra

section CoalgebraStruct

variable {R : Type u} {C : Type v}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]

/-- For the whole module the closure condition is empty: the tensor square of `⊤` maps onto
`C ⊗[R] C`, so every comultiplication lies in its range. The statement needs the
comultiplication only, hence `CoalgebraStruct`. -/
theorem comul_mem_tensorSquare_top (c : C) :
    Coalgebra.comul (R := R) c ∈
      LinearMap.range (TensorProduct.map (⊤ : Submodule R C).subtype
        (⊤ : Submodule R C).subtype) := by
  have h : LinearMap.range (TensorProduct.map (⊤ : Submodule R C).subtype
      (⊤ : Submodule R C).subtype) = ⊤ :=
    (TensorProduct.range_mapIncl ⊤ ⊤).trans (TensorProduct.map₂_mk_top_top_eq_top R C C)
  rw [h]
  exact Submodule.mem_top

end CoalgebraStruct

end Subcoalgebra

variable (R : Type u) (C : Type v)
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- A subcoalgebra of the `R`-coalgebra `C`: an `R`-submodule `carrier` of `C` such that the
comultiplication of each of its elements comes from `carrier ⊗[R] carrier`. -/
structure Subcoalgebra where
  /-- The submodule of `C` underlying the subcoalgebra. -/
  carrier : Submodule R C
  /-- `Δ c` is in the image of `carrier ⊗[R] carrier` in `C ⊗[R] C` whenever `c ∈ carrier`. -/
  comul_mem' :
    ∀ ⦃c : C⦄, c ∈ carrier →
      Coalgebra.comul (R := R) c ∈
        LinearMap.range (TensorProduct.map carrier.subtype carrier.subtype)

namespace Subcoalgebra

variable {R C}

instance : SetLike (Subcoalgebra R C) C where
  coe D := D.carrier
  coe_injective := by
    rintro ⟨D, _⟩ ⟨E, _⟩ h
    obtain rfl : D = E := SetLike.coe_injective h
    rfl

instance : AddSubmonoidClass (Subcoalgebra R C) C where
  add_mem {D} := D.carrier.add_mem
  zero_mem D := D.carrier.zero_mem

instance : SMulMemClass (Subcoalgebra R C) R C where
  smul_mem {D} r := D.carrier.smul_mem r

instance : PartialOrder (Subcoalgebra R C) :=
  .ofSetLike (Subcoalgebra R C)

/-- A subcoalgebra viewed as a submodule. -/
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

/-- Subcoalgebras with the same elements are equal. -/
@[ext]
theorem ext {D E : Subcoalgebra R C} (h : ∀ c : C, c ∈ D ↔ c ∈ E) : D = E :=
  SetLike.ext h

/-- The closure condition, for membership in the subcoalgebra itself. -/
theorem comul_mem (D : Subcoalgebra R C) {c : C} (hc : c ∈ D) :
    Coalgebra.comul (R := R) (A := C) c ∈
      LinearMap.range (TensorProduct.map D.carrier.subtype D.carrier.subtype) :=
  D.comul_mem' hc

/-- The subcoalgebra on a submodule that satisfies the closure condition. -/
@[expose] def ofSubmodule (D : Submodule R C) (hD :
      ∀ ⦃c : C⦄, c ∈ D →
        Coalgebra.comul (R := R) (A := C) c ∈
          LinearMap.range (TensorProduct.map D.subtype D.subtype)) :
    Subcoalgebra R C :=
  ⟨D, hD⟩

@[simp]
theorem ofSubmodule_carrier (D : Submodule R C) (hD) :
    (ofSubmodule (R := R) (C := C) D hD).carrier = D :=
  rfl

@[simp]
theorem mem_ofSubmodule {D : Submodule R C} {hD} {c : C} :
    c ∈ ofSubmodule (R := R) (C := C) D hD ↔ c ∈ D :=
  Iff.rfl

/-- `C` itself is the largest subcoalgebra. -/
instance instTop : Top (Subcoalgebra R C) where
  top := ⟨⊤, fun c _ ↦ comul_mem_tensorSquare_top c⟩

@[simp]
theorem top_toSubmodule : (⊤ : Subcoalgebra R C).toSubmodule = (⊤ : Submodule R C) :=
  rfl

@[simp]
theorem mem_top (c : C) : c ∈ (⊤ : Subcoalgebra R C) :=
  Submodule.mem_top

/-- Every subcoalgebra lies in `⊤`, since this holds for the underlying submodules. -/
instance : OrderTop (Subcoalgebra R C) where
  top := ⊤
  le_top _ := toSubmodule_le_toSubmodule.mp le_top

/-- The zero submodule is the smallest subcoalgebra: `Δ 0 = 0` lies in every submodule. -/
instance instBot : Bot (Subcoalgebra R C) where
  bot := ⟨⊥, fun c hc ↦ by
    rw [(Submodule.mem_bot R).mp hc, map_zero]
    exact zero_mem _⟩

@[simp]
theorem bot_toSubmodule : (⊥ : Subcoalgebra R C).toSubmodule = (⊥ : Submodule R C) :=
  rfl

@[simp]
theorem mem_bot {c : C} : c ∈ (⊥ : Subcoalgebra R C) ↔ c = 0 :=
  Submodule.mem_bot R

/-- `⊥` lies in every subcoalgebra, since this holds for the underlying submodules. -/
instance : OrderBot (Subcoalgebra R C) where
  bot := ⊥
  bot_le _ := toSubmodule_le_toSubmodule.mp bot_le

end Subcoalgebra

end Langlands

namespace Langlands.Subcoalgebra

universe u' v'

open Coalgebra in
/-- A vector space `A` with a comultiplication and a counit is a coalgebra as soon as it has
an injective linear map `f` to a coalgebra `B` that commutes with both structure maps.

Each axiom for `A` is an equality in a tensor power of `A`. The corresponding tensor power of
`f` is injective because the base ring is a field, and it carries the two sides of the axiom
for `A` to the two sides of the axiom for `B`. -/
abbrev coalgebraOfInjective {k A B : Type*} [Field k]
    [AddCommGroup A] [Module k A] [CoalgebraStruct k A]
    [AddCommGroup B] [Module k B] [Coalgebra k B]
    (f : A →ₗ[k] B) (hf : Function.Injective f)
    (he : ∀ x : A, Coalgebra.counit (R := k) (f x) = Coalgebra.counit (R := k) x)
    (hd : ∀ x : A, TensorProduct.map f f (Coalgebra.comul (R := k) x) =
      Coalgebra.comul (R := k) (f x)) :
    Coalgebra k A where
  toCoalgebraStruct := inferInstance
  coassoc := by
    -- Both sides are compared in `B ⊗ (B ⊗ B)`, through `f ⊗ (f ⊗ f)`.
    have hΔ : TensorProduct.map f f ∘ₗ comul (R := k) (A := A) = comul ∘ₗ f :=
      LinearMap.ext hd
    refine LinearMap.ext fun x ↦
      TensorProduct.map_injective_of_flat_flat f (TensorProduct.map f f) hf
        (TensorProduct.map_injective_of_flat_flat f f hf hf) ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [TensorProduct.map_map_assoc, LinearMap.map_rTensor, LinearMap.map_lTensor, hΔ,
      ← LinearMap.rTensor_map, ← LinearMap.lTensor_map, hd, coassoc_apply]
  rTensor_counit_comp_comul := by
    -- Both sides are compared in `k ⊗ B`, through `k ⊗ f`.
    have hε : counit (R := k) (A := B) ∘ₗ f = counit := LinearMap.ext he
    refine LinearMap.ext fun x ↦
      Module.Flat.lTensor_preserves_injective_linearMap (M := k) f hf ?_
    calc f.lTensor k ((counit (R := k)).rTensor A (comul (R := k) x))
        = TensorProduct.map (counit (R := k)) f (comul (R := k) x) :=
          LinearMap.congr_fun (LinearMap.lTensor_comp_rTensor _ (counit (R := k)) f) _
      _ = (counit (R := k)).rTensor B (TensorProduct.map f f (comul (R := k) x)) := by
          rw [LinearMap.rTensor_map, hε]
      _ = 1 ⊗ₜ[k] f x := by rw [hd, rTensor_counit_comul]
      _ = f.lTensor k (1 ⊗ₜ[k] x) := rfl
  lTensor_counit_comp_comul := by
    -- Both sides are compared in `B ⊗ k`, through `f ⊗ k`.
    have hε : counit (R := k) (A := B) ∘ₗ f = counit := LinearMap.ext he
    refine LinearMap.ext fun x ↦
      Module.Flat.rTensor_preserves_injective_linearMap (M := k) f hf ?_
    calc f.rTensor k ((counit (R := k)).lTensor A (comul (R := k) x))
        = TensorProduct.map f (counit (R := k)) (comul (R := k) x) :=
          LinearMap.congr_fun (LinearMap.rTensor_comp_lTensor _ f (counit (R := k))) _
      _ = (counit (R := k)).lTensor B (TensorProduct.map f f (comul (R := k) x)) := by
          rw [LinearMap.lTensor_map, hε]
      _ = f x ⊗ₜ[k] 1 := by rw [hd, lTensor_counit_comul]
      _ = f.rTensor k (x ⊗ₜ[k] 1) := rfl

section Field

variable {k : Type u'} {C : Type v'}
variable [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

instance : AddSubgroupClass (Subcoalgebra k C) C where
  neg_mem {D} := D.carrier.neg_mem

instance (D : Subcoalgebra k C) : AddCommGroup D :=
  inferInstanceAs (AddCommGroup D.carrier)

instance (D : Subcoalgebra k C) : Module k D :=
  inferInstanceAs (Module k D.carrier)

/-- The map `D ⊗[k] D → C ⊗[k] C` induced by the inclusion of `D` on both factors. -/
@[expose] def tensorSquareInclusion (D : Subcoalgebra k C) : D ⊗[k] D →ₗ[k] C ⊗[k] C :=
  TensorProduct.map D.carrier.subtype D.carrier.subtype

/-- Vector spaces are flat, so the tensor square of an inclusion is injective. -/
theorem tensorSquareInclusion_injective (D : Subcoalgebra k C) :
    Function.Injective D.tensorSquareInclusion :=
  TensorProduct.map_injective_of_flat_flat _ _
    D.carrier.injective_subtype D.carrier.injective_subtype

/-- `D ⊗[k] D` as a subspace of `C ⊗[k] C`: the linear equivalence with the range of
`tensorSquareInclusion`. -/
@[expose] noncomputable def tensorSquareEquivRange (D : Subcoalgebra k C) :
    D ⊗[k] D ≃ₗ[k] LinearMap.range D.tensorSquareInclusion :=
  LinearEquiv.ofInjective D.tensorSquareInclusion D.tensorSquareInclusion_injective

/-- The comultiplication of `D`. For `x ∈ D` the element `Δ x` of `C ⊗[k] C` lies in the
range of `tensorSquareInclusion`, and `carrierComul D x` is its unique preimage. -/
@[expose] noncomputable def carrierComul (D : Subcoalgebra k C) : D →ₗ[k] D ⊗[k] D :=
  D.tensorSquareEquivRange.symm.toLinearMap ∘ₗ
    (Coalgebra.comul ∘ₗ D.carrier.subtype).codRestrict
      (LinearMap.range D.tensorSquareInclusion) (fun x => D.comul_mem x.property)

/-- Comultiplication and counit of a subcoalgebra: `carrierComul`, and the counit of `C`
restricted to `D`. -/
noncomputable instance instCoalgebraStruct (D : Subcoalgebra k C) : CoalgebraStruct k D where
  comul := D.carrierComul
  counit := Coalgebra.counit ∘ₗ D.carrier.subtype

@[simp]
theorem map_comul_subtype (D : Subcoalgebra k C) (x : D) :
    TensorProduct.map D.carrier.subtype D.carrier.subtype (Coalgebra.comul (R := k) (A := D) x) =
      Coalgebra.comul (R := k) (x : C) :=
  congrArg Subtype.val <| D.tensorSquareEquivRange.apply_symm_apply
    ((Coalgebra.comul ∘ₗ D.carrier.subtype).codRestrict
      (LinearMap.range D.tensorSquareInclusion) (fun x => D.comul_mem x.property) x)

@[simp]
theorem counit_subtype (D : Subcoalgebra k C) (x : D) :
    Coalgebra.counit (R := k) x = Coalgebra.counit (R := k) (x : C) := rfl

theorem map_comul_subtype_comp (D : Subcoalgebra k C) :
    TensorProduct.map D.carrier.subtype D.carrier.subtype ∘ₗ (Coalgebra.comul (R := k) (A := D)) =
      Coalgebra.comul ∘ₗ D.carrier.subtype :=
  LinearMap.ext D.map_comul_subtype

/-- Over a field a subcoalgebra is a coalgebra. The inclusion into `C` is injective and
commutes with comultiplication and counit, so the axioms follow from those of `C` by
`coalgebraOfInjective`. -/
noncomputable instance instCoalgebra (D : Subcoalgebra k C) : Coalgebra k D :=
  coalgebraOfInjective (A := D) D.carrier.subtype D.carrier.injective_subtype
    (fun _ => rfl) (map_comul_subtype D)

/-- The inclusion of a subcoalgebra, as a homomorphism of coalgebras. Its underlying linear
map is the inclusion of the submodule. -/
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
