import Langlands.Algebra.NonUnitalModuleFinitenessStatements
import Langlands.Algebra.NonUnitalModuleSubobject
import Langlands.Algebra.IntegerOriginalSubmoduleGenerationProof
import Langlands.CategoryTheory.RenardModuleFiniteTypeProof
import Langlands.CategoryTheory.RenardModuleNoetherianProof
import Mathlib.Order.Bounds.OrderIso

/-!
# Object finiteness for original additive nonunital modules: proof

Proof of `NonUnitalModuleFinitenessStatement`. The source predicates of Renard's A.I.3,
printed pp. 248–249, transfer along an order isomorphism of categorical subobject types.
The subobjects of `M` are identified with those of the integer-unitized module
`IntegerUnitization.extendObj A M` through the published `subobjectOrderIso`, and the
published unital-module comparisons and original-action generation comparisons finish.
-/

set_option autoImplicit false

open CategoryTheory

namespace Langlands.Algebra.NonUnitalModuleFiniteness

section Transport

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {X : C} {Y : D}

/-- Subobject unions transfer along an order isomorphism of subobject types. -/
theorem hasSubobjectUnions_of_orderIso (e : Subobject X ≃o Subobject Y)
    (h : Langlands.Renard.HasSubobjectUnions Y) : Langlands.Renard.HasSubobjectUnions X := by
  intro S
  obtain ⟨U, hU⟩ := h (e '' S)
  exact ⟨e.symm U, e.isLUB_image.mp hU⟩

/-- The finite-subcover property transfers along an order isomorphism of subobject types. -/
theorem hasFiniteSubcoverProperty_of_orderIso (e : Subobject X ≃o Subobject Y)
    (h : Langlands.Renard.HasFiniteSubcoverProperty Y) :
    Langlands.Renard.HasFiniteSubcoverProperty X := by
  classical
  refine ⟨hasSubobjectUnions_of_orderIso e h.1, fun S hS => ?_⟩
  have hcover : IsLUB (e '' S) ⊤ := by
    simpa using e.isLUB_image'.mpr hS
  obtain ⟨T, hT, hcoverT⟩ := h.2 (e '' S) hcover
  refine ⟨T.image e.symm, ?_, ?_⟩
  · intro P hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨R, hR, rfl⟩ := hT hQ
    simpa using hR
  · rw [Finset.coe_image]
    simpa using e.symm.isLUB_image'.mpr hcoverT

/-- Renard's Noetherian-object condition transfers along an order isomorphism of
subobject types. -/
theorem isNoetherianObject_of_orderIso (e : Subobject X ≃o Subobject Y)
    (h : Langlands.Renard.IsNoetherianObject Y) : Langlands.Renard.IsNoetherianObject X := by
  intro S hS
  obtain ⟨P, ⟨P', hP', rfl⟩, hmax⟩ := h (e '' S) (hS.image e)
  exact ⟨P', hP', fun Q hQ hle => e.injective (hmax (e Q) ⟨Q, hQ, rfl⟩ (e.monotone hle))⟩

/-- The finite-subcover property is invariant under an order isomorphism of subobject types. -/
theorem hasFiniteSubcoverProperty_congr (e : Subobject X ≃o Subobject Y) :
    Langlands.Renard.HasFiniteSubcoverProperty X ↔
      Langlands.Renard.HasFiniteSubcoverProperty Y :=
  ⟨hasFiniteSubcoverProperty_of_orderIso e.symm, hasFiniteSubcoverProperty_of_orderIso e⟩

/-- The Noetherian-object condition is invariant under an order isomorphism of subobject
types. -/
theorem isNoetherianObject_congr (e : Subobject X ≃o Subobject Y) :
    Langlands.Renard.IsNoetherianObject X ↔ Langlands.Renard.IsNoetherianObject Y :=
  ⟨isNoetherianObject_of_orderIso e.symm, isNoetherianObject_of_orderIso e⟩

end Transport

universe uA uM

section Object

variable {A : Type uA} [NonUnitalRing A]

/-- Categorical subobjects of `M` are those of its integer-unitized module, through the
published comparison with the original stable additive subgroups. -/
noncomputable def subobjectExtendOrderIso (M : NonUnitalModuleCat.{uA, uM} A) :
    Subobject M ≃o Subobject (IntegerUnitization.extendObj A M) :=
  ((NonUnitalModuleCat.subobjectOrderIso M).trans
    (NonUnitalSubmodule.intUnitizedOrderIso (A := A) (M := M))).trans
    (ModuleCat.subobjectModule (IntegerUnitization.extendObj A M)).symm

/-- Component 2 for one object. -/
theorem finiteSubcover_iff_finite (M : NonUnitalModuleCat.{uA, uM} A) :
    Langlands.Renard.HasFiniteSubcoverProperty M ↔
      (letI := CompatibleUnitization.module
        (NonUnitalModule.toIntLinearEndHom (A := A) (V := M));
        Module.Finite (Unitization ℤ A) M) :=
  (hasFiniteSubcoverProperty_congr (subobjectExtendOrderIso M)).trans
    (Langlands.Renard.ModuleFiniteType.finiteSubcover_iff_finite
      (IntegerUnitization.extendObj A M))

/-- Component 1 for one object. -/
theorem finiteType_iff_finite (M : NonUnitalModuleCat.{uA, uM} A) :
    Langlands.Renard.IsFiniteTypeObject M ↔
      (letI := CompatibleUnitization.module
        (NonUnitalModule.toIntLinearEndHom (A := A) (V := M));
        Module.Finite (Unitization ℤ A) M) :=
  (Langlands.Renard.finiteTypeFiniteSubcover (NonUnitalModuleCat.{uA, uM} A) M).trans
    (finiteSubcover_iff_finite M)

/-- Component 3 for one object. -/
theorem noetherianObject_iff_isNoetherian (M : NonUnitalModuleCat.{uA, uM} A) :
    Langlands.Renard.IsNoetherianObject M ↔
      (letI := CompatibleUnitization.module
        (NonUnitalModule.toIntLinearEndHom (A := A) (V := M));
        IsNoetherian (Unitization ℤ A) M) :=
  (isNoetherianObject_congr (subobjectExtendOrderIso M)).trans
    (Langlands.Renard.ModuleNoetherian.object_iff (Unitization ℤ A)
      (IntegerUnitization.extendObj A M))

/-- Component 4 for one object. -/
theorem finiteType_iff_original_stable_generators (M : NonUnitalModuleCat.{uA, uM} A) :
    Langlands.Renard.IsFiniteTypeObject M ↔
      ∃ S : Finset M, ∀ P : NonUnitalSubmodule A M,
        (↑S : Set M) ⊆ P → ∀ m : M, m ∈ P :=
  (finiteType_iff_finite M).trans
    IntegerOriginalSubmoduleGeneration.finite_iff_original_stable_generators

/-- Component 5 for one object. -/
theorem noetherianObject_iff_original_stable_generators (M : NonUnitalModuleCat.{uA, uM} A) :
    Langlands.Renard.IsNoetherianObject M ↔
      ∀ P : NonUnitalSubmodule A M,
        ∃ S : Finset M, (↑S : Set M) ⊆ P ∧
          ∀ Q : NonUnitalSubmodule A M, (↑S : Set M) ⊆ Q → P ≤ Q :=
  (noetherianObject_iff_isNoetherian M).trans
    IntegerOriginalSubmoduleGeneration.noetherian_iff_original_stable_generators

end Object

/-- The closed finite-type comparison. -/
theorem finiteType : FiniteTypeStatement.{uA, uM} :=
  fun _ _ M => finiteType_iff_finite M

/-- The closed finite-subcover comparison. -/
theorem finiteSubcover : FiniteSubcoverStatement.{uA, uM} :=
  fun _ _ M => finiteSubcover_iff_finite M

/-- The closed Noetherian comparison. -/
theorem noetherian : NoetherianStatement.{uA, uM} :=
  fun _ _ M => noetherianObject_iff_isNoetherian M

/-- The closed whole-module original-generation comparison. -/
theorem finiteGeneration : FiniteGenerationStatement.{uA, uM} :=
  fun _ _ M => finiteType_iff_original_stable_generators M

/-- The closed all-subgroups original-generation comparison. -/
theorem noetherianGeneration : NoetherianGenerationStatement.{uA, uM} :=
  fun _ _ M => noetherianObject_iff_original_stable_generators M

/-- The five comparisons, in the order of the published aggregate. -/
theorem nonUnitalModuleFiniteness : NonUnitalModuleFinitenessStatement.{uA, uM} :=
  ⟨finiteType, finiteSubcover, noetherian, finiteGeneration, noetherianGeneration⟩

end Langlands.Algebra.NonUnitalModuleFiniteness
