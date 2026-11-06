import Langlands.Algebra.RenardFullModuleAxiomStatements
import Langlands.Algebra.NonUnitalModuleFinitenessProof
import Langlands.CategoryTheory.RenardModuleFiniteTypeProof
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.CompactlyGenerated.Basic

/-!
# Source axioms for Renard's full module categories: proof

Proof of `FullModuleAxiomsStatement`, Renard (9 July 2026), A.VI.3, printed p.264 / PDF270.
Each subobject type used here is order isomorphic to a lattice of submodules: in
`ModuleCat A` by Mathlib's `ModuleCat.subobjectModule`, and in `NonUnitalModuleCat A`
through the published integer-unitization comparison. Directed distributivity and local
finite type are transported from submodules. Coproducts come from Mathlib's colimits in
`ModuleCat`, transported along the integer-unitization equivalence in the nonunital case.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.RenardFullModuleAxiomProof

open RenardFullModuleAxiomStatements

universe u v uR uV uA uI uM

section Transport

variable {C : Type u} [Category.{v} C] {R : Type uR} [Ring R]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- An order isomorphism restricts to the lower intervals of corresponding elements. -/
def iicOrderIso {α : Type*} {β : Type*} [Preorder α] [Preorder β] (e : α ≃o β) (x : α) :
    Set.Iic x ≃o Set.Iic (e x) where
  toFun y := ⟨e y, e.monotone y.2⟩
  invFun y := ⟨e.symm y, e.symm_apply_le.mpr y.2⟩
  left_inv y := Subtype.ext (e.symm_apply_apply y.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_rel_iff' := e.le_iff_le

/-- Directed sums and their intersections with a fixed element, transported from
submodules. The family may be empty. -/
theorem directedSums_of_orderIso {α : Type*} [SemilatticeInf α] (e : α ≃o Submodule R V)
    {I : Type uI} (F : I → α) (hF : Directed (· ≤ ·) F) (N : α) :
    ∃ U : α, IsLUB (Set.range F) U ∧ IsLUB (Set.range fun i => N ⊓ F i) (N ⊓ U) := by
  have hE : Directed (· ≤ ·) (fun i => e (F i)) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hF i j
    exact ⟨k, e.monotone hik, e.monotone hjk⟩
  let U : α := e.symm (⨆ i, e (F i))
  have heU : e U = ⨆ i, e (F i) := e.apply_symm_apply _
  refine ⟨U, ?_, ?_⟩
  · apply (e.isLUB_image (s := Set.range F) (x := ⨆ i, e (F i))).1
    simpa only [← Set.range_comp'] using
      (isLUB_iSup : IsLUB (Set.range (fun i => e (F i))) (⨆ i, e (F i)))
  · have heInf : e (N ⊓ U) = ⨆ i, e (N ⊓ F i) := by
      rw [map_inf, heU, hE.inf_iSup_eq]
      simp only [map_inf]
    apply (e.isLUB_image' (s := Set.range fun i => N ⊓ F i)).1
    simpa only [← Set.range_comp', heInf] using
      (isLUB_iSup : IsLUB (Set.range (fun i => e (N ⊓ F i))) (⨆ i, e (N ⊓ F i)))

/-- A subobject whose corresponding submodule is finitely generated has a source
finite-type domain. -/
theorem finiteType_of_fg {X : C} (e : Subobject X ≃o Submodule R V) (P : Subobject X)
    (hP : (e P).FG) : Langlands.Renard.IsFiniteTypeObject (P : C) := by
  let f : Subobject (P : C) ≃o Subobject (ModuleCat.of R (e P)) :=
    (((Subobject.subobjectOrderIso P).trans (iicOrderIso e P)).trans
      (e P).mapIic.symm).trans (ModuleCat.subobjectModule (ModuleCat.of R (e P))).symm
  have hfin : Module.Finite R (e P) := Module.Finite.iff_fg.mpr hP
  exact (Langlands.Renard.finiteTypeFiniteSubcover C (P : C)).2
    (NonUnitalModuleFiniteness.hasFiniteSubcoverProperty_of_orderIso f
      ((Langlands.Renard.finiteTypeFiniteSubcover _ _).1
        ((Langlands.Renard.ModuleFiniteType.finiteType_iff_finite
          (ModuleCat.of R (e P))).2 hfin)))

/-- An object whose subobjects form a submodule lattice is the sum of its source
finite-type subobjects: the cyclic submodules already cover it. -/
theorem locallyFiniteType_of_orderIso {X : C} (e : Subobject X ≃o Submodule R V) :
    Langlands.Renard.IsLocallyFiniteTypeObject X := by
  refine ⟨fun _ _ => le_top, fun Q hQ => ?_⟩
  apply e.le_iff_le.mp
  rw [e.map_top]
  intro x _
  have hx := e.monotone (hQ (finiteType_of_fg e (e.symm (Submodule.span R {x}))
    (by rw [e.apply_symm_apply]; exact Submodule.fg_span_singleton x)))
  rw [e.apply_symm_apply] at hx
  exact hx (Submodule.mem_span_singleton_self x)

end Transport

section NonUnital

/-- Categorical subobjects of an original additive action are the submodules of its
integer-unitized module. -/
def subobjectSubmoduleOrderIso {A : Type uA} [NonUnitalRing A]
    (M : NonUnitalModuleCat.{uA, uM} A) :
    Subobject M ≃o Submodule (Unitization ℤ A) (IntegerUnitization.extendObj A M) :=
  (NonUnitalModuleFiniteness.subobjectExtendOrderIso M).trans
    (ModuleCat.subobjectModule (IntegerUnitization.extendObj A M))

/-- Directed distributivity for all original additive actions. -/
theorem nonUnitalDirectedSubobjectDistributivity :
    NonUnitalDirectedSubobjectDistributivityStatement.{uA, uI, uM} := by
  intro A _ M I _ F hF N
  exact directedSums_of_orderIso (subobjectSubmoduleOrderIso M) F hF N

/-- Source AB5 for all original additive actions. -/
theorem nonUnitalSourceAB5 : NonUnitalSourceAB5Statement.{uA, uI, uM} := by
  intro A _
  refine ⟨fun J => ?_, nonUnitalDirectedSubobjectDistributivity.{uA, uI, max uI uM} A⟩
  exact Adjunction.hasColimitsOfShape_of_equivalence (IntegerUnitization.extendFunctor A)

/-- Source AB6 for all original additive actions. -/
theorem nonUnitalSourceAB6 : NonUnitalSourceAB6Statement.{uA, uM} := by
  intro A _ M
  exact locallyFiniteType_of_orderIso (subobjectSubmoduleOrderIso M)

end NonUnital

section Unital

/-- Directed distributivity for unital modules. -/
theorem unitalDirectedSubobjectDistributivity :
    UnitalDirectedSubobjectDistributivityStatement.{uA, uI, uM} := by
  intro A _ M I _ F hF N
  exact directedSums_of_orderIso (ModuleCat.subobjectModule M) F hF N

/-- Source AB5 for unital modules. -/
theorem unitalSourceAB5 : UnitalSourceAB5Statement.{uA, uI, uM} := by
  intro A _
  exact ⟨fun _ => inferInstance, unitalDirectedSubobjectDistributivity.{uA, uI, max uI uM} A⟩

/-- Source AB6 for unital modules. -/
theorem unitalSourceAB6 : UnitalSourceAB6Statement.{uA, uM} := by
  intro A _ M
  exact locallyFiniteType_of_orderIso (ModuleCat.subobjectModule M)

end Unital

/-- The six full-category targets. -/
theorem fullModuleAxioms : FullModuleAxiomsStatement.{uA, uI, uM} :=
  ⟨nonUnitalDirectedSubobjectDistributivity, nonUnitalSourceAB5, nonUnitalSourceAB6,
    unitalDirectedSubobjectDistributivity, unitalSourceAB5, unitalSourceAB6⟩

example : FullModuleAxiomsStatement.{uA, uI, uM} := fullModuleAxioms.{uA, uI, uM}
example : FullModuleAxiomsStatement.{0, 1, 0} := fullModuleAxioms.{0, 1, 0}
example : FullModuleAxiomsStatement.{1, 0, 2} := fullModuleAxioms.{1, 0, 2}
example : FullModuleAxiomsStatement.{2, 1, 0} := fullModuleAxioms.{2, 1, 0}

end Langlands.Algebra.RenardFullModuleAxiomProof
