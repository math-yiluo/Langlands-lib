import Langlands.CategoryTheory.RenardModuleFiniteTypeStatements
import Langlands.CategoryTheory.Renard.FiniteTypeFiniteSubcover
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.Order.Bounds.OrderIso
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Renard's finite-type example in the actual unital module category: proof

Source: Renard (9 July 2026), Appendix A.I.3, printed pages 248–249.
The finite-subcover comparison is proved through Mathlib's order equivalence
between categorical subobjects and submodules; the finite-type comparison
composes it with the general categorical finite-type/finite-subcover theorem.
-/

set_option autoImplicit false

namespace Langlands.Renard.ModuleFiniteType

open CategoryTheory

universe uR uM

section Module

variable {R : Type uR} [Ring R] (M : ModuleCat.{uM} R)

/-- Every set of actual subobjects of a module has a least upper bound. -/
theorem hasSubobjectUnions : HasSubobjectUnions M := by
  intro S
  let e := ModuleCat.subobjectModule M
  exact ⟨e.symm (sSup (e '' S)), e.isLUB_image.mp (isLUB_sSup (e '' S))⟩

/-- The source finite-subcover property is ordinary finite generation. -/
theorem finiteSubcover_iff_finite :
    HasFiniteSubcoverProperty M ↔ Module.Finite R M := by
  classical
  let e := ModuleCat.subobjectModule M
  constructor
  · intro h
    rw [Module.finite_def, Submodule.fg_iff_compact,
      isCompactElement_iff_exists_le_sSup_of_le_sSup]
    intro S hS
    have htop : sSup S = (⊤ : Submodule R M) := top_le_iff.mp hS
    have hcover : IsLUB (e.symm '' S) ⊤ := by
      simpa using e.symm.isLUB_image'.mpr (htop ▸ isLUB_sSup S)
    obtain ⟨T, hT, hcoverT⟩ := h.2 (e.symm '' S) hcover
    refine ⟨T.image e, ?_, ?_⟩
    · rintro P hP
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨P, hP, hPQ⟩ := hT hQ
      simpa [← hPQ] using hP
    · have hcoverImage : IsLUB ((↑(T.image e) : Set (Submodule R M))) ⊤ := by
        simpa using e.isLUB_image'.mpr hcoverT
      simpa only [Finset.sup_id_eq_sSup] using
        (isLUB_iff_sSup_eq.mp hcoverImage).ge
  · intro h
    refine ⟨hasSubobjectUnions M, ?_⟩
    intro S hS
    have hc : IsCompactElement (⊤ : Submodule R M) :=
      (Submodule.fg_iff_compact _).mp (Module.finite_def.mp h)
    have hcover : IsLUB (e '' S) ⊤ := by
      simpa using e.isLUB_image'.mpr hS
    obtain ⟨T, hT, htop⟩ :=
      (isCompactElement_iff_exists_le_sSup_of_le_sSup _).mp hc
        (e '' S) (isLUB_iff_sSup_eq.mp hcover).ge
    refine ⟨T.image e.symm, ?_, ?_⟩
    · rintro P hP
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨P, hP, hPQ⟩ := hT hQ
      simpa [← hPQ] using hP
    · have hcoverT : IsLUB (↑T : Set (Submodule R M)) ⊤ := by
        apply isLUB_iff_sSup_eq.mpr
        simpa only [Finset.sup_id_eq_sSup] using top_le_iff.mp htop
      simpa using e.symm.isLUB_image'.mpr hcoverT

/-- Source finite type is ordinary finite generation, via the general
categorical finite-type/finite-subcover theorem in `ModuleCat R`. -/
theorem finiteType_iff_finite :
    IsFiniteTypeObject M ↔ Module.Finite R M :=
  (finiteTypeFiniteSubcover (ModuleCat.{uM} R) M).trans
    (finiteSubcover_iff_finite M)

end Module

/-- The closed finite-type comparison of Renard's A.I.3 example. -/
theorem finiteType : FiniteTypeStatement.{uR, uM} := by
  intro R _ M
  exact finiteType_iff_finite M

/-- The closed finite-subcover comparison. -/
theorem finiteSubcover : FiniteSubcoverStatement.{uR, uM} := by
  intro R _ M
  exact finiteSubcover_iff_finite M

/-- Renard A.I.3 example: the finite-type and finite-subcover comparisons
for actual unital modules, in order. -/
theorem moduleFiniteType : ModuleFiniteTypeStatement.{uR, uM} :=
  ⟨finiteType, finiteSubcover⟩

end Langlands.Renard.ModuleFiniteType
