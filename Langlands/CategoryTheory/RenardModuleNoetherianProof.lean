import Langlands.CategoryTheory.RenardModuleNoetherianStatements
import Langlands.CategoryTheory.RenardModuleFiniteTypeProof
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.Algebra.Module.ULift
import Mathlib.Order.Bounds.OrderIso
import Mathlib.RingTheory.Noetherian.Basic

set_option autoImplicit false

namespace Langlands.Renard.ModuleNoetherian

universe uR uM

open CategoryTheory

theorem object_iff (R : Type uR) [Ring R] (M : ModuleCat.{uM} R) :
    Langlands.Renard.IsNoetherianObject M ↔ IsNoetherian R M := by
  classical
  let e := ModuleCat.subobjectModule M
  rw [← set_has_maximal_iff_noetherian (R := R) (M := M)]
  constructor
  · intro h S hS
    have hpre : (e ⁻¹' S).Nonempty := by
      obtain ⟨Q, hQ⟩ := hS
      exact ⟨e.symm Q, by simpa using hQ⟩
    obtain ⟨P, hP, hmax⟩ := h (e ⁻¹' S) hpre
    refine ⟨e P, hP, ?_⟩
    intro Q hQ hlt
    have hle : P ≤ e.symm Q := by
      simpa using e.symm.monotone hlt.le
    have heq : e.symm Q = P :=
      hmax (e.symm Q) (by simpa using hQ) hle
    have hQP : Q = e P := by simpa using congrArg e heq
    exact hlt.ne hQP.symm
  · intro h S hS
    obtain ⟨N, hN, hmax⟩ := h (e '' S) (hS.image e)
    obtain ⟨P, hP, rfl⟩ := hN
    refine ⟨P, hP, ?_⟩
    intro Q hQ hle
    exact (e.injective (eq_of_le_of_not_lt (e.monotone hle)
      (hmax (e Q) ⟨Q, hQ, rfl⟩))).symm

theorem objectStatement :
    Langlands.Renard.ModuleNoetherian.ObjectStatement.{uR, uM} := by
  intro R _ M
  exact object_iff R M

theorem category_of_finite_type
    (hFT : Langlands.Renard.ModuleFiniteType.FiniteTypeStatement.{uR, max uR uM}) :
    Langlands.Renard.ModuleNoetherian.CategoryStatement.{uR, uM} := by
  intro R _
  constructor
  · intro hcat
    let L : ModuleCat.{max uR uM} R := ModuleCat.of R (ULift.{uM} R)
    have hfin : Module.Finite R L := inferInstance
    have hsource : Langlands.Renard.IsFiniteTypeObject L := (hFT R L).mpr hfin
    have hnoeth : IsNoetherian R L := (object_iff R L).mp (hcat.2 L hsource)
    let : IsNoetherian R (ULift.{uM} R) := hnoeth
    exact isNoetherian_of_linearEquiv
      (ULift.moduleEquiv : ULift.{uM} R ≃ₗ[R] R)
  · intro hR
    let : IsNoetherianRing R := hR
    refine ⟨fun M => Langlands.Renard.ModuleFiniteType.hasSubobjectUnions M, ?_⟩
    intro M hM
    let : Module.Finite R M := (hFT R M).mp hM
    exact (object_iff R M).mpr inferInstance

theorem moduleNoetherian_of_finite_type
    (hFT : Langlands.Renard.ModuleFiniteType.FiniteTypeStatement.{uR, max uR uM}) :
    Langlands.Renard.ModuleNoetherian.ModuleNoetherianStatement.{uR, uM} :=
  ⟨objectStatement, category_of_finite_type hFT⟩

theorem categoryStatement :
    Langlands.Renard.ModuleNoetherian.CategoryStatement.{uR, uM} :=
  category_of_finite_type Langlands.Renard.ModuleFiniteType.finiteType.{uR, max uR uM}

theorem moduleNoetherian :
    Langlands.Renard.ModuleNoetherian.ModuleNoetherianStatement.{uR, uM} :=
  ⟨objectStatement, categoryStatement⟩

end Langlands.Renard.ModuleNoetherian
