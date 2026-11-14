import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Local saturation of a submodule presheaf -/

noncomputable section

universe u v

namespace Langlands.ModuleSheaf

open CategoryTheory TopologicalSpace

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{u} R}

/-- Local saturation inside an actual module sheaf. -/
def localSaturation (P : M.val.Submodule) : M.Submodule where
  toSubmodule := {
    obj U := {
      carrier := (P.toSubfunctor.sheafify J).obj U
      zero_mem' := P.toSubfunctor.le_sheafify J U (P.obj U).zero_mem
      add_mem' {s t} hs ht := by
        apply J.superset_covering _ (J.intersection_covering hs ht)
        intro V g hg
        change M.val.map g.op (s + t) ∈ P.obj (.op V)
        rw [map_add]
        exact (P.obj (.op V)).add_mem hg.1 hg.2
      smul_mem' a s hs := by
        apply J.superset_covering _ hs
        intro V g hg
        change M.val.map g.op (a • s) ∈ P.obj (.op V)
        rw [M.val.map_smul]
        exact (P.obj (.op V)).smul_mem _ hg }
    map g := (P.toSubfunctor.sheafify J).map g }
  isSheaf {U} s hs := by
    change (P.toSubfunctor.sheafify J).sieveOfSection s ∈ J U.unop at hs
    change P.toSubfunctor.sieveOfSection s ∈ J U.unop
    apply J.superset_covering _
      (J.bind_covering hs (fun V g hg => hg))
    rintro V g ⟨W, i, j, hj, hi, rfl⟩
    change M.val.map (i ≫ j).op s ∈ P.obj (.op V)
    rw [op_comp, M.val.map_comp_apply]
    exact hi

/-- Original submodule sections belong to its local saturation. -/
theorem le_localSaturation (P : M.val.Submodule) :
    P ≤ (localSaturation P).toSubmodule :=
  P.toSubfunctor.le_sheafify J

section Opens

variable {X : TopCat.{u}} {R : X.Sheaf RingCat.{u}} {M : SheafOfModules.{u} R}

/-- Local saturation on an open-set site is membership near each point. -/
theorem mem_localSaturation_iff (P : M.val.Submodule)
    (U : Opens X) (s : M.val.obj (.op U)) :
    s ∈ (localSaturation P).toSubmodule.obj (.op U) ↔
      ∀ x ∈ U, ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
        M.val.map (homOfLE hVU).op s ∈ P.obj (.op V) := by
  constructor
  · intro h x hx
    obtain ⟨V, g, hg, hxV⟩ := h x hx
    exact ⟨V, g.le, hxV, hg⟩
  · intro h x hx
    obtain ⟨V, hVU, hxV, hs⟩ := h x hx
    exact ⟨V, homOfLE hVU, hs, hxV⟩

end Opens

end Langlands.ModuleSheaf
