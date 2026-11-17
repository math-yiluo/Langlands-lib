import Langlands.Sheaf.Equivariant.LocalActionConstant
import Langlands.Cohomology.SiteCech.FreeSections

/-! # Free module sheaves on discrete presheaves -/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory Opposite

universe u v z w

variable {T : Type u} [Category.{v} T] {G : Type z} [Group G] [TopologicalSpace G]
variable {R : Type w} [CommRing R]

/-- A discrete generator stays discrete in the free module presheaf. -/
theorem IsDiscreteSection.freeMk {F : Tᵒᵖ ⥤ Type w} {U : T} {H : OpenSubgroup G}
    {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ} {s : F.obj (op U)}
    (hs : IsDiscreteSection F a s) :
    IsDiscreteSection (F ⋙ ModuleCat.free R) a (ModuleCat.freeMk s) := by
  obtain ⟨N, hNH, hN⟩ := hs
  refine ⟨N, hNH, fun h hh => ?_⟩
  change (ModuleCat.free R).map (F.map (a h).unop.op) (ModuleCat.freeMk s) =
    ModuleCat.freeMk s
  rw [ModuleCat.free_map_apply, hN h hh]

namespace LocalActionSystem

variable (S : LocalActionSystem T G)

/-- Finite support makes the free module presheaf on a discrete presheaf
discrete. -/
theorem IsDiscrete.free {F : Tᵒᵖ ⥤ Type w} (hF : S.IsDiscrete F) :
    S.IsDiscrete (F ⋙ ModuleCat.free R) := by
  intro U H a ha s
  induction s using Finsupp.induction_linear with
  | zero => exact isDiscreteSection_zero _ a
  | add s t hs ht => exact hs.add ht
  | single x r =>
      have hx := (hF U H a ha x).freeMk (R := R)
      have hxr := hx.smul r
      change IsDiscreteSection (F ⋙ ModuleCat.free R) a
        (r • Finsupp.single x (1 : R)) at hxr
      rw [Finsupp.smul_single_one] at hxr
      exact hxr

variable (J : GrothendieckTopology T) (R)
variable [HasSheafify J (ModuleCat.{w} R)] [S.HasFiniteEquivariantRefinements J]

/-- Under finite equivariant refinements, the free module sheaf on a discrete
type-valued presheaf is discrete. -/
theorem IsDiscrete.freeSheaf {F : Tᵒᵖ ⥤ Type w} (hF : S.IsDiscrete F) :
    S.IsDiscrete ((Langlands.Cohomology.SiteCech.freeSheafFunctor J R).obj F).obj :=
  isDiscrete_sheafify (hF.free S)

end LocalActionSystem

end Langlands.Sheaf.Equivariant
