/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.Monoidal.Rigid.Trace

/-!
# Braided monoidal functors preserve categorical traces

Let `F : C ⥤ D` be a braided (strong) monoidal functor between braided monoidal categories.
The endomorphisms of the units are rings, and `F` induces the map
`ρ_F : End (𝟙_ C) → End (𝟙_ D)`, `t ↦ ε ≫ F t ≫ η` (`CategoryTheory.Functor.unitEndRingHom`),
a ring homomorphism when `C` and `D` are preadditive and `F` is additive. The categorical trace
is compatible with `F`: `tr (F f) = ρ_F (tr f)` (`CategoryTheory.Functor.trace_map`), and so
`tr (f') = ρ_F (tr f)` for every endomorphism `f'` of an object `X'` intertwined with `F f` by
an isomorphism `F X ≅ X'` (`CategoryTheory.Functor.trace_eq_unitEndRingHom_trace`).

For the derived extension of scalars `- ⊗ᴸ_A B` along a homomorphism of coefficient rings
`ρ : A → B` this is the scalar-extension law `ρ (tr_A (v ∣ P)) = tr_B (v ⊗ᴸ B ∣ P ⊗ᴸ B)` of the
categorical trace (blueprint `proposition-properties-trace`, item (3)), used for blueprint
`theorem-grothendieck-lefschetz-trace-formula--7`.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Category Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D] (F : C ⥤ D) [F.Braided]

namespace Functor

/-- A braided monoidal functor preserves categorical traces: `tr(F f) = ε ≫ F(tr f) ≫ η`. -/
theorem trace_map {X : C} [HasRightDual X] [HasRightDual (F.obj X)] (f : X ⟶ X) :
    trace (F.map f) = ε F ≫ F.map (trace f) ≫ η F :=
  MonoidalCategory.trace_map F (by rw [map_braiding, Monoidal.μ_δ_assoc]) f

/-- The map `End (𝟙_ C) → End (𝟙_ D)`, `t ↦ ε ≫ F t ≫ η`, induced by a monoidal functor on the
endomorphism rings of the units: for the derived extension of scalars along a homomorphism of
coefficient rings `ρ : A → B`, this is `ρ` itself. -/
noncomputable def unitEndRingHom [Preadditive C] [Preadditive D] [F.Additive] :
    End (𝟙_ C) →+* End (𝟙_ D) where
  toFun t := .of (ε F ≫ F.map t.asHom ≫ η F)
  map_one' := by
    apply End.ext
    rw [End.one_asHom, End.one_asHom, F.map_id, id_comp, Monoidal.ε_η]
  map_mul' s t := by
    apply End.ext
    rw [End.mul_asHom, End.mul_asHom, F.map_comp, assoc, assoc, assoc, Monoidal.η_ε_assoc]
  map_zero' := by
    apply End.ext
    change ε F ≫ F.map 0 ≫ η F = 0
    rw [F.map_zero, Limits.zero_comp, Limits.comp_zero]
  map_add' s t := by
    apply End.ext
    change ε F ≫ F.map (s.asHom + t.asHom) ≫ η F =
      (ε F ≫ F.map s.asHom ≫ η F) + (ε F ≫ F.map t.asHom ≫ η F)
    rw [F.map_add, Preadditive.add_comp, Preadditive.comp_add]

lemma unitEndRingHom_apply [Preadditive C] [Preadditive D] [F.Additive] (t : End (𝟙_ C)) :
    F.unitEndRingHom t = .of (ε F ≫ F.map t.asHom ≫ η F) :=
  rfl

/-- **Scalar-extension law of the trace** (blueprint `proposition-properties-trace`, item (3)):
if an isomorphism `e : F X ≅ X'` intertwines `F f` with an endomorphism `f'` of `X'`, then
`tr (f') = ρ_F (tr f)`. -/
theorem trace_eq_unitEndRingHom_trace [Preadditive C] [Preadditive D] [F.Additive] {X : C}
    {X' : D} [HasRightDual X] [HasRightDual (F.obj X)] [HasRightDual X'] (f : X ⟶ X)
    (f' : X' ⟶ X') (e : F.obj X ≅ X') (h : F.map f ≫ e.hom = e.hom ≫ f') :
    trace f' = (F.unitEndRingHom (.of (trace f))).asHom := by
  rw [unitEndRingHom_apply]
  change trace f' = ε F ≫ F.map (trace f) ≫ η F
  rw [← trace_map, trace_eq_of_iso e _ _ h]

end Functor

end CategoryTheory
