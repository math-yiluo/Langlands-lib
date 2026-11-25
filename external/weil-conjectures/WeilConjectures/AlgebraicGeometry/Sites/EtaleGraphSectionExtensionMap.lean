/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Sections over graphs extend by zero

The sum presheaf is the left Kan extension used by `Etale.etaleLowerShriek` before
sheafification. Its Kan-extension unit is the inclusion of the graph-indexed summand.

## References

* Stacks Project, Tag 0F4L, first paragraph of the proof, and Tag 01KT
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Graph geometry, clause 1 of Stacks 0F4L's presheaf construction.
-/
theorem etale_graph_clopen
    {X U : Scheme.{u}} (π : U ⟶ X) [IsFinite π] [Etale π]
    (V : X.Etale) (φ : V.left ⟶ U) (h : V.hom = φ ≫ π) :
    let Γ := pullback.lift (𝟙 V.left) φ (by simp [h])
    Etale φ ∧ IsOpenImmersion Γ ∧ IsClosedImmersion Γ ∧
      ∃ O : (pullback V.hom π).Opens,
        (O : Set (pullback V.hom π : Scheme.{u})) = Set.range Γ ∧
          ∃ γ : V.left ≅ O.toScheme, γ.hom ≫ O.ι = Γ := by
  sorry

/-- Extension of graph sections, clauses 2 and 3 of Stacks 0F4L's presheaf construction.
-/
theorem etale_graph_section_extension_map
    {X U : Scheme.{u}} (π : U ⟶ X) [IsFinite π] [Etale π]
    (Λ : Type (u + 1)) [CommRing Λ] :
    let L := MorphismProperty.Over.map (P := @Etale) ⊤ (inferInstance : Etale π)
    let B := MorphismProperty.Over.pullback @Etale ⊤ π
    let P := sheafToPresheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙ L.op.lan
    let D := Etale.lowerStar (ModuleCat.{u + 1} Λ) π ⋙
      sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    ∃ c : P ⟶ D,
      ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (W : U.Etale),
        let γ : W ⟶ B.obj (L.obj W) :=
          (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ π inferInstance trivial).unit.app W
        let e : M.obj.obj (op W) ⟶ M.obj.obj (op (B.obj (L.obj W))) :=
          (L.op.lanUnit.app M.obj).app (op W) ≫ (c.app M).app (op (L.obj W))
        ∀ (s : M.obj.obj (op W)) (t : M.obj.obj (op (B.obj (L.obj W)))),
          (M.obj.map γ.op t = s ∧
            ∀ (T : U.Etale) (j : T ⟶ B.obj (L.obj W)),
              IsOpenImmersion j.left →
              Set.range j.left = (Set.range γ.left)ᶜ → M.obj.map j.op t = 0) ↔
          t = e s := by
  sorry

/-- The inverse image of a graph is the graph of the restricted morphism, the key
compatibility in Stacks 0F4L's presheaf construction.
-/
theorem etale_graph_preimage
    {X U : Scheme.{u}} (π : U ⟶ X) [IsFinite π] [Etale π]
    (V V' : X.Etale) (a : V' ⟶ V) (φ : V.left ⟶ U) (h : V.hom = φ ≫ π) :
    let Γ := pullback.lift (𝟙 V.left) φ (by simp [h])
    let Γ' := pullback.lift (𝟙 V'.left) (a.left ≫ φ)
      (by simp only [Category.id_comp, Category.assoc, ← h, MorphismProperty.Over.w])
    let aU := (MorphismProperty.Over.pullback @Etale ⊤ π).map a
    aU.left ⁻¹' Set.range Γ = Set.range Γ' := by
  sorry

end AlgebraicGeometry
