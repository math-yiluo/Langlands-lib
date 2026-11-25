/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.ZariskiUnitsRestriction
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Abelian

/-! # Local lifting of Zariski units along closed immersions

Source: Stacks Project, Varieties, Lemma 09NY, opening short exact sequence
(blueprint: lem-sc-closed-immersion-zariski-units-epi).
-/

@[expose] public section

universe u
open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme

/-- Restriction of units along a closed immersion is an epimorphism of abelian sheaves.
Source: Stacks Project, Varieties, Lemma 09NY, opening short exact sequence
(blueprint: lem-sc-closed-immersion-zariski-units-epi).

Proof: At a point of Z, the map of local rings is surjective and local. Lift the germ
of a unit; locality implies that its lift is a unit. Represent the lift on a neighbourhood
in X, and shrink to its basic open to make the representative invertible. Equality of
germs gives equality with the prescribed unit on a neighbourhood in Z. For a closed
embedding, this neighbourhood contains the inverse image of a neighbourhood in X:
remove the closed image of its complement. Outside Z, remove its closed image; the
inverse-image open is empty and its units group is trivial. These local lifts prove
epimorphy by the locally-surjective criterion. -/
theorem epi_unitsSheafToPushforward_of_isClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Epi (unitsSheafToPushforward i) := by
  classical
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).1
  apply (TopCat.Presheaf.isLocallySurjective_iff _).2
  intro U t x hx
  by_cases hxim : x ∈ Set.range i
  · obtain ⟨z, rfl⟩ := hxim
    let v := unitsSheaf.toUnits t
    obtain ⟨a, ha⟩ := i.stalkMap_surjective z
      (Z.presheaf.germ (i ⁻¹ᵁ U) z hx v.val)
    have hau : IsUnit a := (isUnit_map_iff (i.stalkMap z).hom a).mp
      (ha ▸ v.isUnit.map (Z.presheaf.germ (i ⁻¹ᵁ U) z hx).hom)
    obtain ⟨A, hAU, hzA, s, hs⟩ := X.presheaf.exists_le_germ_eq a hx
    let B := X.basicOpen s
    have hzB : i z ∈ B := (X.mem_basicOpen s (i z) hzA).2 (hs ▸ hau)
    have hBA : B ≤ A := X.basicOpen_le s
    let b := X.presheaf.map (homOfLE hBA).op s
    have hbu : IsUnit b := X.toRingedSpace.isUnit_res_basicOpen s
    have hb : X.presheaf.germ B (i z) hzB b = a := by
      rw [X.presheaf.germ_res_apply]
      exact hs
    have hbg : Z.presheaf.germ (i ⁻¹ᵁ B) z hzB (i.app B b) =
        Z.presheaf.germ (i ⁻¹ᵁ U) z hx v.val := by
      rw [← i.germ_stalkMap_apply, hb, ha]
    obtain ⟨V, hzV, hVB, hVU, heq⟩ := Z.presheaf.germ_eq z hzB hx _ _ hbg
    let W : Opens X := ⟨B ∩ (i '' (V : Set Z)ᶜ)ᶜ,
      B.isOpen.inter (i.isClosedEmbedding.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩
    have hWB : W ≤ B := fun y hy ↦ hy.1
    have hWU : W ≤ U := hWB.trans (hBA.trans hAU)
    have hWV : i ⁻¹ᵁ W ≤ V := by
      intro y hy
      by_contra hyV
      exact hy.2 ⟨y, hyV, rfl⟩
    refine ⟨W, hWU, ⟨unitsSheaf.ofUnits
      (Units.map (X.presheaf.map (homOfLE hWB).op).hom hbu.unit), ?_⟩, ?_⟩
    · apply Additive.toMul.injective
      apply Units.ext
      change i.app W (X.presheaf.map (homOfLE hWB).op hbu.unit.val) =
        Z.presheaf.map (homOfLE ((Opens.map i.base).monotone hWU)).op v.val
      rw [hbu.unit_spec]
      have hn := ConcreteCategory.congr_hom (i.c.naturality (homOfLE hWB).op) b
      change i.app W (X.presheaf.map (homOfLE hWB).op b) = _
      change i.app W (X.presheaf.map (homOfLE hWB).op b) =
        Z.presheaf.map (homOfLE ((Opens.map i.base).monotone hWB)).op (i.app B b) at hn
      rw [hn]
      have he := congrArg (Z.presheaf.map (homOfLE hWV).op) heq
      calc
        _ = Z.presheaf.map (homOfLE hWV).op
            (Z.presheaf.map hVB.op (i.app B b)) := by
          exact ConcreteCategory.congr_hom
            (Z.presheaf.map_comp hVB.op (homOfLE hWV).op) (i.app B b)
        _ = Z.presheaf.map (homOfLE hWV).op (Z.presheaf.map hVU.op v.val) := he
        _ = _ := by
          exact (ConcreteCategory.congr_hom
            (Z.presheaf.map_comp hVU.op (homOfLE hWV).op) v.val).symm
    · exact ⟨hzB, fun ⟨y, hy, he⟩ ↦ hy (i.isClosedEmbedding.isEmbedding.injective he ▸ hzV)⟩
  · let W : Opens X := ⟨U ∩ (Set.range i)ᶜ,
      U.isOpen.inter i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have hWU : W ≤ U := fun y hy ↦ hy.1
    have he : i ⁻¹ᵁ W = ⊥ := by
      ext z
      change (i z ∈ U ∧ i z ∉ Set.range i) ↔ False
      exact ⟨fun hz ↦ hz.2 ⟨z, rfl⟩, False.elim⟩
    refine ⟨W, hWU, ⟨0, ?_⟩, hx, hxim⟩
    have ht := TopCat.Sheaf.isTerminalOfEqEmpty (X := (Z : TopCat)) Z.unitsSheaf he
    have hzero := ConcreteCategory.congr_hom (ht.hom_ext (𝟙 _) 0)
      (Z.unitsSheaf.obj.map (homOfLE ((Opens.map i.base).monotone hWU)).op t)
    change (unitsSheafToPushforward i).hom.app (op W) 0 = _
    rw [map_zero]
    exact hzero.symm

end AlgebraicGeometry.Scheme
