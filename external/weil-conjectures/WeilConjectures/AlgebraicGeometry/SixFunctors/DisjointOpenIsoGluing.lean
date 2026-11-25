/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
import WeilConjectures.Topology.GlueSheavesOfModules
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Gluing module isomorphisms on disjoint opens

## References

* Stacks Project, Sheaves, Tags 00AL, 00AM and 04TN
* Stacks Project, Sheaves, Tags 04TN and 00AM
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- On a disjoint open covering, arbitrary local isomorphisms glue. -/
theorem disjointOpen_nonempty_iso {X : Scheme.{u}} {ι : Type}
    (U : ι → X.Opens)
    (hcover : ∀ x : X, ∃ i : ι, x ∈ U i)
    (hdisjoint : ∀ (i j : ι) (x : X), x ∈ U i → x ∈ U j → i = j)
    (F G : X.Modules)
    (hlocal : ∀ i : ι,
      Nonempty ((tensorPullback (U i).ι).obj F ≅ (tensorPullback (U i).ι).obj G)) :
    Nonempty (F ≅ G) := by
  classical
  have hcov : ⨆ i, U i = ⊤ := by
    apply top_unique
    intro x hx
    obtain ⟨i, hi⟩ := hcover x
    exact (le_iSup U i) hi
  let e (i : ι) (M : X.Modules) :
      (overEquiv (U i)).functor.obj (M.over (U i)) ≅
        (tensorPullback (U i).ι).obj M :=
    (overFunctorEquiv (U i)).app M ≪≫ (restrictFunctorIsoPullback _).app M ≪≫
      ((tensorPullbackSectionAdjunction _).leftAdjointUniq
        (pullbackPushforwardAdjunction _)).symm.app M
  let E (i : ι) : F.over (U i) ≅ G.over (U i) :=
    (overEquiv (U i)).fullyFaithfulFunctor.preimageIso
      (e i F ≪≫ (hlocal i).some ≪≫ (e i G).symm)
  have empty_eq (M : X.Modules) (s t : Γ(M, ⊥)) : s = t := by
    let S : TopCat.Sheaf (Type u) X.toTopCat :=
      (sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u})).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    exact S.eq_of_locally_eq' (fun i : Empty ↦ ⊥) ⊥
      (fun i ↦ isEmptyElim i) bot_le s t (fun i ↦ isEmptyElim i)
  have compatible (M N : X.Modules)
      (φ : ∀ i : ι, M.over (U i) ⟶ N.over (U i)) :
      ∀ (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
        (φ i).val.app (op (Over.mk (homOfLE hi))) =
          (φ j).val.app (op (Over.mk (homOfLE hj))) := by
    intro i j W hi hj
    by_cases hij : i = j
    · subst j
      rfl
    · have hW : W = ⊥ := by
        apply le_antisymm _ bot_le
        intro x hx
        exact False.elim (hij (hdisjoint i j x (hi hx) (hj hx)))
      subst W
      ext s
      exact empty_eq N _ _
  have hg := glue_sheaves_of_modules.{u, 0, 0} X.toRingedSpace ι U hcov
  obtain ⟨a, ha, _⟩ := hg.1 F G (fun i ↦ (E i).hom)
    (compatible F G (fun i ↦ (E i).hom))
  obtain ⟨b, hb, _⟩ := hg.1 G F (fun i ↦ (E i).inv)
    (compatible G F (fun i ↦ (E i).inv))
  refine ⟨⟨a, b, ?_, ?_⟩⟩
  · apply hg.2.1 F F
    intro i
    change (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map (a ≫ b) =
      (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map (𝟙 F)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    change a.over (U i) ≫ b.over (U i) = 𝟙 _
    rw [ha i, hb i]
    exact (E i).hom_inv_id
  · apply hg.2.1 G G
    intro i
    change (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map (b ≫ a) =
      (SheafOfModules.overFunctor X.ringCatSheaf (U i)).map (𝟙 G)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    change b.over (U i) ≫ a.over (U i) = 𝟙 _
    rw [hb i, ha i]
    exact (E i).inv_hom_id

end AlgebraicGeometry.Scheme.Modules
