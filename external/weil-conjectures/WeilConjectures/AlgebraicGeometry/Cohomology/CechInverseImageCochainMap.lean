/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.Topology.Sheaves.CechCohomology

/-! # Ordered Čech cochains under inverse image

Source: Stacks Project, Tag 01FD, the maps of Čech complexes in Lemma 20.15.1.
(blueprint: def-pc-cech-inverse-image-cochain-map)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- The ordered Čech chain map associated to a coefficient map to a direct image.
Source: Stacks Project, Tag 01FD, Lemma 20.15.1, map of Čech complexes.
The component on a tuple is the coefficient map followed by restriction to the
smaller tuple intersection. Naturality of the coefficient map and functoriality of
restriction identify the two orders of applying each face, hence the differentials.
(blueprint: def-pc-cech-inverse-image-cochain-map) -/
noncomputable def cechInverseImageCochainMap
    {X Y : Scheme.{u}} {ι : Type u} (g : Y ⟶ X)
    (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (G : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (α : F.obj ⟶ (Opens.map g.base).op ⋙ G.obj) :
    (TopCat.Sheaf.cechComplexFunctor U).obj F ⟶
      (TopCat.Sheaf.cechComplexFunctor V).obj G :=
  CochainComplex.ofHom
    (fun k ↦ AddCommGrpCat.ofHom
      { toFun := fun x y ↦ G.obj.map (homOfLE (hinter k y)).op (α.app _ (x y))
        map_zero' := by funext y; simp
        map_add' := by intros; funext y; simp }) (by
      intro k
      ext x
      funext y
      change ((TopCat.Sheaf.cechComplexFunctor V).obj G).d k (k + 1)
          (fun y ↦ G.obj.map (homOfLE (hinter k y)).op (α.app _ (x y))) y =
        G.obj.map (homOfLE (hinter (k + 1) y)).op
          (α.app _ (((TopCat.Sheaf.cechComplexFunctor U).obj F).d k (k + 1) x y))
      dsimp only [TopCat.Sheaf.cechComplexFunctor, Functor.comp_obj, sheafToPresheaf]
      simp only [TopCat.Presheaf.cechComplex_d_apply]
      change (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        G.obj.map (homOfLE (TopCat.Presheaf.iInf_le_iInf_comp V y i.succAbove)).op
          (G.obj.map (homOfLE (hinter k (y ∘ i.succAbove))).op
            (α.app _ (x (y ∘ i.succAbove))))) =
        (G.obj.map (homOfLE (hinter (k + 1) y)).op).hom
          ((α.app _).hom (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
            F.obj.map (homOfLE (TopCat.Presheaf.iInf_le_iInf_comp U y i.succAbove)).op
              (x (y ∘ i.succAbove))))
      simp only [map_sum, map_zsmul]
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      change G.obj.map
          (homOfLE (TopCat.Presheaf.iInf_le_iInf_comp V y i.succAbove)).op
          (G.obj.map (homOfLE (hinter k (y ∘ i.succAbove))).op
            (α.app _ (x (y ∘ i.succAbove)))) =
        G.obj.map (homOfLE (hinter (k + 1) y)).op
          (α.app _ (F.obj.map
            (homOfLE (TopCat.Presheaf.iInf_le_iInf_comp U y i.succAbove)).op
              (x (y ∘ i.succAbove))))
      have hn := NatTrans.naturality_apply α
        (homOfLE (TopCat.Presheaf.iInf_le_iInf_comp U y i.succAbove)).op
        (x (y ∘ i.succAbove))
      change α.app _ (F.obj.map _ (x (y ∘ i.succAbove))) =
        G.obj.map _ (α.app _ (x (y ∘ i.succAbove))) at hn
      refine (TopCat.Presheaf.map_homOfLE_map_homOfLE_apply G.obj _ _ _).trans ?_
      refine Eq.trans ?_ (congrArg (G.obj.map (homOfLE (hinter (k + 1) y)).op) hn).symm
      exact (TopCat.Presheaf.map_homOfLE_map_homOfLE_apply G.obj _ _ _).symm)

end AlgebraicGeometry.Scheme.Modules
