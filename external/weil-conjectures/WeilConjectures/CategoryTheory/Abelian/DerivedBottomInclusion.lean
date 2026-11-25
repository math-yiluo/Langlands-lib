/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus

/-! # The canonical inclusion of bottom homology

Source: Stacks Project, Tag 05TC (2).
(blueprint: new-lem-pc-derived-bottom-inclusion).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace DerivedCategory.Plus
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The canonical inclusion `H^n(M)[-n] ⟶ M` for an object with no homology below n.
It is the inverse double-truncation identification, inverse lower projection,
and upper inclusion. Source: Stacks Project, Tag 05TC (2).
(blueprint: new-lem-pc-derived-bottom-inclusion). -/
noncomputable def bottomHomologyInclusion (n : ℤ) (M : Plus C) [M.IsGE n] :
    (singleFunctor C n).obj ((homologyFunctor C n).obj M) ⟶ M := by
  let t := TStructure.t (C := C)
  have : IsIso ((t.truncGEπ n).app ((t.truncLT (n + 1)).obj M)) := inferInstance
  exact ((eTruncLTCompETruncGEIso n).app M).inv ≫
    inv ((t.truncGEπ n).app ((t.truncLT (n + 1)).obj M)) ≫
    (t.truncLTι (n + 1)).app M

/-- Every map from an object in degree n to an object concentrated in degrees ≥ n
factors through the canonical inclusion of bottom homology.
Source: Stacks Project, Tag 05TC (2).
(blueprint: new-lem-pc-derived-bottom-inclusion).

Proof: The upper truncation inclusion on the source single object is invertible.
Naturality factors f through the upper truncation of M. Since M is ≥ n, the
lower projection of its upper truncation is invertible. Thus this factor is a
map between objects concentrated in degree n. Apply the faithful homology
functor on these objects. The homology formula for the double-truncation
isomorphism identifies its image with the homology of f, conjugated by the
single/homology identification. Faithfulness gives equality of the factors;
compose with the inverse lower projection and upper inclusion. -/
theorem single_map_bottomHomologyInclusion (n : ℤ) (M : Plus C) [M.IsGE n]
    (Y : C) (f : (singleFunctor C n).obj Y ⟶ M) :
    f = (singleFunctor C n).map
        ((singleFunctorCompHomologyFunctorIso n).inv.app Y ≫
          (homologyFunctor C n).map f) ≫ bottomHomologyInclusion n M  := by
  let t := TStructure.t (C := C)
  let H := homologyFunctor C n
  let W := (singleFunctor C n).obj Y
  let U := (t.truncLT (n + 1)).obj M
  let B := (t.truncGE n).obj U
  let a := (t.truncLTι (n + 1)).app W
  let b := (t.truncGEπ n).app U
  let e := (eTruncLTCompETruncGEIso n).app M
  have : IsIso a := (t.isLE_iff_isIso_truncLTι_app n (n + 1) rfl W).mp
    (by change (TStructure.t).IsLE ((singleFunctor C n).obj Y) n; infer_instance)
  have : IsIso b := inferInstance
  let f' : W ⟶ B := inv a ≫ (t.truncLT (n + 1)).map f ≫ b
  have hf : f' ≫ e.hom = (singleFunctor C n).map
      ((singleFunctorCompHomologyFunctorIso n).inv.app Y ≫ H.map f) := by
    apply singleFunctor_hom_ext_of_isGE_of_isLE n
    rw [← cancel_mono ((singleFunctorCompHomologyFunctorIso n).hom.app (H.obj M))]
    dsimp only [f', e, H]
    simp only [Functor.map_comp, Category.assoc]
    erw [homologyFunctor_map_eTruncLTCompETruncGEIso_hom_app n M]
    change H.map (inv a) ≫ H.map ((t.truncLT (n + 1)).map f) ≫
      H.map b ≫ inv (H.map b) ≫ H.map ((t.truncLTι (n + 1)).app M) = _
    rw [IsIso.hom_inv_id_assoc]
    rw [← H.map_comp]
    have hnat := (t.truncLTι (n + 1)).naturality f
    change _ = _ at hnat
    rw [hnat, ← H.map_comp]
    change H.map (inv a ≫ a ≫ f) = _
    rw [IsIso.inv_hom_id_assoc]
    simpa only [Functor.comp_map, Functor.map_comp, Functor.id_map, Functor.id_obj, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.hom_inv_id_app_assoc] using
      ((singleFunctorCompHomologyFunctorIso n).hom.naturality
        ((singleFunctorCompHomologyFunctorIso n).inv.app Y ≫ H.map f)).symm
  rw [← hf]
  change f = (f' ≫ e.hom) ≫
    (e.inv ≫ inv b ≫ (t.truncLTι (n + 1)).app M)
  simp only [f', Category.assoc, Iso.hom_inv_id_assoc, IsIso.hom_inv_id_assoc]
  have hn : (t.truncLT (n + 1)).map f ≫ (t.truncLTι (n + 1)).app M = a ≫ f :=
    (t.truncLTι (n + 1)).naturality f
  rw [hn, IsIso.inv_hom_id_assoc]

end DerivedCategory.Plus
