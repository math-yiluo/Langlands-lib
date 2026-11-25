/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Final

/-! # Restricted ring sheafification units on abelian stalks

## References

* Stacks Project, Sheaves, Lemmas 007Z and 0087
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open Opposite TopologicalSpace
namespace AlgebraicGeometry

private theorem restrict_stalk_map_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] {P Q : Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u}} (α : P ⟶ Q)
    (x : X) [IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (f x)).map α)] :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (whiskerLeft f.opensFunctor.op α)) := by
  let L := f.isOpenEmbedding.functorNhds x
  have : L.op.Final := Functor.final_of_adjunction
    (f.isOpenEmbedding.adjunctionNhds x).op
  let p := colimit.pre ((OpenNhds.inclusion (f x)).op ⋙ P) L.op
  let q := colimit.pre ((OpenNhds.inclusion (f x)).op ⋙ Q) L.op
  have h : (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (whiskerLeft f.opensFunctor.op α) ≫ q =
      p ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat (f x)).map α := by
    apply colimit.hom_ext
    intro U
    simp only [TopCat.Presheaf.stalkFunctor, Functor.comp_map, colim_map,
      whiskeringLeft_obj_map,
      ι_colimMap_assoc, whiskerLeft_app]
    change α.app _ ≫ colimit.ι (L.op ⋙ (OpenNhds.inclusion (f x)).op ⋙ Q) U ≫ q =
      colimit.ι (L.op ⋙ (OpenNhds.inclusion (f x)).op ⋙ P) U ≫ p ≫
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat (f x)).map α
    simp [p, q, TopCat.Presheaf.stalkFunctor]
  have : IsIso p := inferInstance
  have : IsIso q := inferInstance
  have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (whiskerLeft f.opensFunctor.op α) ≫ q) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ q

/-- The ring sheafification unit remains bijective on underlying abelian stalks after
restriction to an open subscheme. -/
theorem ringSheafification_restricted_stalk_bijective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (P : Y.Opensᵒᵖ ⥤ CommRingCat.{u}) (x : X) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (whiskerLeft f.opensFunctor.op
        (whiskerRight (toSheafify (Opens.grothendieckTopology Y) P)
          (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{u})))) := by
  let G := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat.{u}
  let J := Opens.grothendieckTopology Y
  let α := whiskerRight (toSheafify J P) G
  have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (f x)).map α) := by
    rw [show α = toSheafify J (P ⋙ G) ≫ (sheafifyComposeIso J G P).hom from
      (sheafComposeIso_hom_fac J G P).symm]
    rw [Functor.map_comp]
    have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
      (f x) AddCommGrpCat (P ⋙ G)
    infer_instance
  have := restrict_stalk_map_isIso f α x
  exact ConcreteCategory.bijective_of_isIso _

end AlgebraicGeometry
