/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtaleSectionColimitEventualZero
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence

/-! # Equality in filtered colimits on a fixed small etale site

Source: Stacks Project, Sites Tag 0738, proof of part (2).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private noncomputable def intModules : AddCommGrpCat.{u + 1} ⥤ ModuleCat.{u + 1} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap

private theorem intModules_comp_forget :
    intModules ⋙ forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1} = 𝟭 _ := rfl

/-- Equality in a filtered colimit of abelian sheaves on a fixed scheme is detected
at a later index on any quasi-compact etale object.
Source: Stacks Project, Sites Tag 0738 (lemma-directed-colimits-sections), part (2).
(blueprint: lem-weil-pbc-etale-abelian-section-colimit-eventual-equality).

Proof: Give every abelian group its canonical integer-module structure, and transport
sheaves and their colimit along the equivalence with integer modules. Subtract the
second section from the first. The colimit image of this difference is zero. The
module-sheaf eventual-zero theorem provides a later arrow killing the difference.
Forgetting the integer action and using subtraction gives the desired equality.
The empty etale object has its unique section; zero groups and singleton diagrams
are included. This statement involves one fixed scheme and no inverse system. -/
theorem etale_abelian_section_colimit_eventual_equality
    (X : Scheme.{u}) (U : X.Etale) [CompactSpace U.left]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (G : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (L : Cocone G) (hL : IsColimit L)
    (i : I) (s t : (G.obj i).obj.obj (op U))
    (hst : (L.ι.app i).hom.app (op U) s = (L.ι.app i).hom.app (op U) t) :
    ∃ (j : I) (a : i ⟶ j),
      (G.map a).hom.app (op U) s = (G.map a).hom.app (op U) t := by
  have : (intModules.{u} ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsEquivalence := by
    rw [intModules_comp_forget]
    infer_instance
  have : intModules.{u}.IsEquivalence :=
    Functor.isEquivalence_of_comp_right intModules.{u}
      (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})
  let J := X.smallEtaleTopology
  let Q := sheafCompose J intModules.{u}
  let V := sheafCompose J (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})
  have hQV : Q ⋙ V = 𝟭 _ := rfl
  have : (Q ⋙ V).EssSurj := by rw [hQV]; infer_instance
  have : Q.EssSurj := Functor.essSurj_of_comp_fully_faithful Q V
  have : Q.IsEquivalence := { }
  let pres : PreservesColimitsOfSize.{u, u} Q :=
    CategoryTheory.Adjunction.isEquivalence_preservesColimits Q
  have : PreservesColimit G Q :=
    (pres.preservesColimitsOfShape (J := I)).preservesColimit
  let K := AsSmall.{u + 1} I
  let d : K ⥤ I := (AsSmall.equiv : I ≌ K).inverse
  let H := d ⋙ G ⋙ Q
  let C := (Q.mapCocone L).whisker d
  have hC : IsColimit C :=
    (Functor.Final.isColimitWhiskerEquiv d _).symm (isColimitOfPreserves Q hL)
  have h := etale_section_colimit_eventual_zero X ℤ U K H C hC
    (AsSmall.up.obj i) (s - t) (by
      change (L.ι.app i).hom.app (op U) (s - t) = 0
      rw [map_sub, hst, sub_self])
  obtain ⟨j, a, ha⟩ := h
  refine ⟨d.obj j, d.map a, ?_⟩
  change (G.map (d.map a)).hom.app (op U) (s - t) = 0 at ha
  rwa [map_sub, sub_eq_zero] at ha

end AlgebraicGeometry.Etale
