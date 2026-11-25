/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf

/-! # The normalized restriction equation for the structure module

Source: Stacks Project, Tags 0096, 01CA and 03DR, equation (35.8.1).
(blueprint: lem-sc-etale-tensor-unit-restriction-equation)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] tensorPullback tensorPullbackObj tensorPullbackObjUnitToUnit

private theorem tensorStructureMap_comp {A B D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) :
    (tensorSectionsComp a b).hom.app (SheafOfModules.unit D.ringCatSheaf) ≫
        tensorPullbackObjUnitToUnit (a ≫ b) =
      (tensorPullback a).map (tensorPullbackObjUnitToUnit b) ≫
        tensorPullbackObjUnitToUnit a := by
  let adjA := Classical.choose (exists_tensorPullbackAdjunction a)
  let adjB := Classical.choose (exists_tensorPullbackAdjunction b)
  let adjAB := Classical.choose (exists_tensorPullbackAdjunction (a ≫ b))
  apply ((adjB.comp adjA).homEquiv _ _).injective
  have hu := unit_conjugateEquiv_symm adjAB (adjB.comp adjA)
    (pushforwardComp a b).inv (SheafOfModules.unit D.ringCatSheaf)
  have ha := (tensorPullbackObjUnitToUnit_isIso a).2
  have hb := (tensorPullbackObjUnitToUnit_isIso b).2
  have hab := (tensorPullbackObjUnitToUnit_isIso (a ≫ b)).2
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  rw [Functor.map_comp, ← Category.assoc]
  change adjAB.unit.app _ ≫ (pushforwardComp a b).inv.app _ =
    (adjB.comp adjA).unit.app _ ≫ (pushforward a ⋙
      pushforward b).map ((tensorSectionsComp a b).hom.app _)
    at hu
  rw [← hu, Category.assoc]
  rw [← (pushforwardComp a b).inv.naturality]
  rw [← Category.assoc, hab]
  rw [Adjunction.comp_unit_app, Category.assoc]
  dsimp only [Functor.comp_map]
  have hn : adjA.unit.app _ ≫ (pushforward a).map
      ((tensorPullback a).map (tensorPullbackObjUnitToUnit b) ≫
        tensorPullbackObjUnitToUnit a) =
      tensorPullbackObjUnitToUnit b ≫
        SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom := by
    rw [Functor.map_comp, ← Category.assoc]
    erw [adjA.unit_naturality (tensorPullbackObjUnitToUnit b)]
    rw [Category.assoc, ha]
  rw [← Functor.map_comp, hn, Functor.map_comp, ← Category.assoc, hb]
  ext W x
  rfl

private theorem topRestriction_id {A B : Scheme.{u}} (a : A ⟶ B) (M : A.Modules) :
    M.presheaf.map (homOfLE a.preimage_top.ge).op = 𝟙 Γ(M, ⊤) := by
  have hi : homOfLE a.preimage_top.ge = 𝟙 (⊤ : TopologicalSpace.Opens A) := rfl
  erw [hi, op_id, M.presheaf.map_id]
  rfl

private theorem structureMapSectionsOfAdjunction {A B : Scheme.{u}} (a : A ⟶ B)
    (L : B.Modules ⥤ A.Modules) (adj : L ⊣ pushforward a)
    (ε : L.obj (SheafOfModules.unit B.ringCatSheaf) ⟶
      SheafOfModules.unit A.ringCatSheaf)
    (hε : adj.unit.app (SheafOfModules.unit B.ringCatSheaf) ≫
      (pushforward a).map ε = SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom)
    (G : B.Modules) (φ : G ⟶ SheafOfModules.unit B.ringCatSheaf) :
    (adj.unit.app G).app ⊤ ≫ (L.obj G).presheaf.map (homOfLE a.preimage_top.ge).op ≫
      (L.map φ).app ⊤ ≫ ε.app ⊤ =
      φ.app ⊤ ≫ AddCommGrpCat.ofHom a.appTop.hom.toAddMonoidHom := by
  have hn := congrArg (fun ψ ↦ ψ.app ⊤) (adj.unit_naturality φ)
  change (adj.unit.app G).app ⊤ ≫ (L.map φ).app ⊤ =
    φ.app ⊤ ≫ (adj.unit.app (SheafOfModules.unit B.ringCatSheaf)).app ⊤ at hn
  have he := congrArg (fun ψ ↦ ψ.app ⊤) hε
  change (adj.unit.app (SheafOfModules.unit B.ringCatSheaf)).app ⊤ ≫ ε.app ⊤ =
    AddCommGrpCat.ofHom a.appTop.hom.toAddMonoidHom at he
  erw [topRestriction_id, Category.id_comp, ← Category.assoc, hn, Category.assoc, he]

private theorem tensorStructureMap_sections {A B : Scheme.{u}} (a : A ⟶ B)
    (G : B.Modules) (φ : G ⟶ SheafOfModules.unit B.ringCatSheaf) :
    tensorSectionsUnit a G ≫
        ((tensorPullback a).map φ).app ⊤ ≫
          (tensorPullbackObjUnitToUnit a).app ⊤ =
      φ.app ⊤ ≫ AddCommGrpCat.ofHom a.appTop.hom.toAddMonoidHom := by
  exact structureMapSectionsOfAdjunction a (tensorPullback a)
    (Classical.choose (exists_tensorPullbackAdjunction a)) (tensorPullbackObjUnitToUnit a)
    (tensorPullbackObjUnitToUnit_isIso a).2 G φ

private theorem tensorStructureMap_restriction {A B D : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ D) (h : a ≫ b = c) :
    (tensorSectionsUnit a
          ((tensorPullback b).obj (SheafOfModules.unit D.ringCatSheaf)) ≫
        ((tensorSectionsComp a b).hom.app
          (SheafOfModules.unit D.ringCatSheaf)).app ⊤ ≫
        (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj
          (SheafOfModules.unit D.ringCatSheaf)) h)).app ⊤) ≫
        (tensorPullbackObjUnitToUnit c).app ⊤ =
      (tensorPullbackObjUnitToUnit b).app ⊤ ≫
        AddCommGrpCat.ofHom a.appTop.hom.toAddMonoidHom := by
  subst c
  simp only [eqToHom_refl, Hom.id_app, Category.comp_id]
  rw [Category.assoc, ← Hom.comp_app, tensorStructureMap_comp,
    Hom.comp_app]
  exact tensorStructureMap_sections a _ (tensorPullbackObjUnitToUnit b)


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The normalized restriction followed by the adjoint structure-module map is the
structure-sheaf restriction followed after the source structure-module map.
Source: Stacks Project, Tags 0096, 01CA and 03DR, equation (35.8.1).
(blueprint: lem-sc-etale-tensor-unit-restriction-equation)

Proof: Write epsilon_f for tensorPullbackObjUnitToUnit f. Apply the composite
adjunction Hom equivalence to the two maps from g^*u^*O_X to O_V. The unit equation
of tensorSectionsComp and naturality of the adjunction unit identify the image of
c_{g,u} followed by epsilon_{g >> u} with the image of g^*(epsilon_u) followed by
epsilon_g. Both images are the composite structure-sheaf map, by the defining
equations eta_f followed by f_*(epsilon_f) = f-sharp. Injectivity of the Hom
bijection proves equality. Transport along g >> u = v by equality elimination.
Evaluate on the top open. Unit naturality moves epsilon_u through section pullback;
the adjunction-unit equation for epsilon_g makes the resulting map g-sharp.
The restriction from the inverse image of top to top is the identity. These
identities give the stated equality of additive homomorphisms, including on the
empty scheme and for identity or composite site arrows. -/
theorem etaleTensorUnitRestriction_equation {X : Scheme.{u}} {U V : X.Etale}
    (g : V ⟶ U) (x : Γ((tensorPullback U.hom).obj
      (SheafOfModules.unit X.ringCatSheaf), ⊤)) :
    (tensorPullbackObjUnitToUnit V.hom).app ⊤
        (etaleTensorSectionsRestriction (SheafOfModules.unit X.ringCatSheaf) g x) =
      g.left.appTop ((tensorPullbackObjUnitToUnit U.hom).app ⊤ x) := by
  have h : etaleTensorSectionsRestriction (SheafOfModules.unit X.ringCatSheaf) g ≫
      (tensorPullbackObjUnitToUnit V.hom).app ⊤ =
      (tensorPullbackObjUnitToUnit U.hom).app ⊤ ≫
        AddCommGrpCat.ofHom g.left.appTop.hom.toAddMonoidHom :=
    tensorStructureMap_restriction (D := X) g.left U.hom V.hom g.w
  exact ConcreteCategory.congr_hom h x

end AlgebraicGeometry.Scheme.Modules
