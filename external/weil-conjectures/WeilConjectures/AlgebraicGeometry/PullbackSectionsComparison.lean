/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleObjectSections
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-! # Sections on an étale object as global sections on its base change

Source: Stacks Project, Tags 03S2, 03CF and 03EF; naturality of restriction and pullback units.
(blueprint: lem-weil-pbc-pullback-sections-comparison)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Evaluation at an étale object, followed by restriction to its base change and the
inverse-image composition isomorphism. Source: Stacks Tags 03S2 and 00XZ.
(blueprint: lem-weil-pbc-pullback-sections-comparison) -/
noncomputable def pullbackSectionsEquiv {R X : Scheme.{u}}
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : R.Etale) (f : X ⟶ R) :
    ((lowerStar AddCommGrpCat.{u + 1} f).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj G)).obj.obj (op W) ≃+
      (Sheaf.Γ (pullback W.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((upperStar AddCommGrpCat.{u + 1} (pullback.fst W.hom f ≫ W.hom)).obj G) := by
  let A := AddCommGrpCat.{u + 1}
  let V : X.Etale := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W
  let p : V.left ⟶ X := V.hom
  let F := (upperStar A f).obj G
  let w : V.left.Etale := Scheme.Etale.mk (𝟙 V.left)
  let eW : (MorphismProperty.Over.map ⊤ (inferInstance : Etale p)).obj w ≅ V :=
    MorphismProperty.Over.isoMk (Iso.refl V.left) (by simp [w, p])
  let e₁ : F.obj.obj (op V) ≅
      ((localizationRestriction A p inferInstance).obj F).obj.obj (op w) :=
    F.obj.mapIso eW.op
  let e₂ := ((upperStarIsoLocalizationRestriction A p inferInstance).app F).symm
  let e₃ := ((Sheaf.ΓNatIsoSheafSections V.left.smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal (P := @Etale) V.left)).app
      ((upperStar A p).obj F)).symm
  exact Iso.addCommGroupIsoToAddEquiv
    (e₁ ≪≫ ((sheafSections V.left.smallEtaleTopology A).obj (op w)).mapIso e₂ ≪≫
      e₃ ≪≫ (Sheaf.Γ V.left.smallEtaleTopology A).mapIso
        ((upperStarComp A p f (pullback.fst W.hom f ≫ W.hom)
          pullback.condition).symm.app G))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem pullbackSectionsEquiv_apply {R X : Scheme.{u}}
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : R.Etale) (f : X ⟶ R)
    (s : ((lowerStar AddCommGrpCat.{u + 1} f).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj G)).obj.obj (op W)) :
    pullbackSectionsEquiv G W f s =
      ((etaleObjectSectionsIso ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)).hom.app
          ((upperStar AddCommGrpCat.{u + 1} f).obj G) ≫
        (Sheaf.Γ (pullback W.hom f).smallEtaleTopology AddCommGrpCat.{u + 1}).map
          ((upperStarComp AddCommGrpCat.{u + 1} (pullback.snd W.hom f) f
            (pullback.fst W.hom f ≫ W.hom) pullback.condition).inv.app G)) s := by
  rfl

set_option linter.unusedVariables false in
-- Projection equality proofs are referenced only through proof-irrelevant arguments.
set_option maxRecDepth 4000 in
-- The concrete abelian-sheaf functors require extra reduction during elaboration.
/-- Evaluation of f_* f^* G at an étale object W identifies naturally with the global
sections of the pullback of G to W ×_R X. This is a comparison for a single cartesian
square, independent of any limit or compactness hypotheses.
Source: Stacks Project, Tags 03S2, 03CF and 03EF.
(blueprint: lem-weil-pbc-pullback-sections-comparison)

Proof: By the definition of direct image, the source is (f^* G)(W ×_R X). Restriction
along the étale second projection identifies this with Γ(W ×_R X, p^* f^* G), using the
étale inverse-image/restriction isomorphism and evaluation at the terminal object.
Compose with the inverse-image composition isomorphism and the equality
p ≫ f = fst ≫ W.hom to obtain the displayed additive equivalence. For a cartesian map m,
apply the restriction/pullback-unit identity to the square over h. Naturality of the
restriction isomorphism moves the composition isomorphism past restriction. Naturality
of the unit moves the source composition isomorphism past pullback. Associativity of
inverse-image composition identifies the resulting composites. The two projection
equations specify the canonical cartesian map, so this proves the stated equality for
any m satisfying them. Every map is additive, and hence the equivalences preserve zero. -/
theorem pullbackSections_comparison (R : Scheme.{u})
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : R.Etale) :
    let A := AddCommGrpCat.{u + 1}
    let v := fun {X : Scheme.{u}} (f : X ⟶ R) ↦ pullback.fst W.hom f ≫ W.hom
    let F := fun {X : Scheme.{u}} (f : X ⟶ R) ↦ (upperStar A (v f)).obj G
    let e := fun {X : Scheme.{u}} (f : X ⟶ R) ↦ pullbackSectionsEquiv G W f
      ∀ {X Y : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ R) (g : X ⟶ R)
        (w : g = h ≫ f) (m : pullback W.hom g ⟶ pullback W.hom f)
        (hm : m ≫ pullback.fst W.hom f = pullback.fst W.hom g)
        (hm' : m ≫ pullback.snd W.hom f = pullback.snd W.hom g ≫ h)
        (s : ((lowerStar A f).obj ((upperStar A f).obj G)).obj.obj (op W)),
        e g (((lowerStar A f).map
            ((upperStarLowerStarAdjunction A h).unit.app ((upperStar A f).obj G)) ≫
          (lowerStarComp A h f g w).hom.app _ ≫
          (lowerStar A g).map ((upperStarComp A h f g w).inv.app G)).hom.app (op W) s) =
        (globalSectionsUpperStarMap A m (F f) ≫
          (Sheaf.Γ (pullback W.hom g).smallEtaleTopology A).map
            ((upperStarComp A m (v f) (v g)
              (by dsimp [v]; rw [← Category.assoc, hm])).inv.app G)) (e f s) := by
  dsimp
  intro X Y h f g w m hm hm' s
  let A := AddCommGrpCat.{u + 1}
  let Vf := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W
  let Vg := (MorphismProperty.Over.pullback @Etale ⊤ g).obj W
  let H := (upperStar A f).obj G
  let d := (upperStarComp A h f g w).inv.app G
  let cf := (upperStarComp A Vf.hom f (pullback.fst W.hom f ≫ W.hom)
    pullback.condition).inv.app G
  let cg := (upperStarComp A Vg.hom g (pullback.fst W.hom g ≫ W.hom)
    pullback.condition).inv.app G
  let cm := (upperStarComp A m (pullback.fst W.hom f ≫ W.hom)
    (pullback.fst W.hom g ≫ W.hom)
    (by rw [← Category.assoc, hm])).inv.app G
  let Γg := Sheaf.Γ Vg.left.smallEtaleTopology A
  let Γf := Sheaf.Γ Vf.left.smallEtaleTopology A
  let ef := (etaleObjectSectionsIso Vf).hom.app H
  let eg := (etaleObjectSectionsIso Vg).hom.app ((upperStar A g).obj G)
  let rho := (((lowerStar A f).map ((upperStarLowerStarAdjunction A h).unit.app H) ≫
    (lowerStarComp A h f g w).hom.app _).hom.app (op W))
  rw [pullbackSectionsEquiv_apply, pullbackSectionsEquiv_apply]
  change ((rho ≫ ((lowerStar A g).map d).hom.app (op W)) ≫ eg ≫ Γg.map cg) s =
    ((ef ≫ Γf.map cf) ≫ globalSectionsUpperStarMap A m _ ≫ Γg.map cm) s
  apply ConcreteCategory.congr_hom
  have hn := (etaleObjectSectionsIso Vg).hom.naturality d
  change ((lowerStar A g).map d).hom.app (op W) ≫ eg =
    (etaleObjectSectionsIso Vg).hom.app ((upperStar A h).obj H) ≫
      Γg.map ((upperStar A Vg.hom).map d) at hn
  have hb := etaleObjectSections_baseChange W h f g w m hm hm' H
  let b := m ≫ Vf.hom
  let c₁ := upperStarComp A m Vf.hom b rfl
  let c₂ := upperStarComp A Vg.hom h b hm'
  change rho ≫ (etaleObjectSectionsIso Vg).hom.app ((upperStar A h).obj H) =
    ef ≫ globalSectionsUpperStarMap A m _ ≫ Γg.map (c₁.inv.app H ≫ c₂.hom.app H) at hb
  have hc : c₂.hom.app H ≫ (upperStar A Vg.hom).map d ≫ cg =
      c₁.hom.app H ≫ (upperStar A m).map cf ≫ cm := by
    have hbf : pullback.fst W.hom g ≫ W.hom = b ≫ f := by
      change pullback.fst W.hom g ≫ W.hom = (m ≫ pullback.snd W.hom f) ≫ f
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hm]
    have h₁ := upperStarComp_hom_app_map_upperStarComp_inv_app A
      Vg.hom h f b g (pullback.fst W.hom g ≫ W.hom) hm' w hbf G
    have h₂ := upperStarComp_hom_app_map_upperStarComp_inv_app A
      m Vf.hom f b (pullback.fst W.hom f ≫ W.hom)
      (pullback.fst W.hom g ≫ W.hom) rfl pullback.condition hbf G
    dsimp [d, cf, cg, cm, c₁, c₂, H]
    rw [← Category.assoc, h₁, ← Category.assoc, h₂]
    simp
  rw [Category.assoc, reassoc_of% hn, ← Category.assoc, hb]
  simp only [Γg.map_comp, Category.assoc]
  rw [← Γg.map_comp, ← Γg.map_comp, ← Γg.map_comp, hc]
  simp only [Iso.inv_hom_id_app_assoc, Γg.map_comp]
  have natural : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      {B C : Sheaf X.smallEtaleTopology A} (g : B ⟶ C),
      (Sheaf.Γ X.smallEtaleTopology A).map g ≫ globalSectionsUpperStarMap A f C =
        globalSectionsUpperStarMap A f B ≫
          (Sheaf.Γ Y.smallEtaleTopology A).map ((upperStar A f).map g) := by
    intro X Y f B C g
    unfold globalSectionsUpperStarMap
    rw [Category.assoc, Category.assoc,
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology A
        terminalIsTerminal).hom.naturality_assoc g]
    have hn := (upperStarLowerStarAdjunction A f).unit.naturality g
    simp only [Functor.id_map] at hn
    rw [← Functor.map_comp_assoc, hn, Functor.map_comp]
    simp only [Category.assoc]
    rw [← (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology A
        terminalIsTerminal).inv.naturality]
    congr 1
    congr 1
    have hu := ((upperStar A f).map g).hom.naturality
      (PreservesTerminal.iso (Scheme.Hom.Etale f)).inv.op
    simp only [Functor.comp_map, Functor.flip_obj_map, ObjectProperty.ι_map]
    erw [lowerStar_map_hom_app]
    simpa only [Category.assoc] using! congrArg (fun a ↦ a ≫
      (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology A
        terminalIsTerminal).inv.app ((upperStar A f).obj C)) hu.symm
  have hg := natural m cf
  change Γf.map cf ≫ globalSectionsUpperStarMap A m _ =
    globalSectionsUpperStarMap A m _ ≫ Γg.map ((upperStar A m).map cf) at hg
  rw [reassoc_of% hg]


end AlgebraicGeometry.Etale
