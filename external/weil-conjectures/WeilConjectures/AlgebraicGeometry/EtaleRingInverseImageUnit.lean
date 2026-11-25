/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.AlgebraicGeometry.EtaleRingDirectImageComparison

/-!
# A ring-valued lift of the étale set inverse image and its unit

Source: Stacks Project, Proposition 00YV, ring paragraph and Section 00YR.
(blueprint: lem-weil-pbc-etale-ring-inverse-image-unit).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Source: Stacks Project, Proposition 00YV, proof of (2), ring paragraph;
Section 00YR, sextuples.
(blueprint: lem-weil-pbc-etale-ring-inverse-image-unit).

Proof: Identify ring sheaves with internal commutative ring objects on both sites,
using the sectionwise-operation identifications. Finite-limit preservation of L
implies finite-product preservation. Apply the ring-only lifted adjunction
to the set adjunction. Compose its left functor with the two inverse identification
functors to obtain Lr, and compose their forgetful comparisons to obtain er.
On the right, the product comparisons for sectionwise precomposition identify each
transported operation with the original operation at the base-changed object.
Consequently the underlying right comparison is a ring isomorphism, natural in the
ring sheaf and site object, to Rr. Transport the lifted unit through this comparison.
Naturality of the transported unit follows from that of the original unit and the
comparisons. The generic lifted-unit formula becomes the displayed equality after
cancelling the inverse-identification components. This constructs only the unit;
no triangle identity or universal property of this unit is asserted here. -/
theorem etaleRingInverseImageUnit (U V : Scheme.{u}) (f : U ⟶ V)
    (hL : PreservesFiniteLimits (Scheme.etaleSetPullback f)) :
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let L := Scheme.etaleSetPullback f
    let R := b.sheafPushforwardContinuous (Type (u + 1))
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u + 1}
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
    let FrV := sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology
    let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    ∃ (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
          Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (er : Lr ⋙ FrU ≅ FrV ⋙ L) (η : 𝟭 _ ⟶ Lr ⋙ Rr),
      ∀ G, FrV.map (η.app G) = a.unit.app (FrV.obj G) ≫ R.map (er.inv.app G) := by
  let b := MorphismProperty.Over.pullback @Etale ⊤ f
  let L := Scheme.etaleSetPullback f
  let R : Sheaf U.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf V.smallEtaleTopology (Type (u + 1)) := b.sheafPushforwardContinuous (Type (u + 1))
    (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
  let Rr : Sheaf U.smallEtaleTopology CommRingCat.{u + 1} ⥤
      Sheaf V.smallEtaleTopology CommRingCat.{u + 1} :=
    b.sheafPushforwardContinuous CommRingCat.{u + 1}
    (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
  let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
  let FrV := sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology
  let a : L ⊣ R := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
    (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
    (U.smallGrothendieckTopology @Etale)
  let : PreservesFiniteLimits L := hL
  let : PreservesFiniteProducts L := ⟨fun n => inferInstance⟩
  obtain ⟨FU, GU, hFU, hGU, hFUGU, hGUFU, opsU⟩ :=
    sheavesAlgebraicStructuresRing_core.{u + 1, u, u + 1} U.smallEtaleTopology
  obtain ⟨FV, GV, hFV, hGV, hFVGV, hGVFV, opsV⟩ :=
    sheavesAlgebraicStructuresRing_core.{u + 1, u, u + 1} V.smallEtaleTopology
  let : PreservesLimitsOfSize.{0, 0} R := a.rightAdjoint_preservesLimits
  let : PreservesFiniteProducts R := ⟨fun n => inferInstance⟩
  obtain ⟨LF, RF, hLF, hRF, ar, opsL, opsR, homs, units, counits, criteria⟩ :=
    a.liftedCommRingBranch
  let Lr := FV ⋙ LF ⋙ GU
  have he : Lr ⋙ FrU = FrV ⋙ L := by
    change FV ⋙ LF ⋙ GU ⋙ FrU = FrV ⋙ L
    rw [show GU ⋙ FrU = CommRingObjCat.forget _ from hGU]
    rw [hLF]
    change (FV ⋙ CommRingObjCat.forget _) ⋙ L = FrV ⋙ L
    rw [show FV ⋙ CommRingObjCat.forget _ = FrV from hFV]
  let er : Lr ⋙ FrU ≅ FrV ⋙ L := eqToIso he
  obtain ⟨d, hd⟩ := etaleRingDirectImageComparison U V f
    FU GU hFU hGU hGUFU opsU FV GV hFV hGV hGVFV opsV RF hRF opsR
  change ∀ X, FrV.map (d.hom.app X) =
    (eqToIso hGV).hom.app (RF.obj X) ≫ (eqToIso hRF).hom.app X ≫
      R.map ((eqToIso hGU).inv.app X) at hd
  clear opsU opsV opsL opsR homs counits criteria
  let η : 𝟭 _ ⟶ Lr ⋙ Rr :=
    (eqToIso hFVGV).inv ≫ Functor.whiskerLeft FV (Functor.whiskerRight ar.unit GV) ≫
      Functor.whiskerLeft (FV ⋙ LF) d.hom
  refine ⟨Lr, er, η, ?_⟩
  intro G
  change FrV.map (η.app G) = a.unit.app (FrV.obj G) ≫ R.map (er.inv.app G)
  dsimp only [η, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [FrV.map_comp, FrV.map_comp, hd]
  dsimp only [Functor.comp_obj]
  change (FrV.map ((eqToIso hFVGV).inv.app G) ≫
      FrV.map (GV.map (ar.unit.app (FV.obj G)))) ≫
    (eqToIso hGV).hom.app (RF.obj (LF.obj (FV.obj G))) ≫
      (eqToIso hRF).hom.app (LF.obj (FV.obj G)) ≫
        R.map ((eqToIso hGU).inv.app (LF.obj (FV.obj G))) =
    a.unit.app (FrV.obj G) ≫ R.map (er.inv.app G)
  have hn := (eqToIso hGV).hom.naturality (ar.unit.app (FV.obj G))
  change FrV.map (GV.map (ar.unit.app (FV.obj G))) ≫
    (eqToIso hGV).hom.app (RF.obj (LF.obj (FV.obj G))) =
    (eqToIso hGV).hom.app (FV.obj G) ≫
      (CommRingObjCat.forget _).map (ar.unit.app (FV.obj G)) at hn
  rw [Category.assoc, ← Category.assoc (FrV.map (GV.map _)), hn]
  have hstart : FrV.map ((eqToIso hFVGV).inv.app G) ≫
      (eqToIso hGV).hom.app (FV.obj G) = (eqToIso hFV).inv.app G := by
    simp only [eqToIso, eqToHom_app, eqToHom_map, eqToHom_trans]
  simp only [Category.assoc]
  rw [← Category.assoc (FrV.map ((eqToIso hFVGV).inv.app G))
    ((eqToIso hGV).hom.app (FV.obj G)), hstart]
  have hu : (CommRingObjCat.forget _).map (ar.unit.app (FV.obj G)) ≫
      (eqToIso hRF).hom.app (LF.obj (FV.obj G)) =
      a.unit.app (FV.obj G).X ≫ R.map ((eqToIso hLF).inv.app (FV.obj G)) := by
    apply (cancel_mono (R.map ((eqToIso hLF).hom.app (FV.obj G)))).1
    simp only [Category.assoc]
    rw [← R.map_comp, (eqToIso hLF).inv_hom_id_app]
    dsimp only [Functor.comp_obj, Functor.id_obj, CommRingObjCat.forget_obj]
    rw [R.map_id, Category.comp_id]
    exact units (FV.obj G)
  have hn' := a.unit.naturality ((eqToIso hFV).inv.app G)
  change (eqToIso hFV).inv.app G ≫ a.unit.app (FV.obj G).X =
    a.unit.app (FrV.obj G) ≫ R.map (L.map ((eqToIso hFV).inv.app G)) at hn'
  have hend : L.map ((eqToIso hFV).inv.app G) ≫
      (eqToIso hLF).inv.app (FV.obj G) ≫
        (eqToIso hGU).inv.app (LF.obj (FV.obj G)) = er.inv.app G := by
    simp only [er, eqToIso, eqToHom_app, eqToHom_map, eqToHom_trans]
  rw [← Category.assoc ((CommRingObjCat.forget _).map _), hu]
  simp only [Category.assoc]
  rw [← Category.assoc ((eqToIso hFV).inv.app G), hn']
  simp only [Category.assoc, ← R.map_comp]
  rw [hend]


end AlgebraicGeometry
