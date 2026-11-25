/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Algebra.Category.Ring.Limits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.EtaleRingInverseImageUnit
import WeilConjectures.AlgebraicGeometry.EtaleRingInverseImageCounit
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# The ring-sheaf adjunction underlying the étale inverse image

Source: Stacks Project, Proposition 00YV and Section 00YR.
(blueprint: lem-weil-pbc-etale-inverse-image-ring-adjunction).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Sites and Sheaves, Proposition 00YV, ring paragraph;
Section 00YR, rings as sextuples.
(blueprint: lem-weil-pbc-etale-inverse-image-ring-adjunction).

Proof: Apply the ring clause of `sheaves_algebraicStructures_objects` to both sites.
Finite-limit preservation implies finite-product preservation for the set inverse
image. Apply the ring clause of `Adjunction.liftsGroupRingObjects` to its adjunction.
Compose the left and right lifted functors with the inverse functors between ring
sheaves and internal ring objects. The transported right functor is isomorphic to
sectionwise direct image: its underlying sheaf is precomposition with base change,
and the five transported operations are the original operations evaluated at each
base-changed object. The sectionwise identification is a ring homomorphism and is
natural in the sheaf. Transport the adjunction along this right-functor isomorphism.
Compose the left forgetful comparisons to obtain `er`. The generic lift's hom-set
identity, transported through the strict inverse functors and the right identification,
is precisely the asserted identity. This construction needs no assertion about the
left operation formulas; those will be deduced separately from this identity. -/
theorem etaleInverseImageRingAdjunction (U V : Scheme.{u}) (f : U ⟶ V)
    (hL : PreservesFiniteLimits (Scheme.etaleSetPullback f)) :
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let L := Scheme.etaleSetPullback f
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u + 1}
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
    let FrV := sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology
    let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    ∃ (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
          Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (ar : Lr ⊣ Rr) (er : Lr ⋙ FrU ≅ FrV ⋙ L),
        ∀ (G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
            (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (h : Lr.obj G ⟶ F),
          FrV.map (ar.homEquiv G F h) =
            a.homEquiv (FrV.obj G) (FrU.obj F) (er.inv.app G ≫ FrU.map h) := by
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
  obtain ⟨Lr, er, η, hη⟩ := etaleRingInverseImageUnit U V f hL
  obtain ⟨ε, hε⟩ := etaleRingInverseImageCounit U V f hL Lr er η hη
  change ∀ G, FrV.map (η.app G) =
    a.unit.app (FrV.obj G) ≫ R.map (er.inv.app G) at hη
  change ∀ F, FrU.map (ε.app F) =
    er.hom.app (Rr.obj F) ≫ a.counit.app (FrU.obj F) at hε
  let ar : Lr ⊣ Rr := {
    unit := η
    counit := ε
    left_triangle_components := by
      intro G
      apply FrU.map_injective
      rw [FrU.map_comp, FrU.map_id, hε]
      change FrU.map (Lr.map (η.app G)) ≫
        er.hom.app (Rr.obj (Lr.obj G)) ≫ a.counit.app (FrU.obj (Lr.obj G)) = 𝟙 _
      have hn : FrU.map (Lr.map (η.app G)) ≫ er.hom.app (Rr.obj (Lr.obj G)) =
          er.hom.app G ≫ L.map (FrV.map (η.app G)) := er.hom.naturality (η.app G)
      rw [← Category.assoc, hn]
      change er.hom.app G ≫ L.map (FrV.map (η.app G)) ≫
        a.counit.app (FrU.obj (Lr.obj G)) = 𝟙 _
      have hc : L.map (R.map (er.inv.app G)) ≫ a.counit.app (FrU.obj (Lr.obj G)) =
          a.counit.app (L.obj (FrV.obj G)) ≫ er.inv.app G :=
        a.counit_naturality (er.inv.app G)
      rw [hη, L.map_comp]
      simp only [Category.assoc]
      rw [hc]
      calc
        _ = er.hom.app G ≫ (L.map (a.unit.app (FrV.obj G)) ≫
            a.counit.app (L.obj (FrV.obj G))) ≫ er.inv.app G := by
          simp only [Category.assoc]
        _ = er.hom.app G ≫ er.inv.app G := by
          rw [a.left_triangle_components]
          exact congrArg (fun k ↦ k ≫ er.inv.app G)
            (Category.comp_id (er.hom.app G))
        _ = 𝟙 _ := er.hom_inv_id_app G
    right_triangle_components := by
      intro F
      apply FrV.map_injective
      rw [FrV.map_comp, FrV.map_id, hη]
      change (a.unit.app (FrV.obj (Rr.obj F)) ≫ R.map (er.inv.app (Rr.obj F))) ≫
        R.map (FrU.map (ε.app F)) = 𝟙 _
      rw [hε]
      calc
        _ = a.unit.app (FrV.obj (Rr.obj F)) ≫
            R.map ((er.inv.app (Rr.obj F) ≫ er.hom.app (Rr.obj F)) ≫
              a.counit.app (FrU.obj F)) := by simp only [R.map_comp, Category.assoc]
        _ = a.unit.app (FrV.obj (Rr.obj F)) ≫ R.map (a.counit.app (FrU.obj F)) := by
          rw [er.inv_hom_id_app]
          exact congrArg (fun k ↦ a.unit.app (FrV.obj (Rr.obj F)) ≫ R.map k)
            (Category.id_comp (a.counit.app (FrU.obj F)))
        _ = 𝟙 _ := a.right_triangle_components (FrU.obj F) }
  refine ⟨Lr, ar, er, ?_⟩
  intro G F h
  rw [ar.homEquiv_apply, FrV.map_comp, hη]
  change (a.unit.app (FrV.obj G) ≫ R.map (er.inv.app G)) ≫ R.map (FrU.map h) =
    a.homEquiv (FrV.obj G) (FrU.obj F) (er.inv.app G ≫ FrU.map h)
  rw [a.homEquiv_apply, R.map_comp, Category.assoc]

end AlgebraicGeometry
