/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingInverseImageComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleInverseImageTransport

/-!
# Exact inverse image of constant-ring modules on the small etale site

Source: Stacks Project, Modules on Sites, Tags 03D2, 03D3, 03D6, 03D7, 04JC;
Sites and Sheaves, Example 0H7J
(blueprint: situation-conventions).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry

-- Elaborating the dependent witness package and its comparisons exceeds the default limit.
set_option backward.defeqAttrib.useBackward true in
/-- Constant-ring inverse image is the exact module pullback, with the abelian adjunction.
Source: Stacks Project, Tags 03D2, 03D3, 03D6, 03D7, 04JC and Example 0H7J
(blueprint: situation-conventions).

The names RV, RU, etaV and etaU are lambda-bound and immediately applied to the
constant ring sheaves and their sheafification units; these are reducible names, not
additional hypotheses. Lr is the ring inverse image, L0 the module
inverse image before transporting scalars, and LM the module inverse image over RU.

Proof:
1. The ring lift of situation-conventions and the
constant-sheaf adjunction (situation-conventions) identify
maps from the inverse image of RV with maps from R into global sections on U.
Yoneda gives c. Its adjoint gamma sends constant sections to constant sections,
by def-weil-pbc-constant-sheaf and def-weil-pbc-sheafification.
2. Apply the set inverse image to the action and the module axioms, using preservation
of finite products. This gives the unique action and the functor L0, compatible with
forgetting to abelian sheaves (situation-conventions). Transport along c
produces LM. Sectionwise extension of scalars along the ring isomorphism sends
(a tensor m) to c inverse(a) times m; sheafification gives the natural tensor comparison,
using def-pur-sheaf-tensor-product and def-weil-pbc-sheafification.
3. The faithful forgetful functor preserves kernels and cokernels, by
situation-conventions. The abelian inverse image is additive
and exact, by prop-weil-pbc-inverse-image-exact. Kernel and cokernel comparisons
are therefore isomorphisms after forgetting, hence before forgetting. Additivity,
kernels and cokernels give all finite limits and colimits. Alternatively use
situation-conventions for the colimit part.
4. By situation-conventions, the abelian adjunction restricts
to linear morphisms. Transport along c makes its right adjoint the direct image with
scalars restricted through gamma, as in def-weil-pbc-direct-image. Its unit and
counit are the abelian ones. This is the pullback of the flat ringed-site morphism
(u,c), by 03D6 and 03D7. -/
theorem etaleInverseImageModulesExact (U V : Scheme.{u}) (f : U ⟶ V)
    (R : CommRingCat.{u + 1}) :
    (fun (RV : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
      (RU : Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (etaV : ((Functor.const V.Etaleᵒᵖ).obj R) ⟶ RV.obj)
      (etaU : ((Functor.const U.Etaleᵒᵖ).obj R) ⟶ RU.obj) =>
    ∃ (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤ Sheaf U.smallEtaleTopology
      CommRingCat.{u + 1})
      (ar : Lr ⊣ (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology
        @Etale))
      (er : Lr ⋙ sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology ≅ sheafForget (D :=
        CommRingCat.{u + 1}) V.smallEtaleTopology ⋙ Scheme.etaleSetPullback f)
      (ea : Etale.upperStar AddCommGrpCat.{u + 1} f ⋙ sheafForget (D := AddCommGrpCat.{u + 1})
        U.smallEtaleTopology ≅ sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology ⋙
        Scheme.etaleSetPullback f)
      (gamma : RV ⟶ ((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology
        @Etale)).obj RU) (c : Lr.obj RV ≅ RU),
    ar.homEquiv RV RU c.hom = gamma ∧
    (∀ (W : V.Etaleᵒᵖ) (r : R),
      gamma.hom.app W ((etaV).app W r) =
        (etaU).app ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj W) r) ∧
    (∀ (G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
      (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (h : Lr.obj G ⟶ F),
      (sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology).map (ar.homEquiv G F h) =
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1)) (V.smallGrothendieckTopology
          @Etale) (U.smallGrothendieckTopology @Etale)).homEquiv ((sheafForget (D :=
          CommRingCat.{u + 1}) V.smallEtaleTopology).obj G) ((sheafForget (D := CommRingCat.{u +
          1}) U.smallEtaleTopology).obj F)
          (er.inv.app G ≫ (sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).map h)) ∧
    (∀ (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
      (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : (Etale.upperStar
        AddCommGrpCat.{u + 1} f).obj G ⟶ F),
      (sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).map
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv G F h) =
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1)) (V.smallGrothendieckTopology
          @Etale) (U.smallGrothendieckTopology @Etale)).homEquiv ((sheafForget (D :=
          AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj G) ((sheafForget (D := AddCommGrpCat.{u
          + 1}) U.smallEtaleTopology).obj F)
          (ea.inv.app G ≫ (sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).map h)) ∧
    ∃ (L0 : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
      1} RingCat.{u + 1})).obj RV) ⥤ SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj RV)))
      (LM : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
        1} RingCat.{u + 1})).obj RV) ⥤ SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU))
      (e0 : L0 ⋙ SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂
        CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj RV)) ≅ SheafOfModules.toSheaf
        ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)
        ⋙ Etale.upperStar AddCommGrpCat.{u + 1} f)
      (e : LM ⋙ SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u
        + 1} RingCat.{u + 1})).obj RU) ≅ SheafOfModules.toSheaf ((sheafCompose
        V.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV) ⋙
        Etale.upperStar AddCommGrpCat.{u + 1} f)
      (t : LM ⋙ SheafOfModules.pushforward (F := 𝟭 U.Etale) ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c).hom ≅ L0)
      (am : LM ⊣ SheafOfModules.pushforward (J := V.smallGrothendieckTopology @Etale) (K :=
        U.smallGrothendieckTopology @Etale) (F := MorphismProperty.Over.pullback @Etale ⊤ f)
        ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        gamma)),
    LM.Additive ∧ PreservesFiniteLimits LM ∧ PreservesFiniteColimits LM ∧
    (∀ G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj RV),
      (SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
        RingCat.{u + 1})).obj (Lr.obj RV))).map (t.hom.app G) ≫ e0.hom.app G = e.hom.app G) ∧
    (∀ G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj RV),
      ∃ (muV : ((sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology).obj RV) ⨯
        ((sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
        ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
        RingCat.{u + 1})).obj RV)).obj G)) ⟶
          (sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
            ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj RV)).obj G)),
      (∀ (W : V.Etaleᵒᵖ)
        (x : ((((sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology).obj RV) ⨯
          ((sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
          ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
          1} RingCat.{u + 1})).obj RV)).obj G))).obj.obj W)),
        HEq (muV.hom.app W x)
          (@SMul.smul (((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u
            + 1})).obj RV).obj.obj W) (G.val.obj W) (G.val.obj W).isModule.toSMul
          ((prod.fst : ((sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology).obj RV) ⨯
            ((sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
            ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj RV)).obj G)) ⟶ (sheafForget (D := CommRingCat.{u + 1})
            V.smallEtaleTopology).obj RV).hom.app W x : ((sheafCompose V.smallEtaleTopology
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV).obj.obj W)
            ((prod.snd : ((sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology).obj RV) ⨯
              ((sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
              ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u
              + 1} RingCat.{u + 1})).obj RV)).obj G)) ⟶ (sheafForget (D := AddCommGrpCat.{u + 1})
              V.smallEtaleTopology).obj ((SheafOfModules.toSheaf ((sheafCompose
              V.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)).obj
              G)).hom.app W x : G.val.obj W))) ∧
      ∃! (muU : ((sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).obj (Lr.obj RV)) ⨯
          ((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj
            ((SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj (Lr.obj RV))).obj (L0.obj G))) ⟶
          (sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj
            ((SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj (Lr.obj RV))).obj (L0.obj G))),
      (∀ (W : U.Etaleᵒᵖ)
        (x : ((((sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).obj (Lr.obj RV)) ⨯
          ((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj
            ((SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj (Lr.obj RV))).obj (L0.obj G)))).obj.obj W)),
        HEq (muU.hom.app W x)
          (@SMul.smul (((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u
            + 1})).obj (Lr.obj RV)).obj.obj W) ((L0.obj G).val.obj W) ((L0.obj G).val.obj
            W).isModule.toSMul
          ((prod.fst : ((sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).obj (Lr.obj
            RV)) ⨯ ((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj
            ((SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj (Lr.obj RV))).obj (L0.obj G))) ⟶ (sheafForget (D :=
            CommRingCat.{u + 1}) U.smallEtaleTopology).obj (Lr.obj RV)).hom.app W x :
            ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (Lr.obj RV)).obj.obj W)
            ((prod.snd : ((sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).obj
              (Lr.obj RV)) ⨯ ((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj
              ((SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u
              + 1} RingCat.{u + 1})).obj (Lr.obj RV))).obj (L0.obj G))) ⟶ (sheafForget (D :=
              AddCommGrpCat.{u + 1}) U.smallEtaleTopology).obj ((SheafOfModules.toSheaf
              ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u +
              1})).obj (Lr.obj RV))).obj (L0.obj G))).hom.app W x : (L0.obj G).val.obj W))) ∧
      (Scheme.etaleSetPullback f).map muV =
        prodComparison (Scheme.etaleSetPullback f) ((sheafForget (D := CommRingCat.{u + 1})
          V.smallEtaleTopology).obj RV)
          ((sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj
            ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj RV)).obj G)) ≫
        prod.map (er.inv.app RV)
          (((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).mapIso (e0.app G) ≪≫
            ea.app ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂
            CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)).obj G)).inv) ≫
        muU ≫ ((sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).mapIso (e0.app G) ≪≫
          ea.app ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂
            CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)).obj G)).hom) ∧
    (∃ (d : ∀ G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂
      CommRingCat.{u + 1} RingCat.{u + 1})).obj RV),
        SheafOfModules.changeOfRings.{u, u + 1, u + 1} (J := U.smallEtaleTopology) c.hom (L0.obj
          G) ≅ LM.obj G),
      (∀ (G H : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u
        + 1} RingCat.{u + 1})).obj RV)) (h : G ⟶ H),
        SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} (J := U.smallEtaleTopology) c.hom
          (L0.obj G) (L0.map h) ≫ (d H).hom =
          (d G).hom ≫ LM.map h) ∧
      (∀ (G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
        1} RingCat.{u + 1})).obj RV)) (W : U.Etaleᵒᵖ)
        (a : RU.obj.obj W) (m : (L0.obj G).val.obj W),
        (d G).hom.val.app W
          ((toSheafify U.smallEtaleTopology
            (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (J := U.smallEtaleTopology)
              c.hom (L0.obj G)).presheaf).app W
              (a ⊗ₜ[(Lr.obj RV).obj.obj W, (c.hom.hom.app W).hom] m)) =
          (t.inv.app G).val.app W ((c.inv.hom.app W a) • m))) ∧
    (∀ (G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
      1} RingCat.{u + 1})).obj RV)) (F : SheafOfModules.{u + 1} ((sheafCompose
      U.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU))
      (h : LM.obj G ⟶ F),
      (SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
        RingCat.{u + 1})).obj RV)).map (am.homEquiv G F h) =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
          ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
          1} RingCat.{u + 1})).obj RV)).obj G)
          ((SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj RU)).obj F)
          (e.inv.app G ≫ (SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂
            CommRingCat.{u + 1} RingCat.{u + 1})).obj RU)).map h)) ∧
    (∀ G : SheafOfModules.{u + 1} ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj RV),
      (SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
        RingCat.{u + 1})).obj RV)).map (am.unit.app G) =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
          ((SheafOfModules.toSheaf ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u +
          1} RingCat.{u + 1})).obj RV)).obj G) ≫
          (Etale.lowerStar AddCommGrpCat.{u + 1} f).map (e.inv.app G)) ∧
    (∀ F : SheafOfModules.{u + 1} ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
      RingCat.{u + 1})).obj RU),
      (SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u + 1}
        RingCat.{u + 1})).obj RU)).map (am.counit.app F) =
        e.hom.app ((SheafOfModules.pushforward (J := V.smallGrothendieckTopology @Etale) (K :=
          U.smallGrothendieckTopology @Etale) (F := MorphismProperty.Over.pullback @Etale ⊤ f)
          ((sheafCompose V.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          gamma)).obj F) ≫
          (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app
            ((SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u +
            1} RingCat.{u + 1})).obj RU)).obj F)))
      ((constantSheaf V.smallEtaleTopology CommRingCat.{u + 1}).obj R)
      ((constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj R)
      (toSheafify V.smallEtaleTopology ((Functor.const V.Etaleᵒᵖ).obj R))
      (toSheafify U.smallEtaleTopology ((Functor.const U.Etaleᵒᵖ).obj R)) := by
  classical
  obtain ⟨Lr, ar, er, ea, gamma, c, hc, hconst, hr, ha⟩ :=
    etaleConstantRingInverseImageComparison U V f R
  obtain ⟨L0, LM, e0, e, t, am, ht, hmu, hd, hm, hu, he⟩ :=
    etaleModuleInverseImageTransport U V f R _ _ _ _ Lr ar er ea gamma c
      hc hconst hr ha
  refine ⟨Lr, ar, er, ea, gamma, c, hc, hconst, hr, ha,
    L0, LM, e0, e, t, am, ?_, ?_, ?_, ht, hmu, hd, hm, hu, he⟩
  · let FU := SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj R))
    have : (LM ⋙ FU).Additive := Functor.additive_of_iso e.symm
    exact Functor.additive_of_comp_faithful LM FU
  · let FU := SheafOfModules.toSheaf ((sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj R))
    have : PreservesFiniteLimits (LM ⋙ FU) := preservesFiniteLimits_of_natIso e.symm
    exact preservesFiniteLimits_of_reflects_of_preserves LM FU
  · let := am.isLeftAdjoint
    infer_instance

end AlgebraicGeometry
