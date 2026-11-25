/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
public import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import WeilConjectures.AlgebraicGeometry.StrictLocalSectionPullback

/-! # Exchange and the representative restriction comparison

Source: Stacks Project, Tags 03Q1 and 0A3U, expanded compatibility in degree zero.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem module_inverseImage_stalk_germ
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : X.Etale)
    (ū : (Scheme.pointSmallEtale (y ≫ f)).fiber.obj U) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G).hom.app
        (op U) ≫
      (Scheme.pointSmallEtale y).toPresheafFiber (f.Etale.obj U)
        ((Scheme.pointSmallEtaleFiberEtaleIso f y).inv.app U ū)
        ((upperStar (ModuleCat.{u + 1} Λ) f).obj G).obj ≫
      (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) f y).hom.app G =
      (Scheme.pointSmallEtale (y ≫ f)).toPresheafFiber U ū G.obj := by
  rw [← Category.assoc]
  apply (Iso.eq_comp_inv ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) f y).app G)).1
  simp only [upperStarCompSheafFiberIso, Iso.app_inv, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc]
  rw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  rw [show (Scheme.pointSmallEtale y).sheafFiber.map _ =
    (Scheme.pointSmallEtale y).presheafFiber.map _ from rfl,
    GrothendieckTopology.Point.toPresheafFiber_naturality]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Functor.sheafAdjunctionContinuous
      (MorphismProperty.Over.pullback @Etale ⊤ f) (ModuleCat.{u + 1} Λ)
      (X.smallGrothendieckTopology (P := @Etale))
      (Y.smallGrothendieckTopology (P := @Etale)))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f) G
  have huU := NatTrans.congr_app (Sheaf.hom_ext_iff.1 hu) (op U)
  rw [← Category.assoc, ← huU]
  rfl


set_option maxRecDepth 2048 in
/-- Any linear map with the strict-local representative formula intertwines exchange
with restriction to a pointed fibre. This is a compatibility result, with no qcqs,
properness, local-ring, closed-point or invertibility hypothesis.
Source: Stacks Project, Tag 03Q1 (3), and Tag 0A3U, compatibility omitted there;
expanded as step 3 of `lem-weil-pbc-qcqs-geometric-exchange-factorization`.
(blueprint: lem-weil-pbc-strict-local-exchange-compatibility).

Proof: the affine pointed neighbourhoods are initial among all pointed neighbourhoods,
so their germs are jointly epimorphic. Precompose the equality with these germs after
transport through the inverse-image stalk isomorphism. The inverse-image germ formula
identifies this composite with the germ of the unit section at the induced pointed
neighbourhood over Spec Ω. Expand `baseChangeMap` as unit, the square inverse-image
comparison, and counit. Naturality of the germ maps, the adjunction identities, and the
composition-unit identity show that this composite is restriction of the original
section to the pointed fibre. On the right, `ha` replaces the strict-local comparison
by its unit and limit-leg restriction. The equation `hpoint` says that the limit leg
restricted along t is exactly the original pointed neighbourhood map. The pullback
universal property, `hqt`, and `hq` therefore identify the two fibre restriction maps.
The composition inverse `upperStarComp` identifies the iterated inverse image with
inverse image along g'. Finally expand `lowerStarCompGlobalSectionsIso` and the
terminal germ: both sides evaluate the same pulled-back section and take its identity
neighbourhood germ. Cancel the inverse-image stalk isomorphism, and use the jointly
epimorphic affine germs to conclude. This proof uses only the representative formula,
not bijectivity of a; it works for zero modules and empty schemes as well. -/
theorem strictLocal_exchange_compatibility
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (t : Spec (.of Ω) ⟶ Scheme.strictLocalization s)
    (hpoint : ∀ j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s),
      t ≫ (Scheme.strictHenselizationAffineCone s).π.app (op (op j)) ≫
        (Spec (unop ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{u}
          (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2.left)
    (q : X' ⟶ pullback f (Scheme.strictLocalizationToBase s))
    (hqt : q ≫ pullback.snd f (Scheme.strictLocalizationToBase s) = f' ≫ t)
    (hq : q ≫ pullback.fst f (Scheme.strictLocalizationToBase s) = g')
    (a : (Scheme.pointSmallEtale s).sheafFiber.obj
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ⟶
      (Sheaf.Γ (pullback f (Scheme.strictLocalizationToBase s)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F))
    (ha : IsQcqsStrictLocalModuleComparison Λ f s F a) :
    let H := (upperStar (ModuleCat.{u + 1} Λ)
      (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F
    (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map
        ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) =
      (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) s
        (𝟙 (Spec (.of Ω)))).hom.app ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F) ≫
      eqToHom (by rw [Category.id_comp]) ≫
      a ≫ globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q H ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) q
          (pullback.fst f (Scheme.strictLocalizationToBase s)) g' hq.symm).inv.app F) ≫
      (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f').inv.app
        ((upperStar (ModuleCat.{u + 1} Λ) g').obj F) ≫
      (Sheaf.ΓNatIsoSheafSections _ _
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ (Spec (.of Ω)))
          (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) Over.mkIdTerminal)).hom.app
            ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
              ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)) ≫
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
        (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
        (Over.homMk (𝟙 _) (Category.comp_id _))
        ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
          ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)).obj := by
  let P := (lowerStar (ModuleCat.{u + 1} Λ) f).obj F
  let e := geometricPointSourceStalkIso Λ s P
  let r := globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) q
        ((upperStar (ModuleCat.{u + 1} Λ)
          (pullback.fst f (Scheme.strictLocalizationToBase s))).obj F) ≫
      (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) q
          (pullback.fst f (Scheme.strictLocalizationToBase s)) g' hq.symm).inv.app F)
  let b := (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f').inv.app
        ((upperStar (ModuleCat.{u + 1} Λ) g').obj F) ≫
      (Sheaf.ΓNatIsoSheafSections _ _
        (IsTerminal.isTerminalOfObj
          (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ (Spec (.of Ω)))
          (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) Over.mkIdTerminal)).hom.app
            ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
              ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)) ≫
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
        (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
        (Over.homMk (𝟙 _) (Category.comp_id _))
        ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
          ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)).obj
  change _ = e.hom ≫ a ≫ r ≫ b
  apply (Iso.inv_comp_eq e).1
  let N := (equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
    Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
      (fun n : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)
  have : N.Initial := (Scheme.strictHenselizationAffineProperties s).1
  let c := ((Scheme.pointSmallEtale s).presheafFiberCocone P.obj).whisker N.op
  let hc : IsColimit c :=
    (Functor.Final.isColimitWhiskerEquiv N.op _).symm
      ((Scheme.pointSmallEtale s).isColimitPresheafFiberCocone P.obj)
  apply hc.hom_ext
  intro j
  change (Scheme.pointSmallEtale s).toPresheafFiber _ _ P.obj ≫
    (e.inv ≫ _) = (Scheme.pointSmallEtale s).toPresheafFiber _ _ P.obj ≫ (a ≫ r ≫ b)
  have he := exchange_pointed_representative Λ sq.toCommSq F
    ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j.unop).1)
    ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j.unop).2
  have hr := strictLocal_section_pullback Λ sq.toCommSq F t hpoint q hqt hq j.unop
  have h := congrArg (fun k ↦ k ≫ r ≫ b) (ha j.unop)
  simpa only [r, b, e, P, N, Scheme.strictHenselizationAffineInclusion,
    Functor.comp_obj, Functor.op_obj, ObjectProperty.ι, ObjectProperty.lift,
    Functor.Elements.precomp, inducedFunctor, Functor.elementsMk, Category.assoc] using
    (he.trans (congrArg (fun k ↦ k ≫ b) hr).symm).trans h.symm

end AlgebraicGeometry.Etale
