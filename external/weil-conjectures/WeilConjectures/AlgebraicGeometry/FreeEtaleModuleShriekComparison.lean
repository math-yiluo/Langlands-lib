/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Free etale module sheaves as extensions by zero

Source: Stacks Project, Modules on Sites, Tag 03DI and the equation following it.
(blueprint: lem-weil-pbc-free-etale-module-shriek-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] (W : X.Etale)

private noncomputable def sectionEquiv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ) ⟶ F) ≃ F.obj.obj (op W) :=
  ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).homEquiv _ _).trans
    (((ModuleCat.adj Λ).whiskerRight X.Etaleᵒᵖ).homEquiv _ _ |>.trans
      uliftYonedaEquiv)
private def etaleIdIsTerminal (Y : Scheme.{u}) :
    IsTerminal (Scheme.Etale.mk (𝟙 Y)) :=
  IsTerminal.ofUniqueHom
    (fun V ↦ MorphismProperty.Over.homMk V.hom (Category.comp_id _))
    (fun V f ↦ MorphismProperty.Over.Hom.ext
      ((Category.comp_id f.left).symm.trans f.w))

private noncomputable def localizationTerminalIso :
    (MorphismProperty.Over.map ⊤ (inferInstance : Etale W.hom)).obj
      (Scheme.Etale.mk (𝟙 W.left)) ≅ W :=
  MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _).symm

private noncomputable def shriekSectionEquiv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) W.hom inferInstance).obj
      ((constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ)) ⟶ F) ≃ F.obj.obj (op W) :=
  ((Etale.etaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) W.hom inferInstance).homEquiv _ F).trans
    ((Iso.homCongr (Iso.refl _)
      ((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ)
        W.hom inferInstance).app F)).trans
    (((constantSheafAdj W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      (etaleIdIsTerminal W.left)).homEquiv _ _).trans
      (ModuleCat.homEquiv.trans
        ((LinearMap.ringLmapEquivSelf Λ Λ _).toEquiv.trans
          (F.obj.mapIso (localizationTerminalIso X W).op).toLinearEquiv.toEquiv))))

private lemma sectionEquiv_comp
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (f : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ) ⟶ F) (h : F ⟶ G) :
    sectionEquiv X Λ W G (f ≫ h) = h.hom.app (op W) (sectionEquiv X Λ W F f) := by
  dsimp only [sectionEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right]
  erw [Adjunction.homEquiv_naturality_right]
  erw [uliftYonedaEquiv_comp]

private lemma shriekSectionEquiv_comp
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (f : (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) W.hom inferInstance).obj
      ((constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ)) ⟶ F) (h : F ⟶ G) :
    shriekSectionEquiv X Λ W G (f ≫ h) =
      h.hom.app (op W) (shriekSectionEquiv X Λ W F f) := by
  dsimp only [shriekSectionEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right]
  simp only [Iso.homCongr_apply, Iso.refl_inv, Category.id_comp, Category.assoc]
  erw [(Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ)
    W.hom inferInstance).hom.naturality h, ← Category.assoc]
  erw [Adjunction.homEquiv_naturality_right]
  let a := (constantSheafAdj W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (etaleIdIsTerminal W.left)).homEquiv _ _
      (((Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ)
        W.hom inferInstance).homEquiv _ F) f ≫
        (Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ)
          W.hom inferInstance).hom.app F)
  let i := localizationTerminalIso X W
  change G.obj.map i.inv.op (h.hom.app _ (a.hom 1)) =
    h.hom.app _ (F.obj.map i.inv.op (a.hom 1))
  exact congrArg (fun k : F.obj.obj (op _) ⟶ G.obj.obj (op W) ↦ k (a.hom 1))
    (h.hom.naturality i.inv.op).symm

/-- The sheafified free module on an etale representable is extension by zero of
its constant rank-one module sheaf.

Source: Stacks Project, Modules on Sites, Tag 03DI, and
`equation-map-lower-shriek-OU-into-module` immediately following it.
(blueprint: lem-weil-pbc-free-etale-module-shriek-comparison).

Proof: The free-module adjunction followed by Yoneda identifies maps from the
presheaf `uliftYoneda.obj W` composed with `ModuleCat.free` to the underlying
presheaf of F with sections of F on W. Sheafification preserves this bijection.
The localization adjunction for the etale map W.hom identifies maps from its
extension by zero of the constant rank-one sheaf to F with maps from that constant
sheaf to the restriction of F. By the constant-sheaf adjunction, these are maps
from the rank-one module to global sections on W. W is the terminal object of
its small etale site, so global sections are F(W), and a linear map from the
rank-one module is determined freely by the image of 1. Both bijections are
natural in F. The uniqueness of representing objects gives the asserted iso.
This uses no affineness or separation condition on W.hom. -/
theorem free_etale_module_shriek_comparison
    (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] (W : X.Etale) :
    Nonempty
      ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ) ≅
        (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) W.hom inferInstance).obj
          ((constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ Λ))) := by
  let e (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    (sectionEquiv X Λ W F).trans (shriekSectionEquiv X Λ W F).symm
  refine ⟨Coyoneda.ext _ _ (fun f ↦ e _ f) (fun f ↦ (e _).symm f)
    (fun f ↦ by simp) (fun f ↦ by simp) (fun f h ↦ ?_)⟩
  apply (sectionEquiv X Λ W _).injective
  dsimp only [e, Equiv.symm_trans, Equiv.trans_apply]
  rw [Equiv.apply_symm_apply, sectionEquiv_comp, Equiv.apply_symm_apply]
  simpa only [Equiv.symm_symm] using shriekSectionEquiv_comp X Λ W f h

end AlgebraicGeometry.Scheme
