/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleOpenObjectCohomologyMap
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # The identity-generator comparison on sheaf morphisms

Source: Stacks Project, Cohomology on Sites, Tag 03F3.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private noncomputable def freeSectionEquiv {X : Scheme.{u}} (U : X.Opens)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι) ⟶ F) ≃
      F.obj.obj (op (Scheme.Etale.mk U.ι)) :=
  ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ F).trans
    (((AddCommGrpCat.adj.whiskerRight (C := X.Etaleᵒᵖ)).homEquiv
      (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk U.ι)) F.obj).trans uliftYonedaEquiv)

/-- The degree-zero identity-generator comparison on morphisms is bijective.
Source: Stacks Project, Cohomology on Sites, Tag 03F3, free abelian representable
and constant-sheaf adjunctions.
(blueprint: lem-weil-pbc-etale-open-object-hom-bijective)

Proof: Sheafification, the free abelian group adjunction, and lifted Yoneda identify
morphisms from the free sheaf at U with sections F(U). The constant-sheaf adjunction
at the terminal object of U, followed by the integer-generator equivalence, identifies
morphisms from the constant integers with sections of the pulled-back sheaf at that
terminal object. The inverse-image/restriction isomorphism identifies these sections
with F(U). Naturality of the three adjunctions shows that sending f to the identity
unit followed by pullback of f becomes the identity on F(U): the free generator at
the identity is sent to the section corresponding to f. Thus this map is a composite
of bijections. Degree zero and the empty open require no separate assumption: Yoneda
and the terminal-object adjunction apply there as well. -/
theorem etaleOpenObjectHom_bijective {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : X.Opens) :
    Function.Bijective (fun f : (etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι) ⟶ F ↦
      etaleOpenFreeSheafUnit U ≫ (Etale.upperStar AddCommGrpCat.{u + 1} U.ι).map f) := by
  let b : U.toScheme.Etale := Scheme.Etale.mk (𝟙 U.toScheme)
  let hT : IsTerminal b := IsTerminal.ofUniqueHom
    (fun a ↦ MorphismProperty.Over.homMk a.hom (Category.comp_id _))
    (fun a f ↦ by
      apply MorphismProperty.Over.Hom.ext
      exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w f))
  let R := Etale.upperStar AddCommGrpCat.{u + 1} U.ι
  let ρ := Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.ι
    inferInstance
  let e := ((constantSheafAdj U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}
    hT).homEquiv _ (R.obj F)).trans
      ((AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv.trans
        (((sheafToPresheaf U.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          (evaluation U.toScheme.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op b)).mapIso
            (ρ.app F)).addCommGroupIsoToAddEquiv.toEquiv))
  have he (f : (etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι) ⟶ F) :
      e (etaleOpenFreeSheafUnit U ≫ R.map f) = freeSectionEquiv U F f := by
    dsimp only [e, Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_right]
    dsimp only [etaleOpenFreeSheafUnit]
    rw [Equiv.apply_symm_apply]
    simp only [AddEquiv.toEquiv_eq_coe]
    change ((ρ.hom.app F).hom.app (op b))
      ((AddCommGrpCat.uliftZMultiplesAddEquiv _)
        (((AddCommGrpCat.uliftZMultiplesAddEquiv _).symm
          (etaleOpenFreeSheafSection U)) ≫ (R.map f).hom.app (op b))) = _
    have hz {G H : AddCommGrpCat.{u + 1}} (a : G) (g : G ⟶ H) :
        AddCommGrpCat.uliftZMultiplesAddEquiv H
          ((AddCommGrpCat.uliftZMultiplesAddEquiv G).symm a ≫ g) = g a := by
      change (uliftZMultiplesHom H).symm (g.hom.comp ((uliftZMultiplesHom G) a)) = g a
      apply (uliftZMultiplesHom H).injective
      rw [Equiv.apply_symm_apply]
      ext n
      simp
    rw [hz]
    have hn := congrArg (fun t ↦ t.hom.app (op b)) (ρ.hom.naturality f)
    change (R.map f).hom.app (op b) ≫ (ρ.hom.app F).hom.app (op b) =
      (ρ.hom.app _).hom.app (op b) ≫
        ((Etale.localizationRestriction AddCommGrpCat.{u + 1} U.ι inferInstance).map f).hom.app
          (op b) at hn
    rw [← ConcreteCategory.comp_apply, hn, ConcreteCategory.comp_apply]
    dsimp only [etaleOpenFreeSheafSection]
    change (f.hom.app _)
      (((ρ.hom.app _).hom.app (op b))
        (((ρ.inv.app _).hom.app (op b)) _)) = _
    have hi := congrArg (fun t ↦ t.hom.app (op b)) (ρ.inv_hom_id_app
      ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι)))
    change (ρ.inv.app _).hom.app (op b) ≫ (ρ.hom.app _).hom.app (op b) = 𝟙 _ at hi
    rw [← ConcreteCategory.comp_apply, hi]
    change (f.hom.app _)
      (((toSheafify X.smallEtaleTopology
        (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk U.ι) ⋙ AddCommGrpCat.free)).app _)
          (FreeAbelianGroup.of ⟨𝟙 _⟩)) = _
    rfl
  apply (Function.Bijective.of_comp_iff' e.bijective _).mp
  change Function.Bijective (fun f ↦ e (etaleOpenFreeSheafUnit U ≫ R.map f))
  rw [show (fun f ↦ e (etaleOpenFreeSheafUnit U ≫ R.map f)) = freeSectionEquiv U F from
    funext he]
  exact (freeSectionEquiv U F).bijective

end AlgebraicGeometry
