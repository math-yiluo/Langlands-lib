/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleOpenObjectCohomologyMap
import WeilConjectures.AlgebraicGeometry.EtaleOpenSectionPullback

/-! # Identity-generator coherence for nested open subschemes

Source: Stacks Project, Tag 03F3, and the open-restriction adjunction unit calculation.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The identity generator restricts to the inclusion generator on a smaller open.
Source: Stacks Project, Tag 03F3, localization restriction; the explicit adjunction
unit calculation in open_restriction_pullback_unit.
(blueprint: lem-weil-pbc-etale-open-free-sheaf-unit-coherence)

Proof: Apply the constant-sheaf adjunction at the terminal object of V to both sides.
On the left, etaleOpenFreeSheafUnit V is the identity generator of the free sheaf
at V. The free-representable map sends this generator to the inclusion V to U.
On the right, the constant pullback comparison sends 1 to 1, and pulling back the
identity generator at U gives the same inclusion generator over V. To check this
with the specified inverse-image comparisons, apply open_restriction_pullback_unit
with g equal to U.ι and W equal to V. The fibre product V times_X U identifies
with V, since V is contained in U and U.ι is a monomorphism. The identity unit
cancels against the identity comparison. The inverse-image composition unit equation
then identifies the two successive restriction comparisons with the direct one.
Naturality of sheafification and of the free functor sends the generator associated
to the identity of V to the generator associated to X.homOfLE h. Thus both sides
classify the same section, and the adjunction bijection proves the equality.
This calculation is valid for equal opens and for the empty open as well. -/
theorem etaleOpenFreeSheafUnit_coherence {X : Scheme.{u}}
    (U V : X.Opens) (h : V ≤ U) :
    etaleOpenFreeSheafUnit V ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} V.ι).map
          ((etaleOpenFreeSheaf X).map
            (MorphismProperty.Over.homMk (P := @Etale) (Q := ⊤) (X := X)
              (A := Scheme.Etale.mk V.ι) (B := Scheme.Etale.mk U.ι)
              (X.homOfLE h) (X.homOfLE_ι h) trivial)) ≫
        (Etale.upperStarComp AddCommGrpCat.{u + 1} (X.homOfLE h) U.ι V.ι
          (X.homOfLE_ι h).symm).hom.app
            ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι)) =
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (X.homOfLE h)).inv.app
        (AddCommGrpCat.of (ULift ℤ))) ≫
      (Etale.upperStar AddCommGrpCat.{u + 1} (X.homOfLE h)).map
        (etaleOpenFreeSheafUnit U) := by
  let a : Scheme.Etale.mk V.ι ⟶ Scheme.Etale.mk U.ι :=
    MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι h) trivial
  let A := (etaleOpenFreeSheaf X).obj (Scheme.Etale.mk U.ι)
  let b := Scheme.Etale.mk (𝟙 V.toScheme)
  let v : X.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale V.ι)).obj b
  let t : v ⟶ Scheme.Etale.mk V.ι :=
    MorphismProperty.Over.homMk (𝟙 V.toScheme) (by rfl)
  let s : A.obj.obj (Opposite.op v) :=
    (toSheafify X.smallEtaleTopology
      (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk U.ι) ⋙ AddCommGrpCat.free)).app
        (Opposite.op v) (FreeAbelianGroup.of ⟨t ≫ a⟩)
  have hs : (((Etale.upperStar AddCommGrpCat.{u + 1} V.ι).map
      ((etaleOpenFreeSheaf X).map a)).hom.app (Opposite.op b)) (etaleOpenFreeSheafSection V) =
      (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} V.ι
        inferInstance).inv.app A).hom.app (Opposite.op b)) s := by
    have hn := (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} V.ι
      inferInstance).inv.naturality ((etaleOpenFreeSheaf X).map a)
    have hn' := congrArg (fun f ↦ f.hom.app (Opposite.op b)) hn
    change _ ≫ _ = _ ≫ _ at hn'
    dsimp [etaleOpenFreeSheafSection]
    rw [← ConcreteCategory.comp_apply, ← hn', ConcreteCategory.comp_apply]
    congr 1
    have ht := toSheafify_naturality X.smallEtaleTopology
      (Functor.whiskerRight (uliftYoneda.{u + 1}.map a) AddCommGrpCat.free)
    have ht' := NatTrans.congr_app ht (Opposite.op v)
    dsimp only [NatTrans.comp_app] at ht'
    change (((toSheafify X.smallEtaleTopology
      (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk V.ι) ⋙ AddCommGrpCat.free)).app
        (Opposite.op v)) ≫ (sheafifyMap X.smallEtaleTopology
          (Functor.whiskerRight (uliftYoneda.{u + 1}.map a) AddCommGrpCat.free)).app
            (Opposite.op v)) (FreeAbelianGroup.of ⟨t⟩) = s
    rw [← ht']
    rfl
  let adj := constantSheafAdj V.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}
    (show Limits.IsTerminal b from Limits.IsTerminal.ofUniqueHom
      (fun a ↦ MorphismProperty.Over.homMk a.hom (Category.comp_id _))
      (fun a f ↦ by
        apply MorphismProperty.Over.Hom.ext
        exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w f)))
  apply (cancel_mono ((Etale.upperStarComp AddCommGrpCat.{u + 1}
    (X.homOfLE h) U.ι V.ι (X.homOfLE_ι h).symm).inv.app A)).1
  dsimp only [A]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  apply (adj.homEquiv _ _).injective
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
  rw [etaleOpenSection_pullback U V h A (etaleOpenFreeSheafUnit U)]
  rw [adj.homEquiv_naturality_right]
  dsimp only [adj, b, A]
  simp only [etaleOpenFreeSheafUnit, Equiv.apply_symm_apply]
  have hz {B C : AddCommGrpCat.{u + 1}}
      (f : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ B) (g : B ⟶ C) :
      AddCommGrpCat.uliftZMultiplesAddEquiv C (f ≫ g) =
        g (AddCommGrpCat.uliftZMultiplesAddEquiv B f) := by rfl
  rw [hz]
  simp only [AddEquiv.apply_symm_apply]
  change (((Etale.upperStar AddCommGrpCat.{u + 1} V.ι).map
    ((etaleOpenFreeSheaf X).map a)).hom.app (Opposite.op b)) (etaleOpenFreeSheafSection V) = _
  rw [hs]
  congr 1
  dsimp [etaleOpenFreeSheafSection]
  simp only [AddEquiv.apply_symm_apply]
  rw [← ConcreteCategory.comp_apply]
  have hc := congrArg (fun f ↦ f.hom.app (Opposite.op (Scheme.Etale.mk (𝟙 U.toScheme))))
    ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.ι
      inferInstance).inv_hom_id_app A)
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hc
  rw [hc]
  let bU := Scheme.Etale.mk (𝟙 U.toScheme)
  let vU : X.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale U.ι)).obj bU
  let tU : vU ⟶ Scheme.Etale.mk U.ι :=
    MorphismProperty.Over.homMk (𝟙 U.toScheme) (by rfl)
  let f : v ⟶ vU := MorphismProperty.Over.homMk (X.homOfLE h)
    (by
      change X.homOfLE h ≫ (𝟙 U.toScheme ≫ U.ι) = 𝟙 V.toScheme ≫ V.ι
      simpa only [Category.id_comp] using X.homOfLE_ι h) trivial
  change s = A.obj.map f.op
    ((toSheafify X.smallEtaleTopology
      (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk U.ι) ⋙ AddCommGrpCat.free)).app
        (Opposite.op vU) (FreeAbelianGroup.of ⟨tU⟩))
  have ht := (toSheafify X.smallEtaleTopology
    (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk U.ι) ⋙ AddCommGrpCat.free)).naturality f.op
  have he : f ≫ tU = t ≫ a := by
    apply MorphismProperty.Over.Hom.ext
    change X.homOfLE h ≫ 𝟙 U.toScheme = 𝟙 V.toScheme ≫ X.homOfLE h
    simp only [Category.comp_id, Category.id_comp]
  have ht' := ConcreteCategory.congr_hom ht (FreeAbelianGroup.of (ULift.up tU))
  change (toSheafify X.smallEtaleTopology
    (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk U.ι) ⋙ AddCommGrpCat.free)).app
      (Opposite.op v) (FreeAbelianGroup.of ⟨f ≫ tU⟩) =
    A.obj.map f.op ((toSheafify X.smallEtaleTopology
      (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk U.ι) ⋙ AddCommGrpCat.free)).app
        (Opposite.op vU) (FreeAbelianGroup.of ⟨tU⟩)) at ht'
  rw [he] at ht'
  exact ht'

end AlgebraicGeometry
