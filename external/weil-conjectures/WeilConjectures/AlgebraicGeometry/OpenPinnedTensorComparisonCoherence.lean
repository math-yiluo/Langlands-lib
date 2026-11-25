/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenPinnedTargetCounitTriangle
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSourceCounitTriangle

/-! # Counit comparison for one open leg
Source: Stacks Project, Tags 08DW and 0D5S. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry
private theorem map_comparison_hom
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H)
    (P : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app P =
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P := rfl

private theorem map_comparison_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H)
    (P : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).inv.app P =
      (NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app P := rfl

private theorem lift_comparison
    {I C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive B] [Preadditive E]
    (T : I → C ⥤ E) [∀ i, (T i).Additive]
    (F : C ⥤ D) (G : D ⥤ E) (R : C ⥤ B) (J : B ⥤ E)
    [F.Additive] [G.Additive] [R.Additive] [J.Additive]
    {i j : I} (h : i = j) (a : F ⋙ G ≅ T j) (b : R ⋙ J ≅ T i)
    (r : F ⋙ G ≅ R ⋙ J) (P : HomotopyCategory C (.up ℤ))
    (hb : a.inv ≫ r.hom = eqToHom (congrArg T h).symm ≫ b.inv) :
    (Functor.mapHomotopyCategoryCompIso a (.up ℤ)).inv.app P ≫
      (Functor.mapHomotopyCategoryCompIso r (.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ J)) (.up ℤ)).symm).hom.app P =
    eqToHom (congrArg (fun i ↦ ((T i).mapHomotopyCategory (.up ℤ)).obj P) h).symm ≫
      (Functor.mapHomotopyCategoryCompIso b (.up ℤ)).inv.app P := by
  cases h
  simp only [eqToHom_refl, Category.id_comp] at hb ⊢
  have hh := congrArg (fun t ↦ (NatTrans.mapHomotopyCategory t (.up ℤ)).app P) hb
  simp only [NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app] at hh
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, map_comparison_hom,
    map_comparison_inv, Iso.refl_inv, NatTrans.mapHomotopyCategory_id,
    NatTrans.id_app, Category.comp_id] using hh

variable [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]

/-- Coherence of the underived localized comparison factors.
Source: Stacks Project, Tags 08DW and 08HY; the explicitly constructed tensor comparisons.
Proof: expand the restriction comparison into its four factors: the inverse
open comparison for U', the inverse target composition comparison, the source
composition comparison along hj, and the open comparison for U. The target
homotopy comparison is the inverse of the lift of the first two factors, so
these cancel. The last two factors are the source comparison. For an arbitrary
morphism f and an equality j ≫ U.ι = f, equality induction identifies the
composition comparison along that equality with the comparison at j ≫ U.ι
precomposed by equality transport. This induction generalizes f first, rather
than trying to eliminate the equality of two fixed composites. Apply this at
hj. Lifting additive functors to complexes and then to the homotopy quotient
preserves composition, inverses, and equality transport, giving the displayed
identity for every P. This argument uses only functor identities; it applies to
empty and top opens and zero complexes without any extra hypothesis.
(blueprint: lem-pc-open-pinned-tensor-counit-transport-coherence) -/
theorem open_pinned_tensor_comparison_coherence
    {X X' : Scheme.{u}} (k : X' ⟶ X)
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ k)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    (openPinnedHomotopyTargetCompositionIso k U').hom.app P ≫
      (openPinnedHomotopyTensorRestrictionIso k U U' j hj).hom.app P =
    eqToHom (congrArg (fun f ↦
      ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ)).obj P) hj).symm ≫
      (openPinnedHomotopySourceCompositionIso U j).hom.app P := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have ht : ∀ (f : U'.toScheme ⟶ X) (h : j ≫ U.ι = f),
      (Scheme.Modules.tensorPullbackCompositionIso j U.ι f h).hom =
        eqToHom (congrArg Scheme.Modules.tensorPullback h).symm ≫
          (Scheme.Modules.tensorPullbackCompositionIso j U.ι (j ≫ U.ι) rfl).hom := by
    intro f h
    cases h
    simp only [eqToHom_refl, Category.id_comp]
  have hb :
      (Functor.isoWhiskerLeft _ (openPinnedTensorOpenIso X' U').symm ≪≫
        (Scheme.Modules.tensorPullbackCompositionIso U'.ι k (U'.ι ≫ k) rfl).symm).inv ≫
        (openPinnedTensorRestrictionIso k U U' j hj).hom =
      eqToHom (congrArg Scheme.Modules.tensorPullback hj).symm ≫
        (Functor.isoWhiskerRight (openPinnedTensorOpenIso X U).symm _ ≪≫
          (Scheme.Modules.tensorPullbackCompositionIso j U.ι (j ≫ U.ι) rfl).symm).inv := by
    simp only [openPinnedTensorRestrictionIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    rw [ht _ hj]
    simp only [Category.assoc, Functor.isoWhiskerRight_inv, Iso.symm_inv,
      Functor.isoWhiskerRight_hom]
  have := schemeOpenRestriction_additive X U
  have := schemeOpenRestriction_additive X' U'
  exact lift_comparison
    (fun f : U'.toScheme ⟶ X ↦ Scheme.Modules.tensorPullback f)
    (Scheme.Modules.tensorPullback k) (schemeOpenRestriction X' U')
    (schemeOpenRestriction X U) (Scheme.Modules.tensorPullback j) hj _ _ _ P hb

end AlgebraicGeometry
