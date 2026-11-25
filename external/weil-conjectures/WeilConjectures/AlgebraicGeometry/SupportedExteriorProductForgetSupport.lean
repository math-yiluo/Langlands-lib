/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportedExteriorProductNaturality

/-!
# Forgetting supports in the resolution pairing

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
def-pur-supported-exterior-product.md (blueprint: proposition-purity-vector-bundles).

We totalize the ordinary pullback and tensor of global sections to a chain map
`exteriorSectionsComplex`, and show that the resolution pairing of supported sections
followed by the map forgetting the support of the product is the ordinary pairing of the
included sections followed by the unit of the derived global sections.

## Main definitions and statements

- `exteriorSectionsComplex`: the totalized ordinary pairing of global sections.
- `exteriorSupportedSectionsComplex_comp_ΓSupportι`: the supported pairing followed by the
  inclusion of supported sections.
- `resolutionSupportedExteriorPairing_comp_forgetSupport`: the resolution pairing followed by
  forgetting the support.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

section RightDerived

variable (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]

/-- The unit of the right derived functor followed by the derived natural transformation is
the localized natural transformation followed by the unit. -/
@[reassoc]
theorem rightDerivedFunctorUnit_comp_rightDerivedFunctorNatTrans {T : Scheme.{u}}
    {F G : Sheaf T.smallEtaleTopology C ⥤ C} [F.Additive] [G.Additive] (τ : F ⟶ G)
    (P : CochainComplex (Sheaf T.smallEtaleTopology C) ℤ) :
    F.rightDerivedFunctorUnitQ P ≫
        (Functor.rightDerivedFunctorNatTrans τ).app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app P) ≫
        G.rightDerivedFunctorUnitQ P := by
  simp only [Functor.rightDerivedFunctorUnitQ, Category.assoc]
  rw [(Functor.rightDerivedFunctorNatTrans τ).naturality]
  simp only [Functor.rightDerivedFunctorNatTrans, Functor.rightDerivedNatTrans_app_assoc]
  erw [← DerivedCategory.quotientCompQhIso_inv_naturality_assoc]

/-- The support resolution unit followed by forgetting the support is the localized inclusion
of supported sections followed by the unit of the global sections. -/
@[reassoc]
theorem exteriorSupportResolutionUnit_comp_forgetSupport
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    {K : DerivedCategory (Sheaf X.smallEtaleTopology C)} (e : DerivedCategory.Q.obj P ⟶ K) :
    (exteriorSupportResolutionUnit C i P ≫ (rightDerivedSectionsWithSupport C i).map e) ≫
        (Functor.rightDerivedFunctorNatTrans
          (Sheaf.ΓSupportι X.smallEtaleTopology C
            (op (Scheme.Etale.mk i.openComplement.ι)))).app K =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (Sheaf.ΓSupportι X.smallEtaleTopology C (op (Scheme.Etale.mk i.openComplement.ι)))
          (.up ℤ)).app P) ≫
        (Sheaf.Γ X.smallEtaleTopology C).rightDerivedFunctorUnitQ P ≫
        (Sheaf.Γ X.smallEtaleTopology C).rightDerivedFunctor.map e := by
  have hnat := (Functor.rightDerivedFunctorNatTrans
    (Sheaf.ΓSupportι X.smallEtaleTopology C
      (op (Scheme.Etale.mk i.openComplement.ι)))).naturality e
  rw [Category.assoc]
  erw [hnat]
  erw [rightDerivedFunctorUnit_comp_rightDerivedFunctorNatTrans_assoc]

end RightDerived

section Ordinary

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [HasSmallSiteSheafify C]

variable {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)

/-- Naturality of the pullback and tensor of sections in the first sheaf. -/
@[reassoc]
theorem exteriorSectionsMap_naturality_left
    {F F' : Sheaf X.smallEtaleTopology C} (a : F ⟶ F') (G : Sheaf Y.smallEtaleTopology C) :
    (Sheaf.Γ X.smallEtaleTopology C).map a ▷ (Sheaf.Γ Y.smallEtaleTopology C).obj G ≫
        exteriorSectionsMap C f g F' G =
      exteriorSectionsMap C f g F G ≫ (Sheaf.Γ (pullback f g).smallEtaleTopology C).map
        ((upperStar C (pullback.fst f g)).map a ▷ (upperStar C (pullback.snd f g)).obj G) := by
  simpa using exteriorSectionsMap_naturality C f g a (𝟙 G)

/-- Naturality of the pullback and tensor of sections in the second sheaf. -/
@[reassoc]
theorem exteriorSectionsMap_naturality_right
    (F : Sheaf X.smallEtaleTopology C) {G G' : Sheaf Y.smallEtaleTopology C} (b : G ⟶ G') :
    (Sheaf.Γ X.smallEtaleTopology C).obj F ◁ (Sheaf.Γ Y.smallEtaleTopology C).map b ≫
        exteriorSectionsMap C f g F G' =
      exteriorSectionsMap C f g F G ≫ (Sheaf.Γ (pullback f g).smallEtaleTopology C).map
        ((upperStar C (pullback.fst f g)).obj F ◁ (upperStar C (pullback.snd f g)).map b) := by
  simpa using exteriorSectionsMap_naturality C f g (𝟙 F) b

/-- The totalized ordinary pairing of sections: in bidegree `(r, s)` it is the pullback and
tensor of sections followed by the inclusion of that bidegree in the exterior complex. -/
noncomputable def exteriorSectionsComplex
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ) :
    ((Sheaf.Γ X.smallEtaleTopology C).mapHomologicalComplex (.up ℤ)).obj P ⊗
        ((Sheaf.Γ Y.smallEtaleTopology C).mapHomologicalComplex (.up ℤ)).obj Q ⟶
      ((Sheaf.Γ (pullback f g).smallEtaleTopology C).mapHomologicalComplex (.up ℤ)).obj
        (exteriorSectionsComplexTarget C f g P Q) where
  f n := HomologicalComplex.mapBifunctorDesc
    (K₁ := ((Sheaf.Γ X.smallEtaleTopology C).mapHomologicalComplex (.up ℤ)).obj P)
    (K₂ := ((Sheaf.Γ Y.smallEtaleTopology C).mapHomologicalComplex (.up ℤ)).obj Q)
    (F := curriedTensor C) (c := .up ℤ) (j := n) (fun r s h ↦
      exteriorSectionsMap C f g (P.X r) (Q.X s) ≫
        (Sheaf.Γ (pullback f g).smallEtaleTopology C).map
          (HomologicalComplex.ιTensorObj
            (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).obj P)
            (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).obj Q) r s n h))
  comm' n n' hnn' := by
    obtain rfl : n + 1 = n' := hnn'
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro r s h
    have h₁ : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (r + 1, s) = n + 1 := by
      have := h
      dsimp at this ⊢
      omega
    have h₂ : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (r, s + 1) = n + 1 := by
      have := h
      dsimp at this ⊢
      omega
    have hr : (ComplexShape.up ℤ).Rel r (r + 1) := rfl
    have hs : (ComplexShape.up ℤ).Rel s (s + 1) := rfl
    erw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
    erw [HomologicalComplex.mapBifunctor.d_eq]
    rw [Preadditive.add_comp, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hr _ _ h₁,
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ hs _ h₂]
    simp only [Units.smul_def, Preadditive.zsmul_comp, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc, Functor.mapHomologicalComplex_obj_d,
      ← Functor.map_comp]
    erw [HomologicalComplex.mapBifunctor.d_eq]
    rw [Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
      HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hr _ _ h₁,
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ hs _ h₂]
    simp only [Units.smul_def, Functor.map_add, Functor.map_zsmul, Preadditive.comp_add,
      Preadditive.comp_zsmul, Functor.map_comp]
    simp only [curriedTensor_map_app, curriedTensor_obj_map,
      Functor.mapHomologicalComplex_obj_d]
    erw [exteriorSectionsMap_naturality_left_assoc, exteriorSectionsMap_naturality_right_assoc]
    rfl

/-- The defining property of the totalized ordinary pairing. -/
@[reassoc]
theorem ιTensorObj_exteriorSectionsComplex_f
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ) (r s n : ℤ) (h : r + s = n) :
    HomologicalComplex.ιTensorObj
        (((Sheaf.Γ X.smallEtaleTopology C).mapHomologicalComplex (.up ℤ)).obj P)
        (((Sheaf.Γ Y.smallEtaleTopology C).mapHomologicalComplex (.up ℤ)).obj Q) r s n h ≫
      (exteriorSectionsComplex C f g P Q).f n =
    exteriorSectionsMap C f g (P.X r) (Q.X s) ≫
      (Sheaf.Γ (pullback f g).smallEtaleTopology C).map
        (HomologicalComplex.ιTensorObj
          (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).obj P)
          (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).obj Q) r s n h) := by
  dsimp only [exteriorSectionsComplex]
  exact HomologicalComplex.ι_mapBifunctorDesc _ _ _ _

variable {Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]

/-- The totalized supported pairing followed by the inclusion of supported sections is the
ordinary pairing after the inclusions of supported sections. -/
theorem exteriorSupportedSectionsComplex_comp_ΓSupportι
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ) :
    exteriorSupportedSectionsComplex C f g i j P Q ≫
        (NatTrans.mapHomologicalComplex
          (Sheaf.ΓSupportι (pullback f g).smallEtaleTopology C
            (op (Scheme.Etale.mk (supportedProductImmersion f g i j).openComplement.ι)))
          (.up ℤ)).app (exteriorSectionsComplexTarget C f g P Q) =
      tensorHom
        ((NatTrans.mapHomologicalComplex
          (Sheaf.ΓSupportι X.smallEtaleTopology C (op (Scheme.Etale.mk i.openComplement.ι)))
          (.up ℤ)).app P)
        ((NatTrans.mapHomologicalComplex
          (Sheaf.ΓSupportι Y.smallEtaleTopology C (op (Scheme.Etale.mk j.openComplement.ι)))
          (.up ℤ)).app Q) ≫
        exteriorSectionsComplex C f g P Q := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro r s h
  simp only [HomologicalComplex.comp_f]
  erw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  rw [curriedTensor_map_app, curriedTensor_obj_map, ← tensorHom_def_assoc]
  erw [ιTensorObj_exteriorSupportedSectionsComplex_f_assoc C f g i j P Q r s n h,
    ιTensorObj_exteriorSectionsComplex_f C f g P Q r s n h]
  simp only [NatTrans.mapHomologicalComplex_app_f]
  erw [(Sheaf.ΓSupportι (pullback f g).smallEtaleTopology C
    (op (Scheme.Etale.mk (supportedProductImmersion f g i j).openComplement.ι))).naturality]
  rw [exteriorSupportedSections_ΓSupportι_assoc]

/-- The resolution pairing followed by forgetting the support of the product is the ordinary
pairing of the included sections followed by the unit of the global sections. -/
@[reassoc]
theorem resolutionSupportedExteriorPairing_comp_forgetSupport
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q)
    {M : DerivedCategory (Sheaf (pullback f g).smallEtaleTopology C)}
    (x : externalProduct C f g (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ⟶ M) :
    resolutionSupportedExteriorPairing C f g i j P Q hP hQ ≫
        (rightDerivedSectionsWithSupport C (supportedProductImmersion f g i j)).map x ≫
        (Functor.rightDerivedFunctorNatTrans
          (Sheaf.ΓSupportι (pullback f g).smallEtaleTopology C
            (op (Scheme.Etale.mk (supportedProductImmersion f g i j).openComplement.ι)))).app M =
      tensorHom
          (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (Sheaf.ΓSupportι X.smallEtaleTopology C (op (Scheme.Etale.mk i.openComplement.ι)))
            (.up ℤ)).app P))
          (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (Sheaf.ΓSupportι Y.smallEtaleTopology C (op (Scheme.Etale.mk j.openComplement.ι)))
            (.up ℤ)).app Q)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q _ _ ≫
        DerivedCategory.Q.map (exteriorSectionsComplex C f g P Q) ≫
        (Sheaf.Γ (pullback f g).smallEtaleTopology C).rightDerivedFunctorUnitQ
          (exteriorSectionsComplexTarget C f g P Q) ≫
        (Sheaf.Γ (pullback f g).smallEtaleTopology C).rightDerivedFunctor.map
          ((exteriorProductResolutionIso C f g P Q hP hQ).inv ≫ x) := by
  have hnat := (Functor.rightDerivedFunctorNatTrans
    (Sheaf.ΓSupportι (pullback f g).smallEtaleTopology C
      (op (Scheme.Etale.mk (supportedProductImmersion f g i j).openComplement.ι)))).naturality
    ((exteriorProductResolutionIso C f g P Q hP hQ).inv ≫ x)
  rw [resolutionSupportedExteriorPairing]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  erw [hnat]
  erw [rightDerivedFunctorUnit_comp_rightDerivedFunctorNatTrans_assoc]
  rw [← Functor.map_comp_assoc, exteriorSupportedSectionsComplex_comp_ΓSupportι, Functor.map_comp,
    Category.assoc]
  erw [← Functor.LaxMonoidal.μ_natural_assoc]

end Ordinary

end AlgebraicGeometry.Etale
