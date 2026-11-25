/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SupportedExteriorProductNormalization
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnit

/-!
# Naturality of the resolution pairing of supported sections

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
def-pur-supported-exterior-product.md (blueprint: proposition-purity-vector-bundles).

The pullback and tensor of supported sections, its totalization, the comparison with the
derived exterior product and the support units are natural in the cochain complexes. We
package the right-hand side of the resolution normalization
`IsResolutionSupportedExteriorProduct` as `resolutionSupportedExteriorPairing` and show that
the normalization transfers along quasi-isomorphisms of K-flat representatives.

## Main definitions and statements

- `resolutionSupportedExteriorPairing`: the resolution pairing on two K-flat complexes.
- `resolutionSupportedExteriorPairing_naturality`: its naturality in chain maps.
- `resolutionSupportedExteriorPairing_transfer`: the normalization equation on targets of
  compatible chain maps implies it on the sources.
- `isResolutionSupportedExteriorProduct_iff`: the normalization in terms of the pairing.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

section GlobalSections

variable (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]

/-- The support resolution unit is natural in the cochain complex. -/
@[reassoc]
theorem exteriorSupportResolutionUnit_naturality
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {P P' : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ} (φ : P ⟶ P') :
    DerivedCategory.Q.map (((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).map φ) ≫
        exteriorSupportResolutionUnit C i P' =
      exteriorSupportResolutionUnit C i P ≫
        (rightDerivedSectionsWithSupport C i).map (DerivedCategory.Q.map φ) :=
  (globalSectionsWithSupport C i).rightDerivedFunctorUnitQ_naturality φ

end GlobalSections

section Naturality

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [HasSmallSiteSheafify C]

omit [HasSmallSiteSheafify C] in
/-- The tensor product of two localized chain maps followed by the tensor localization map. -/
@[reassoc]
theorem derivedTensorHom_Q_map_comp_μ {T : Scheme.{u}}
    {P P' Q Q' : CochainComplex (Sheaf T.smallEtaleTopology C) ℤ} (φ : P ⟶ P') (ψ : Q ⟶ Q') :
    derivedTensorHom C (DerivedCategory.Q.map φ) (DerivedCategory.Q.map ψ) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q P' Q' =
      Functor.LaxMonoidal.μ DerivedCategory.Q P Q ≫ DerivedCategory.Q.map (tensorHom φ ψ) := by
  rw [derivedTensorHom]
  exact Functor.LaxMonoidal.μ_natural DerivedCategory.Q φ ψ

variable {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)

omit [HasSmallSiteSheafify C] in
/-- The comparison of the derived exterior product with the ordinary exterior complex is
natural in both cochain complexes. -/
@[reassoc]
theorem exteriorProductResolutionComparison_naturality
    {P P' : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ}
    {Q Q' : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ} (φ : P ⟶ P') (ψ : Q ⟶ Q') :
    derivedTensorHom C
        ((upperStar C (pullback.fst f g)).leftDerivedFunctor.map (DerivedCategory.Q.map φ))
        ((upperStar C (pullback.snd f g)).leftDerivedFunctor.map (DerivedCategory.Q.map ψ)) ≫
      exteriorProductResolutionComparison C f g P' Q' =
    exteriorProductResolutionComparison C f g P Q ≫
      DerivedCategory.Q.map (tensorHom
        (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).map φ)
        (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).map ψ)) := by
  let ε {T : Scheme.{u}} (h : pullback f g ⟶ T) :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv
        (upperStar C h).leftDerivedFunctor ≫
      Functor.whiskerLeft (HomotopyCategory.quotient _ _)
        (upperStar C h).leftDerivedFunctorCounit ≫
      Functor.whiskerRight ((upperStar C h).mapHomotopyCategoryFactors (.up ℤ)).hom
        DerivedCategory.Qh ≫
      Functor.whiskerLeft ((upperStar C h).mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso _).hom
  have h₁ := (ε (pullback.fst f g)).naturality φ
  have h₂ := (ε (pullback.snd f g)).naturality ψ
  dsimp only [ε, Functor.comp_map, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at h₁ h₂
  rw [exteriorProductResolutionComparison, exteriorProductResolutionComparison,
    derivedTensorHom_comp_assoc]
  erw [h₁, h₂]
  rw [← derivedTensorHom_comp_assoc]
  erw [derivedTensorHom_Q_map_comp_μ C
    (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).map φ)
    (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).map ψ)]
  rw [Category.assoc]

/-- The inverse comparison of the derived exterior product is natural on K-flat complexes. -/
@[reassoc]
theorem exteriorProductResolutionIso_inv_naturality
    {P P' : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ}
    {Q Q' : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ} (φ : P ⟶ P') (ψ : Q ⟶ Q')
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hP' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P')
    (hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q)
    (hQ' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q') :
    DerivedCategory.Q.map (tensorHom
        (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).map φ)
        (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).map ψ)) ≫
      (exteriorProductResolutionIso C f g P' Q' hP' hQ').inv =
    (exteriorProductResolutionIso C f g P Q hP hQ).inv ≫
      derivedTensorHom C
        ((upperStar C (pullback.fst f g)).leftDerivedFunctor.map (DerivedCategory.Q.map φ))
        ((upperStar C (pullback.snd f g)).leftDerivedFunctor.map (DerivedCategory.Q.map ψ)) := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (exteriorProductResolutionComparison_naturality C f g φ ψ).symm

variable {Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]

/-- The defining property of the totalized supported pairing. -/
@[reassoc]
theorem ιTensorObj_exteriorSupportedSectionsComplex_f
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ) (r s n : ℤ) (h : r + s = n) :
    HomologicalComplex.ιTensorObj
        (((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).obj P)
        (((globalSectionsWithSupport C j).mapHomologicalComplex (.up ℤ)).obj Q) r s n h ≫
      (exteriorSupportedSectionsComplex C f g i j P Q).f n =
    exteriorSupportedSections C f g i j (P.X r) (Q.X s) ≫
      (globalSectionsWithSupport C (supportedProductImmersion f g i j)).map
        (HomologicalComplex.ιTensorObj
          (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).obj P)
          (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).obj Q)
          r s n h) :=
  (existsUnique_exteriorSupportedSectionsComplex C f g i j P Q).exists.choose_spec r s n h

/-- The totalized supported pairing is natural in both cochain complexes. -/
@[reassoc]
theorem exteriorSupportedSectionsComplex_naturality
    {P P' : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ}
    {Q Q' : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ} (φ : P ⟶ P') (ψ : Q ⟶ Q') :
    tensorHom (((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).map φ)
        (((globalSectionsWithSupport C j).mapHomologicalComplex (.up ℤ)).map ψ) ≫
        exteriorSupportedSectionsComplex C f g i j P' Q' =
      exteriorSupportedSectionsComplex C f g i j P Q ≫
        ((globalSectionsWithSupport C (supportedProductImmersion f g i j)).mapHomologicalComplex
          (.up ℤ)).map
          (tensorHom (((upperStar C (pullback.fst f g)).mapHomologicalComplex (.up ℤ)).map φ)
            (((upperStar C (pullback.snd f g)).mapHomologicalComplex (.up ℤ)).map ψ)) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro r s h
  simp only [HomologicalComplex.comp_f]
  erw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  rw [curriedTensor_map_app, curriedTensor_obj_map, ← tensorHom_def_assoc]
  erw [ιTensorObj_exteriorSupportedSectionsComplex_f C f g i j P' Q' r s n h,
    ιTensorObj_exteriorSupportedSectionsComplex_f_assoc C f g i j P Q r s n h]
  simp only [Functor.mapHomologicalComplex_map_f]
  rw [exteriorSupportedSections_naturality_assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  erw [HomologicalComplex.ι_mapBifunctorMap]
  rw [curriedTensor_map_app, curriedTensor_obj_map, ← tensorHom_def_assoc]
  rfl

/-- The resolution pairing of supported sections on a pair of K-flat complexes: the tensor
localization, the totalized pairing, the support unit of the exterior complex and the
inverse comparison with the derived exterior product. -/
noncomputable def resolutionSupportedExteriorPairing
    (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
    (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q) :
    DerivedCategory.Q.obj (((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).obj P) ⊗
        DerivedCategory.Q.obj
          (((globalSectionsWithSupport C j).mapHomologicalComplex (.up ℤ)).obj Q) ⟶
      (rightDerivedSectionsWithSupport C (supportedProductImmersion f g i j)).obj
        (externalProduct C f g (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)) :=
  Functor.LaxMonoidal.μ DerivedCategory.Q _ _ ≫
    DerivedCategory.Q.map (exteriorSupportedSectionsComplex C f g i j P Q) ≫
    exteriorSupportResolutionUnit C (supportedProductImmersion f g i j)
      (exteriorSectionsComplexTarget C f g P Q) ≫
    (rightDerivedSectionsWithSupport C (supportedProductImmersion f g i j)).map
      (exteriorProductResolutionIso C f g P Q hP hQ).inv

/-- The resolution pairing is natural in both K-flat complexes. -/
@[reassoc]
theorem resolutionSupportedExteriorPairing_naturality
    {P P' : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ}
    {Q Q' : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ} (φ : P ⟶ P') (ψ : Q ⟶ Q')
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hP' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P')
    (hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q)
    (hQ' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q') :
    tensorHom
        (DerivedCategory.Q.map
          (((globalSectionsWithSupport C i).mapHomologicalComplex (.up ℤ)).map φ))
        (DerivedCategory.Q.map
          (((globalSectionsWithSupport C j).mapHomologicalComplex (.up ℤ)).map ψ)) ≫
        resolutionSupportedExteriorPairing C f g i j P' Q' hP' hQ' =
      resolutionSupportedExteriorPairing C f g i j P Q hP hQ ≫
        (rightDerivedSectionsWithSupport C (supportedProductImmersion f g i j)).map
          (derivedTensorHom C
            ((upperStar C (pullback.fst f g)).leftDerivedFunctor.map (DerivedCategory.Q.map φ))
            ((upperStar C (pullback.snd f g)).leftDerivedFunctor.map
              (DerivedCategory.Q.map ψ))) := by
  rw [resolutionSupportedExteriorPairing, resolutionSupportedExteriorPairing,
    Functor.LaxMonoidal.μ_natural_assoc, ← Functor.map_comp_assoc,
    exteriorSupportedSectionsComplex_naturality, Functor.map_comp_assoc]
  erw [exteriorSupportResolutionUnit_naturality_assoc]
  rw [← Functor.map_comp]
  erw [exteriorProductResolutionIso_inv_naturality C f g φ ψ hP hP' hQ hQ']
  simp only [Category.assoc, Functor.map_comp]

/-- On two K-flat representatives which map to two other K-flat representatives by
quasi-isomorphisms compatible with the identifications, the normalization equation on the
targets implies it on the sources. -/
theorem resolutionSupportedExteriorPairing_transfer
    {K : DerivedCategory (Sheaf X.smallEtaleTopology C)}
    {L : DerivedCategory (Sheaf Y.smallEtaleTopology C)}
    {P P' : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ}
    {Q Q' : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ} (φ : P ⟶ P') (ψ : Q ⟶ Q')
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hP' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P')
    (hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q)
    (hQ' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q')
    (eP : DerivedCategory.Q.obj P ⟶ K) (eQ : DerivedCategory.Q.obj Q ⟶ L)
    (eP' : DerivedCategory.Q.obj P' ⟶ K) (eQ' : DerivedCategory.Q.obj Q' ⟶ L)
    (hφ : DerivedCategory.Q.map φ ≫ eP' = eP) (hψ : DerivedCategory.Q.map ψ ≫ eQ' = eQ)
    (κ : (rightDerivedSectionsWithSupport C i).obj K ⊗
        (rightDerivedSectionsWithSupport C j).obj L ⟶
      (rightDerivedSectionsWithSupport C (supportedProductImmersion f g i j)).obj
        (externalProduct C f g K L))
    (h' : tensorHom
        (exteriorSupportResolutionUnit C i P' ≫ (rightDerivedSectionsWithSupport C i).map eP')
        (exteriorSupportResolutionUnit C j Q' ≫ (rightDerivedSectionsWithSupport C j).map eQ') ≫
          κ =
      resolutionSupportedExteriorPairing C f g i j P' Q' hP' hQ' ≫
        (rightDerivedSectionsWithSupport C (supportedProductImmersion f g i j)).map
          (derivedTensorHom C ((upperStar C (pullback.fst f g)).leftDerivedFunctor.map eP')
            ((upperStar C (pullback.snd f g)).leftDerivedFunctor.map eQ'))) :
    tensorHom
        (exteriorSupportResolutionUnit C i P ≫ (rightDerivedSectionsWithSupport C i).map eP)
        (exteriorSupportResolutionUnit C j Q ≫ (rightDerivedSectionsWithSupport C j).map eQ) ≫
          κ =
      resolutionSupportedExteriorPairing C f g i j P Q hP hQ ≫
        (rightDerivedSectionsWithSupport C (supportedProductImmersion f g i j)).map
          (derivedTensorHom C ((upperStar C (pullback.fst f g)).leftDerivedFunctor.map eP)
            ((upperStar C (pullback.snd f g)).leftDerivedFunctor.map eQ)) := by
  subst hφ hψ
  rw [Functor.map_comp, Functor.map_comp, ← exteriorSupportResolutionUnit_naturality_assoc,
    ← exteriorSupportResolutionUnit_naturality_assoc, ← tensorHom_comp_tensorHom_assoc, h',
    resolutionSupportedExteriorPairing_naturality_assoc C f g i j φ ψ hP hP' hQ hQ',
    Functor.map_comp, Functor.map_comp, ← Functor.map_comp, derivedTensorHom_comp]

/-- The resolution normalization in terms of the resolution pairing. -/
theorem isResolutionSupportedExteriorProduct_iff
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology C))
    (κ : (rightDerivedSectionsWithSupport C i).obj K ⊗
        (rightDerivedSectionsWithSupport C j).obj L ⟶
      (rightDerivedSectionsWithSupport C (supportedProductImmersion f g i j)).obj
        (externalProduct C f g K L)) :
    IsResolutionSupportedExteriorProduct C f g i j K L κ ↔
      ∀ (P : CochainComplex (Sheaf X.smallEtaleTopology C) ℤ)
        (Q : CochainComplex (Sheaf Y.smallEtaleTopology C) ℤ)
        (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
        (hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q)
        (eP : DerivedCategory.Q.obj P ≅ K) (eQ : DerivedCategory.Q.obj Q ≅ L),
        tensorHom
            (exteriorSupportResolutionUnit C i P ≫
              (rightDerivedSectionsWithSupport C i).map eP.hom)
            (exteriorSupportResolutionUnit C j Q ≫
              (rightDerivedSectionsWithSupport C j).map eQ.hom) ≫ κ =
          resolutionSupportedExteriorPairing C f g i j P Q hP hQ ≫
            (rightDerivedSectionsWithSupport C (supportedProductImmersion f g i j)).map
              (derivedTensorHom C ((upperStar C (pullback.fst f g)).leftDerivedFunctor.map eP.hom)
                ((upperStar C (pullback.snd f g)).leftDerivedFunctor.map eQ.hom)) := by
  simp only [IsResolutionSupportedExteriorProduct, resolutionSupportedExteriorPairing,
    Functor.map_comp, Category.assoc]

end Naturality

end AlgebraicGeometry.Etale
