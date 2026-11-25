/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Etale.ProperEtaleOriginScalarData
import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginScalarPullbackSquare

/-! # Scalar restriction of the etale-origin projection square

Source: Stacks Project, Tags 0E48 and 0B56. This is a compatibility of specified
maps for a qcqs morphism; it does not assert a projection formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Etale.scalarTensorIso Scheme.completedAdicDerivedChange
attribute [local implicit_reducible] properOriginEtaleTensor
  Scheme.proEtaleConstantRingComparison

private theorem scalar_restriction_counit
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (N : Scheme.proEtaleDerivedCategory Z B) :
    (Scheme.proEtaleConstantRingDerivedPullback A p).map
        ((scalarMateRestrictionPush φ p).hom.app N) ≫
      (directImageConstantAdjunction A p).counit.app
        ((scalarMateRestriction φ Z).mapDerivedCategory.obj N) =
    (originRestrictionPullback φ p).app ((directImageConstantPush B p).obj N) ≫
      (scalarMateRestriction φ Z).mapDerivedCategory.map
        ((directImageConstantAdjunction B p).counit.app N) := by
  let adjA := directImageConstantAdjunction A p
  let adjB := directImageConstantAdjunction B p
  have h := (Scheme.proEtaleRingSheafChangeAdjunction p
    (Scheme.proEtaleConstantRing Y A) (Scheme.proEtaleConstantRing Y B)
    (Scheme.proEtaleConstantRing Z A) (Scheme.proEtaleConstantRing Z B)
    (Scheme.proEtaleConstantRingMap (T := Y) φ)
    (Scheme.proEtaleConstantRingMap (T := Z) φ)
    (Scheme.proEtaleConstantRingComparison p A) (Scheme.proEtaleConstantRingComparison p B)
    (Scheme.proEtaleConstantInverseImageMap_naturality p
      (CommRingCat.ofHom (RingHom.ulift φ))).symm).2.2
      ((directImageConstantPush B p).obj N) N (adjB.counit.app N)
  have hid : adjB.homEquiv _ _ (adjB.counit.app N) = 𝟙 _ := by
    rw [← adjB.homEquiv_symm_id N]
    exact (adjB.homEquiv _ N).apply_symm_apply _
  change adjA.homEquiv _ _ (_ ≫ _) =
    (scalarMateRestriction φ Y).mapDerivedCategory.map
      (adjB.homEquiv _ _ (adjB.counit.app N)) ≫
      (scalarMateRestrictionPush φ p).hom.app N at h
  rw [hid, CategoryTheory.Functor.map_id, Category.id_comp] at h
  have h' := congrArg (adjA.homEquiv _ _).symm h
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit] at h'
  exact h'.symm

private theorem scalar_counit
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (M : Scheme.proEtaleDerivedCategory Z A) :
    (Scheme.proEtaleConstantRingDerivedPullback A p).map
        ((scalarMateRestriction φ Y).mapDerivedCategory.map
          ((directImageScalarComparison φ p).app M) ≫
          (scalarMateRestrictionPush φ p).hom.app ((directImageScalarExtension φ Z).obj M)) ≫
      (directImageConstantAdjunction A p).counit.app
        ((directImageScalarExtension φ Z ⋙
          (scalarMateRestriction φ Z).mapDerivedCategory).obj M) =
    (originScalarPullback φ p).app ((directImageConstantPush A p).obj M) ≫
      (directImageScalarExtension φ Z ⋙ (scalarMateRestriction φ Z).mapDerivedCategory).map
        ((directImageConstantAdjunction A p).counit.app M) := by
  let U := (scalarMateRestriction φ Z).mapDerivedCategory
  have h := mateEquiv_counit (directImageConstantAdjunction A p)
    (directImageConstantAdjunction B p) (directImageScalarPullbackIso φ p).hom M
  change (Scheme.proEtaleConstantRingDerivedPullback B p).map
      ((directImageScalarComparison φ p).app M) ≫
    (directImageConstantAdjunction B p).counit.app
      ((directImageScalarExtension φ Z).obj M) = _ at h
  have hn := (originRestrictionPullback φ p).naturality
    ((directImageScalarComparison φ p).app M)
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Functor.comp_obj, Category.assoc]
  rw [scalar_restriction_counit]
  rw [← Category.assoc]
  erw [hn]
  simp only [Category.assoc]
  rw [← U.map_comp]
  erw [h]
  rw [U.map_comp]
  simp only [originScalarPullback, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Functor.comp_map, Category.assoc]
  rfl

private theorem etale_projection_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (K : Etale.DerivedCategoryModule A Z) :
    (Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.map
        (properOriginEtaleProjection φ p K) ≫
      (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).counit.app
        (properOriginEtaleTensor φ Z K) =
    (originEtaleTensorPullback φ p).app
        ((Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.obj K) ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} A) Z).flip.obj
        (Etale.scalarCoefficient φ Z)).map
          ((Etale.derivedUpperStarLowerStarAdjunction
            (ModuleCat.{u + 1} A) p).counit.app K) := by
  let adj := Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p
  let T := Etale.derivedTensor (ModuleCat.{u + 1} A) Z
  have hn := (T.map (adj.counit.app K)).naturality (Etale.scalarCoefficientPullbackIso φ p).hom
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn
  change (adj.homEquiv _ _).symm (properOriginEtaleProjection φ p K) = _
  rw [properOriginEtaleProjection, adj.homEquiv_naturality_right_symm]
  erw [Etale.homEquiv_symm_rightDerivedLowerStarProjectionMap]
  simp only [originEtaleTensorPullback, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.flip_map_app, Functor.flip_obj_map,
    Etale.derivedTensorRightCompLeftDerivedUpperStarIso, NatIso.ofComponents_hom_app,
    Etale.leftDerivedUpperStarTensorIso_hom, Category.assoc]
  rw [← hn]

/-- The etale projection and the restricted scalar mate give the same square
through the canonical tensor comparisons and the bounded-below direct-image mates.
The morphism is only required to be qcqs. In particular, this statement neither
uses properness nor claims that either projection morphism is invertible.

Source: Stacks Project, sites-cohomology.tex, Tag 0E48,
remark-compatible-with-diagram, and Tag 0B56, equation-projection-formula-map;
proetale.tex, Tag 09A6.
(blueprint: lem-fix-etale-origin-scalar-projection-square).

Proof: identify the two bounded-below included mates with the ambient site
mate. Transpose the square under the A-geometric adjunction. The ring-sheaf
restriction counit formula and the scalar-extension mate counit formula compute
the scalar side. Naturality and the local scalar/tensor pullback square identify
its initial factors. Tensor-comparison naturality moves the etale geometric
counit to the other side. The ambient site-mate counit identity and the counit
formula for the actual etale projection identify the remaining factors.
Injectivity of the adjunction Hom equivalence gives the displayed square.
The local pullback square is assembled from the separate tensor-free restriction
and extension realization cubes and the proved etale scalar/tensor pullback square.
The bounds on E and H are used only for the two included-mate identifications;
no bound is imposed on scalar extension of the target direct image.
-/
theorem etaleOriginScalarProjectionSquare
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    [QuasiCompact p] [QuasiSeparated p]
    (E : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hH : ∃ n : ℤ,
      (properOriginEtaleTensor (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z E.obj).IsGE n) :
    (properOriginTensorIso φ Y
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj
          E.obj)).hom ≫
      (directImageScalarExtension φ Y ⋙ (scalarMateRestriction φ Y).mapDerivedCategory).map
        (properOriginMateIso A p E).hom ≫
      (scalarMateRestriction φ Y).mapDerivedCategory.map
        ((directImageScalarComparison φ p).app
          ((finiteCoefficientIntrinsicDerivedComparison Z A).obj E.obj)) ≫
      (scalarMateRestrictionPush φ p).hom.app
        ((directImageScalarExtension φ Z).obj
          ((finiteCoefficientIntrinsicDerivedComparison Z A).obj E.obj)) =
    (finiteCoefficientIntrinsicDerivedComparison Y A).map
        (properOriginEtaleProjection (RingHom.ulift.{u + 1, u + 1, u, u} φ) p E.obj) ≫
      (properOriginMateIso A p
        ⟨properOriginEtaleTensor (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z E.obj, hH⟩).hom ≫
      (directImageConstantPush A p).map (properOriginTensorIso φ Z E.obj).hom := by
  let G := finiteCoefficientIntrinsicDerivedComparison Z A
  let L := Scheme.proEtaleConstantRingDerivedPullback A p
  let S := directImageScalarExtension φ Y ⋙ (scalarMateRestriction φ Y).mapDerivedCategory
  let T := directImageScalarExtension φ Z ⋙ (scalarMateRestriction φ Z).mapDerivedCategory
  let Re := (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor
  let adj := directImageConstantAdjunction A p
  let adje := Etale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p
  let H := properOriginEtaleTensor (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z E.obj
  have hE := originMate_app A p E
  have hH' := originMate_app A p ⟨H, hH⟩
  rw [← hE, ← hH']
  apply (adj.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hs := scalar_counit φ p (G.obj E.obj)
  simp only [Functor.map_comp, Category.assoc] at hs
  change L.map (properOriginTensorIso φ Y (Re.obj E.obj)).hom ≫
    L.map (S.map ((originMate A p).app E.obj)) ≫ _ = _
  erw [hs]
  have hn := (originScalarPullback φ p).naturality ((originMate A p).app E.obj)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  change L.map (properOriginTensorIso φ Y (Re.obj E.obj)).hom ≫
    (originScalarPullback φ p).app
      ((finiteCoefficientIntrinsicDerivedComparison Y A).obj (Re.obj E.obj)) ≫
    T.map (L.map ((originMate A p).app E.obj)) ≫
    T.map (adj.counit.app (G.obj E.obj)) = _
  rw [← T.map_comp]
  erw [originMate_counit]
  rw [T.map_comp]
  have hsq := etaleOriginScalarPullbackSquare φ p (Re.obj E.obj)
  erw [reassoc_of% hsq]
  have hq := (originTensorComparison φ Z).hom.naturality (adje.counit.app E.obj)
  simp only [Functor.comp_map, originTensorComparison_hom_app] at hq
  erw [← hq]
  have hb := originMate_counit A p H
  have ha := (originPullback A p).naturality
    (properOriginEtaleProjection (RingHom.ulift.{u + 1, u + 1, u, u} φ) p E.obj)
  dsimp only [Functor.comp_map] at ha
  have hp := etale_projection_counit (RingHom.ulift.{u + 1, u + 1, u, u} φ) p E.obj
  erw [adj.counit.naturality]
  erw [reassoc_of% hb]
  erw [reassoc_of% ha]
  have hp' := congrArg (fun f ↦ G.map f) hp
  simp only [Functor.map_comp] at hp'
  erw [reassoc_of% hp']
  rfl

end AlgebraicGeometry.ProEtale
