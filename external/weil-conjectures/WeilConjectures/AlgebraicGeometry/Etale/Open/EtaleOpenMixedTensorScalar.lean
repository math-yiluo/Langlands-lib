/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenScalarRestrictionTensor
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate

/-! # Scalar extension intertwines the exact open projection map and the scalar tensor maps. -/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale

attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit Functor.mapDerivedCategory
  derivedTensor
attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
  cachedEtaleMonoidalPreadditive cachedEtaleCoproducts cachedEtaleColimits
  cachedEtaleFlatResolution cachedEtaleInjectiveResolution cachedEtaleExactColimits
  cachedEtaleTensor4 cachedEtaleTensor12 cachedEtaleTensor23
  cachedEtaleTensorColimits cachedEtaleTensorFlipColimits

open MonoidalCategory
open scoped CategoryTheory.Functor

private def binaryTensorIso
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D) (F : C ⥤ D)
    (μ : ∀ K M, (S.obj (F.obj K)).obj (F.obj M) ≅ F.obj ((T.obj K).obj M))
    (h₁ : ∀ {K K'} (f : K ⟶ K') M,
      (S.map (F.map f)).app (F.obj M) ≫ (μ K' M).hom =
        (μ K M).hom ≫ F.map ((T.map f).app M))
    (h₂ : ∀ K {M M'} (f : M ⟶ M'),
      (S.obj (F.obj K)).map (F.map f) ≫ (μ K M').hom =
        (μ K M).hom ≫ F.map ((T.obj K).map f)) :
    (((Functor.whiskeringLeft₂ _).obj F).obj F).obj S ≅
      (Functor.postcompose₂.obj F).obj T :=
  NatIso.ofComponents (fun K ↦ NatIso.ofComponents (μ K) (h₂ K))
    (fun f ↦ NatTrans.ext (funext fun M ↦ h₁ f M))

private noncomputable def scalarTensorBifunctorIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :=
  binaryTensorIso (derivedTensor (ModuleCat.{u + 1} A) X)
    (derivedTensor (ModuleCat.{u + 1} B) X) (scalarExtension φ X)
    (etaleHomTensorComparison X φ)
    (etaleHomTensorComparison_existsUnique X φ).choose_spec.1.1
    (etaleHomTensorComparison_existsUnique X φ).choose_spec.1.2.1

private theorem inverseMate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {JA : D ⥤ C} {LB : E ⥤ F} {JB : F ⥤ E}
    {SX : D ⥤ F} {RX : F ⥤ D} {SU : C ⥤ E} {RU : E ⥤ C}
    (a : LA ⊣ JA) (b : LB ⊣ JB) (x : SX ⊣ RX) (v : SU ⊣ RU)
    (q : JB ⋙ RU ≅ RX ⋙ JA) :
    ((mateEquiv a b).symm
      ((mateEquiv x v).symm (TwoSquare.mk _ _ _ _ q.inv))) =
      ((a.comp x).leftAdjointUniq ((v.comp b).ofNatIsoRight q)).inv := by
  have h : (a.comp x).leftAdjointUniq ((v.comp b).ofNatIsoRight q) =
      (conjugateIsoEquiv (v.comp b) (a.comp x)).symm q := by
    ext K
    simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app]
  rw [h]
  exact
    (iterated_mateEquiv_conjugateEquiv_symm a b v x (TwoSquare.mk _ _ _ _ q.inv))

private theorem scalar_open_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P : DerivedCategoryModule A U) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) j).unit.app ((scalarExtension φ U).obj P) ≫
      (derivedRestriction (A := B) j).map ((openScalarExtension φ j).inv.app P) =
    (scalarExtension φ U).map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).unit.app P) ≫
      (openScalarRestriction φ j).hom.app ((derivedExtension (A := A) j).obj P) := by
  let a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let b := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let v := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let α := (mateEquiv x v).symm
    (TwoSquare.mk _ _ _ _ (openDerivedRestrictScalarsIso φ j).inv)
  have h := unit_mateEquiv_symm a b α P
  have hm := inverseMate a b x v (openDerivedRestrictScalarsIso φ j)
  change _ = b.unit.app _ ≫ (derivedRestriction (A := B) j).map
    (((mateEquiv a b).symm α).app P) at h
  rw [hm] at h
  exact h.symm

private noncomputable def exactRestrictionTensorIso
    {A : Type (u + 1)} [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    (((Functor.whiskeringLeft₂ _).obj (derivedRestriction (A := A) j)).obj
      (derivedRestriction (A := A) j)).obj (derivedTensor (ModuleCat.{u + 1} A) U) ≅
    (Functor.postcompose₂.obj (derivedRestriction (A := A) j)).obj
      (derivedTensor (ModuleCat.{u + 1} A) X) :=
  (((Functor.whiskeringLeft₂ _).obj (derivedRestriction (A := A) j)).mapIso
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm).app
        (derivedTensor (ModuleCat.{u + 1} A) U) ≪≫
    mapDerivedCategoryUpperStarDerivedTensorIso (ModuleCat.{u + 1} A) j

private theorem projection_transport
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G S : D ⥤ C} (a : F ⊣ G) (e : S ≅ G)
    (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    (δ : (((Functor.whiskeringLeft₂ C).obj G).obj S).obj T ⟶
      (Functor.postcompose₂.obj G).obj T')
    (K : C) (M : D) :
    F.map ((T.obj K).map (e.inv.app M)) ≫
        ((a.projectionMap S T T' δ).app K).app M =
      ((a.projectionMap G T T'
        ((((Functor.whiskeringLeft₂ C).obj G).map e.inv).app T ≫ δ)).app K).app M := by
  rw [Adjunction.projectionMap_app_app, Adjunction.projectionMap_app_app,
    Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, ← Functor.map_comp_assoc]
  congr 2
  exact ((T.map (a.unit.app K)).naturality_assoc (e.inv.app M) _)

private theorem exact_projection
    {A : Type (u + 1)} [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategoryModule A U) (M : DerivedCategoryModule A X) :
    canonicalGammaExact (ModuleCat.{u + 1} A) j K M =
      ((Adjunction.projectionMap
        (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
        (derivedRestriction (A := A) j) (derivedTensor (ModuleCat.{u + 1} A) U)
          (derivedTensor (ModuleCat.{u + 1} A) X)
          (exactRestrictionTensorIso j).hom).app K).app M := by
  exact projection_transport
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j)
    (derivedTensor (ModuleCat.{u + 1} A) U) (derivedTensor (ModuleCat.{u + 1} A) X)
    (mapDerivedCategoryUpperStarDerivedTensorIso (ModuleCat.{u + 1} A) j).hom K M

/-- Scalar extension intertwines the exact open projection map and the scalar tensor maps.
Source: Stacks Tags 0E8I, 03EL, 06YY and 0E8J; parent proof step 3,
the mixed scalar/tensor compatibility assertion.

Proof: The ordinary scalar/restriction comparison is the mate of the sectionwise
commutation of restriction of coefficients with direct image. This sectionwise
map is monoidal; the conjugate is therefore monoidal for the canonical scalar
oplax tensorators. Apply the ordinary equation degreewise and take signed
direct-sum totalizations. On complexes with flat terms that are K-flat, the
scalar representative maps and the localization tensorator are invertible.
The normalization of the scalar tensor comparison transports the ordinary
monoidal square to the derived restriction square. Every derived object has
a flat K-flat representative; naturality and cancellation extend this square
to all objects in both variables. Finally transpose under the two exact open
adjunctions. The unit identity for q and the definition of r as its scalar
mate identify the transposed maps. The general projection-map mate identity
then gives the displayed mixed projection square. Cancel the invertible q,
r and tensor comparison factors to obtain the stated orientation. All tensor
products are derived using unbounded flat K-flat representatives; neither a
flat coefficient homomorphism nor a quasi-compact open immersion is needed.
The unit identities also cover the empty scheme and the zero coefficient ring.
(blueprint: lem-coef-etale-open-mixed-tensor-scalar). -/
theorem etaleOpenMixedTensorScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ∀ (P : DerivedCategoryModule A U) (T : DerivedCategoryModule A X),
    canonicalGammaExact (ModuleCat.{u + 1} B) j
        ((scalarExtension φ U).obj P) ((scalarExtension φ X).obj T) ≫
        ((derivedTensor (ModuleCat.{u + 1} B) X).map
          ((openScalarExtension φ j).inv.app P)).app ((scalarExtension φ X).obj T) ≫
        (etaleHomTensorComparison X φ ((derivedExtension (A := A) j).obj P) T).hom =
      (derivedExtension (A := B) j).map
          (((derivedTensor (ModuleCat.{u + 1} B) U).obj ((scalarExtension φ U).obj P)).map
              ((openScalarRestriction φ j).inv.app T) ≫
            (etaleHomTensorComparison U φ P ((derivedRestriction j).obj T)).hom) ≫
        (openScalarExtension φ j).inv.app
          (((derivedTensor (ModuleCat.{u + 1} A) U).obj P).obj ((derivedRestriction j).obj T)) ≫
        (scalarExtension φ X).map (canonicalGammaExact (ModuleCat.{u + 1} A) j P T)  := by
  intro P T
  have hδ (K M : DerivedCategoryModule A X) := etaleOpenScalarRestrictionTensor φ j K M
  have h := Adjunction.projectionMap_mate
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (derivedRestriction (A := A) j) (derivedRestriction (A := B) j)
    (exactRestrictionTensorIso (A := A) j).hom
    (exactRestrictionTensorIso (A := B) j).hom
    (scalarTensorBifunctorIso φ U).inv (scalarTensorBifunctorIso φ X).inv
    (openScalarRestriction φ j).hom (openScalarRestriction φ j).hom
    (openScalarExtension φ j).inv (scalar_open_unit φ j) hδ P T
  simp only [← exact_projection] at h
  change (openScalarExtension φ j).inv.app _ ≫
      (scalarExtension φ X).map (canonicalGammaExact (ModuleCat.{u + 1} A) j P T) ≫
      (etaleHomTensorComparison X φ ((derivedExtension (A := A) j).obj P) T).inv =
    (derivedExtension (A := B) j).map
        (etaleHomTensorComparison U φ P ((derivedRestriction (A := A) j).obj T)).inv ≫
      (derivedExtension (A := B) j).map
        (((derivedTensor (ModuleCat.{u + 1} B) U).obj ((scalarExtension φ U).obj P)).map
          ((openScalarRestriction φ j).hom.app T)) ≫
      canonicalGammaExact (ModuleCat.{u + 1} B) j
        ((scalarExtension φ U).obj P) ((scalarExtension φ X).obj T) ≫
      ((derivedTensor (ModuleCat.{u + 1} B) X).map
        ((openScalarExtension φ j).inv.app P)).app ((scalarExtension φ X).obj T) at h
  have hi : (derivedExtension (A := B) j).map
      ((((derivedTensor (ModuleCat.{u + 1} B) U).obj ((scalarExtension φ U).obj P)).map
        ((openScalarRestriction φ j).inv.app T)) ≫
      (etaleHomTensorComparison U φ P ((derivedRestriction (A := A) j).obj T)).hom) ≫
      (derivedExtension (A := B) j).map
        (etaleHomTensorComparison U φ P ((derivedRestriction (A := A) j).obj T)).inv ≫
      (derivedExtension (A := B) j).map
        (((derivedTensor (ModuleCat.{u + 1} B) U).obj ((scalarExtension φ U).obj P)).map
          ((openScalarRestriction φ j).hom.app T)) = 𝟙 _ := by
    simp only [← Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id_app]
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  have hh := congrArg (fun f ↦
    (derivedExtension (A := B) j).map
      ((((derivedTensor (ModuleCat.{u + 1} B) U).obj ((scalarExtension φ U).obj P)).map
        ((openScalarRestriction φ j).inv.app T)) ≫
      (etaleHomTensorComparison U φ P ((derivedRestriction (A := A) j).obj T)).hom) ≫
    f ≫ (etaleHomTensorComparison X φ ((derivedExtension (A := A) j).obj P) T).hom) h
  simpa only [Category.assoc, reassoc_of% hi, Category.id_comp,
    Iso.inv_hom_id, Category.comp_id] using hh.symm

end AlgebraicGeometry.Etale
