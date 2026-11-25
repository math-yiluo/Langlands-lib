/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarTensorOrdinaryPullback
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # One-sided tensor coordinates and geometric pullback

Source: Stacks Project, Tags 03EK, 06YY, 07A4 and 07A6.
(blueprint: lem-sfb-scalar-tensor-one-sided-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.DerivedScalarMate

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
  proEtaleRingModulePullback proEtaleRingDerivedPullbackFactors
  SheafOfModules.monoidalCategory
  proEtaleTensorPullbackTotalIso HomologicalComplex₂.total
  Functor.mapBifunctorHomologicalComplex
attribute [local implicit_reducible] Functor.map₂HomologicalComplex

private theorem uncurry_map_id_left {C D E : Type*}
    [Category C] [Category D] [Category E] (F : C ⥤ D ⥤ E)
    (X : C) {Y Y' : D} (v : Y ⟶ Y') :
    (Functor.uncurry.obj F).map (Prod.mkHom (𝟙 X) v) = (F.obj X).map v := by
  change (F.map (𝟙 X)).app Y ≫ (F.obj X).map v = _
  rw [F.map_id, NatTrans.id_app, Category.id_comp]

private theorem coordinates_normalization {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : A ⟶ B)
    (t : ProEtaleTensorModel W A) (P Q : CochainComplex (proEtaleRingModules W A) ℤ)
    (hp : proEtaleFlatRepresentatives W A P) (hq : proEtaleFlatRepresentatives W A Q)
    (q : Q ⟶ coefficientComplex a) (h : QuasiIso q) :
    t.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
      t.tensor.map (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map q)) ≫
      tensorScalarCoordinates a t P =
    DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 P) q
      (proEtaleOrdinaryTensor W A) (.up ℤ)) := by
  have ht : IsDerivedTensor a t (derivedTensorIso a t) :=
    Classical.choose_spec (derivedTensorIso_existsUnique a t).exists
  have hn := ht P Q hp hq q h
  with_unfolding_all
    change t.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
      t.tensor.map (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map q)) ≫
      (derivedTensorIso a t).inv.app (DerivedCategory.Q.obj P) ≫ tensorScalarCounit a P =
      DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 P) q
        (proEtaleOrdinaryTensor W A) (.up ℤ) ≫ (ordinaryComplexIso a P).inv) at hn
  have hh := congrArg (fun g ↦ g ≫ DerivedCategory.Q.map (ordinaryComplexIso a P).hom) hn
  simpa only [tensorScalarCoordinates, Category.assoc,
    Functor.map_comp, Iso.inv_hom_id_map, Category.comp_id,
    Functor.comp_obj, Functor.prod_obj, ObjectProperty.ι_obj] using hh

/-- Pullback of the one-sided tensor coordinates is the localized ordinary tensor map.
This assertion contains no scalar/pullback mate.

Source: Stacks 06YY, 07A4, 07A6, the resolving calculation for the tensor route
(blueprint: lem-sfb-scalar-tensor-one-sided-pullback).

Proof: resolve the coefficient complex by q:Q→B[0] with Q flat-term K-flat.
Pullback preserves both resolving conditions. Apply IsDerivedTensor at P,Q and
at their pullbacks, using pullback(q) followed by the coefficient complex
identification as the latter augmentation. Insert the representative square
of the canonical tensor pullback. Naturality moves q through that square;
naturality of the ordinary total comparison moves its cochain map. The two
IsDerivedTensor equations cancel the ordinary scalar identifications. Cancel
the localized resolution q and the representative isomorphisms. This works
for nonflat B, since only P needs to be K-flat for the one-sided coordinates.
The coefficient complex is concentrated in degree zero, so no new sign occurs. -/
theorem tensorScalar_oneSided_pullback
    {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (t : ProEtaleTensorModel T A) (z : ProEtaleTensorModel Z (inverseRing f A))
    (P : CochainComplex (proEtaleRingModules T A) ℤ)
    (hp : proEtaleFlatRepresentatives T A P) :
    (pull f A).map ((derivedTensorIso a t).hom.app (DerivedCategory.Q.obj P)) ≫
      (proEtaleCanonicalTensorComparison f A (inverseRing f A) (Iso.refl _) t z).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj (coefficientComplex a)) ≫
      z.tensor.map (Prod.mkHom
        ((proEtaleRingDerivedPullbackFactors f A (inverseRing f A) (Iso.refl _)).hom.app P)
        (derivedCoefficientPullback f a).hom) ≫
      tensorScalarCoordinates (inverseMap f a) z
        (((proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _)
          ).mapHomologicalComplex (.up ℤ)).obj P) =
    (pull f A).map (tensorScalarCounit a P) ≫
      (pull f A).map (DerivedCategory.Q.map (ordinaryComplexIso a P).hom) ≫
      (proEtaleRingDerivedPullbackFactors f A (inverseRing f A) (Iso.refl _)).hom.app
        (CochainComplex.mapBifunctor P (coefficientComplex a) (proEtaleOrdinaryTensor T A)) ≫
      DerivedCategory.Q.map (tensorScalarOrdinaryPullback f a P)  := by
  classical
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let F := (proEtaleRingModulePullback f A (inverseRing f A)
    (Iso.refl _)).mapHomologicalComplex (.up ℤ)
  let U := pull f A
  let d := proEtaleRingDerivedPullbackFactors f A (inverseRing f A) (Iso.refl _)
  let TT := Functor.uncurry.obj ((proEtaleOrdinaryTensor T A).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))
  let TZ := Functor.uncurry.obj ((proEtaleOrdinaryTensor Z (inverseRing f A)
    ).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))
  let C := coefficientComplex a
  let k := tensorCoefficientComplexPullback f a
  let eT := derivedTensorIso a t
  let cZ := tensorScalarCoordinates (inverseMap f a) z (F.obj P)
  let mu := proEtaleCanonicalTensorComparison f A (inverseRing f A) (Iso.refl _) t z
  obtain ⟨Q, q, hQ, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (J := ProEt.topology T) (R := A) C
  have hQ' : proEtaleFlatRepresentatives T A Q := by
    refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat
      (R := A) Q).1 hQ, ?_⟩
    intro n
    exact (CategoryTheory.exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} A (Q.X n)).symm (hf n)
  obtain ⟨hpF, hqF, hsquare⟩ :=
    (Classical.choose_spec (proEtaleCanonicalTensorPullback f A (inverseRing f A)
      (Iso.refl _) t z).2.exists) P Q hp hQ'
  let q' : F.obj Q ⟶ coefficientComplex (inverseMap f a) := F.map q ≫ k.hom
  have : QuasiIso q := hq
  have : QuasiIso q' := by dsimp only [q']; infer_instance
  have hT := coordinates_normalization a t P Q hp hQ' q hq
  have hZ := coordinates_normalization (inverseMap f a) z
    (F.obj P) (F.obj Q) hpF hqF q' inferInstance
  let repT : DerivedCategory.Q.obj (TT.obj (P, Q)) ⟶
      t.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
    t.representative.hom.app (⟨P, hp⟩, ⟨Q, hQ'⟩)
  let repZ : DerivedCategory.Q.obj (TZ.obj (F.obj P, F.obj Q)) ⟶
      z.tensor.obj (DerivedCategory.Q.obj (F.obj P), DerivedCategory.Q.obj (F.obj Q)) :=
    z.representative.hom.app (⟨F.obj P, hpF⟩, ⟨F.obj Q, hqF⟩)
  let r := t.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q))
  have : IsIso (DerivedCategory.Q.map q) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) q hq
  have : IsIso (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q)) :=
    (CategoryTheory.isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso r := by dsimp only [r]; infer_instance
  have : IsIso repT := by dsimp only [repT]; infer_instance
  apply (cancel_epi (U.map (repT ≫ r ≫ eT.inv.app (DerivedCategory.Q.obj P)))).1
  have hnorm : U.map (repT ≫ r ≫ eT.inv.app (DerivedCategory.Q.obj P)) ≫
      U.map (tensorScalarCounit a P) ≫
      U.map (DerivedCategory.Q.map (ordinaryComplexIso a P).hom) =
    U.map (DerivedCategory.Q.map (TT.map (Prod.mkHom (𝟙 P) q))) := by
    rw [← U.map_comp, ← U.map_comp]
    apply congrArg U.map
    simpa only [tensorScalarCoordinates, repT, r, eT, TT, uncurry_map_id_left,
      Functor.map₂HomologicalComplex_obj_map, Category.assoc, Functor.comp_obj,
      Functor.prod_obj, ObjectProperty.ι_obj] using hT
  have hq' : U.map (DerivedCategory.Q.map q) ≫ (derivedCoefficientPullback f a).hom =
      d.hom.app Q ≫ DerivedCategory.Q.map q' := by
    have hd := d.hom.naturality q
    dsimp only [Functor.comp_map] at hd
    have hk : (derivedCoefficientPullback f a).hom = d.hom.app C ≫
        DerivedCategory.Q.map k.hom := by
      simp only [derivedCoefficientPullback, k, tensorCoefficientComplexPullback,
        Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp]
      rfl
    rw [hk]
    erw [← Category.assoc, hd]
    simp only [q', Functor.map_comp, Category.assoc]
    rfl
  have hprod : z.tensor.map (Prod.mkHom (𝟙 (U.obj (DerivedCategory.Q.obj P)))
        (U.map (DerivedCategory.Q.map q))) ≫
      z.tensor.map (Prod.mkHom (d.hom.app P) (derivedCoefficientPullback f a).hom) =
    z.tensor.map (Prod.mkHom (d.hom.app P) (d.hom.app Q)) ≫
      z.tensor.map (Prod.mkHom (𝟙 _) (DerivedCategory.Q.map q')) := by
    rw [← z.tensor.map_comp, ← z.tensor.map_comp]
    congr 1
    apply Prod.ext
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact hq'
  have hmu := mu.hom.naturality
    (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q))
  dsimp only [Functor.comp_map, Functor.prod_map] at hmu
  erw [(pull f A).map_id] at hmu
  change U.map r ≫ mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj C) =
    mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      z.tensor.map (Prod.mkHom (𝟙 _) (U.map (DerivedCategory.Q.map q))) at hmu
  change U.map repT ≫ mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      z.tensor.map (Prod.mkHom (d.hom.app P) (d.hom.app Q)) =
    d.hom.app (TT.obj (P, Q)) ≫
      DerivedCategory.Q.map (proEtaleTensorPullbackTotalIso f A (inverseRing f A)
        (Iso.refl _) P Q).inv ≫ repZ at hsquare
  have hZ' : repZ ≫ z.tensor.map
        (Prod.mkHom (𝟙 (DerivedCategory.Q.obj (F.obj P))) (DerivedCategory.Q.map q')) ≫ cZ =
      DerivedCategory.Q.map (TZ.map (Prod.mkHom (𝟙 (F.obj P)) q')) := by
    simpa only [repZ, cZ, TZ, uncurry_map_id_left,
      Functor.map₂HomologicalComplex_obj_map, Functor.comp_obj,
      Functor.prod_obj, ObjectProperty.ι_obj] using hZ
  have htotal : F.map (TT.map (Prod.mkHom (𝟙 P) q)) ≫
      tensorScalarOrdinaryPullback f a P =
    (proEtaleTensorPullbackTotalIso f A (inverseRing f A) (Iso.refl _) P Q).inv ≫
      TZ.map (Prod.mkHom (𝟙 (F.obj P)) q') :=
    tensorScalarOrdinaryPullback_naturality f a P Q q
  have hd := d.hom.naturality (TT.map (Prod.mkHom (𝟙 P) q))
  change U.map (DerivedCategory.Q.map (TT.map (Prod.mkHom (𝟙 P) q))) ≫
      d.hom.app (TT.obj (P, C)) =
    d.hom.app (TT.obj (P, Q)) ≫ DerivedCategory.Q.map
      (F.map (TT.map (Prod.mkHom (𝟙 P) q))) at hd
  change U.map (repT ≫ r ≫ eT.inv.app (DerivedCategory.Q.obj P)) ≫
      U.map (eT.hom.app (DerivedCategory.Q.obj P)) ≫
      mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj C) ≫
      z.tensor.map (Prod.mkHom (d.hom.app P) (derivedCoefficientPullback f a).hom) ≫ cZ =
    U.map (repT ≫ r ≫ eT.inv.app (DerivedCategory.Q.obj P)) ≫
      U.map (tensorScalarCounit a P) ≫
      U.map (DerivedCategory.Q.map (ordinaryComplexIso a P).hom) ≫
      d.hom.app (TT.obj (P, C)) ≫ DerivedCategory.Q.map (tensorScalarOrdinaryPullback f a P)
  rw [reassoc_of% hnorm]
  simp only [Functor.map_comp, Category.assoc]
  have hi : U.map (eT.inv.app (DerivedCategory.Q.obj P)) ≫
      U.map (eT.hom.app (DerivedCategory.Q.obj P)) = 𝟙 _ := by
    rw [← U.map_comp, eT.inv_hom_id_app, U.map_id]
  erw [reassoc_of% hi]
  rw [reassoc_of% hmu]
  rw [reassoc_of% hprod]
  rw [reassoc_of% hsquare]
  erw [hZ']
  erw [reassoc_of% hd]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun v ↦ d.hom.app (TT.obj (P, Q)) ≫ DerivedCategory.Q.map v) htotal.symm

end AlgebraicGeometry.Scheme.DerivedScalarMate
