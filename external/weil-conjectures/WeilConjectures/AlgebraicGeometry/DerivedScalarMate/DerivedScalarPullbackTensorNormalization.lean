/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateData
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarMateOrdinaryTensorRoute
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.ScalarTensorOneSidedPullback
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

/-! # Tensor normalization before taking the geometric scalar mate

Source: Stacks Project, Tags 03EK, 06YY, 07A4 and 07A6; the representative
calculation in step 1 of lem-sfb-derived-scalar-projection-normalization.
(blueprint: lem-sfb-derived-scalar-pullback-tensor-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.DerivedScalarMate

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
  proEtaleRingModulePullback proEtaleRingDerivedPullbackFactors
  proEtaleCanonicalTensorComparison SheafOfModules.monoidalCategory

private theorem coordinates_isIso {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : A ⟶ B)
    (t : ProEtaleTensorModel W A) (P : CochainComplex (proEtaleRingModules W A) ℤ)
    (hp : proEtaleFlatRepresentatives W A P) : IsIso (tensorScalarCoordinates a t P) := by
  have hP := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat
    (R := A) P).2 hp.1
  have : IsIso ((proEtaleRingDerivedExtensionCounit a).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
    (reductionDerivedExistence W a).choose_spec.choose_spec.2.2 P hP
  unfold tensorScalarCoordinates tensorScalarCounit
  change IsIso ((derivedTensorIso a t).inv.app (DerivedCategory.Q.obj P) ≫
    ((restriction a).mapDerivedCategory.map
        ((proEtaleRingDerivedExtensionCounit a).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (restriction a).mapDerivedCategoryFactorsh.hom.app
        (((proEtaleRingExtension a).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) ≫
    DerivedCategory.Q.map (ordinaryComplexIso a P).hom)
  infer_instance

private theorem flat_representative {T : Scheme.{u}}
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (M : DerivedCategory (proEtaleRingModules T A)) :
    ∃ (P : CochainComplex (proEtaleRingModules T A) ℤ)
      (_hp : proEtaleFlatRepresentatives T A P), Nonempty (DerivedCategory.Q.obj P ≅ M) := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let C := DerivedCategory.Q.objPreimage M
  obtain ⟨P, q, hp, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients.{u + 1, u + 1, u}
      (J := ProEt.topology T) (R := A) C
  have : IsIso (DerivedCategory.Q.map q) :=
    Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) q hq
  refine ⟨P, ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat
    (R := A) P).1 hp, ?_⟩, ⟨asIso (DerivedCategory.Q.map q) ≪≫
    DerivedCategory.Q.objObjPreimageIso M⟩⟩
  intro n
  exact (CategoryTheory.exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} A (P.X n)).symm (hf n)

/-- Scalar extension and pullback agree with the normalized tensor comparison,
before taking any right-adjoint mate. The coefficient comparison is the specified
pullback of the degree-zero restricted B-module, including its unit normalization.

Source: Stacks 03EK, 06YY, 07A4, 07A6; step 1 of the projection-normalization node
(blueprint: lem-sfb-derived-scalar-pullback-tensor-normalization).

Proof: choose a flat-term K-flat complex P representing M and a flat-term K-flat
resolution Q of coefficientComplex a. Pullback preserves these resolving classes.
Use IsDerivedTensor at P,Q and at their pullbacks, and the representative square
of proEtaleCanonicalTensorComparison. The scalar-derived counits are invertible
on these representatives. The inverse scalar mate is the balanced ordinary
scalar/pullback comparison by kflat_scalar_comparison_normalization. After the
ordinary tensor identification, both composites take the inverse image of b tensor m
to pullback(m) tensor pullback(b). This is equality on all local pure tensors,
including nonconstant b, so the balanced tensor universal property and sheafification
prove equality of module maps. Applying this in every degree and using the
single-factor complex identification proves equality of chain maps. The coefficient
unit comparison is exactly coefficientPullback, so its degree-zero localization
is derivedCoefficientPullback. Tensoring the resolution Q to B[0] is a
quasi-isomorphism because P is K-flat; no flatness of B is needed. Cancel these
resolution maps and the scalar counits. Naturality and the resolving localization
equivalence extend the equality from P to every M. This uses no direct image,
no geometric counit and no projection morphism. -/
theorem scalarPullback_tensor_normalization
    {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (t : ProEtaleTensorModel T A) (z : ProEtaleTensorModel Z (inverseRing f A))
    (M : DerivedCategory (proEtaleRingModules T A)) :
    (proEtaleRingRestrictionDerivedPullback f A B (inverseRing f A) (inverseRing f B)
        a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)).inv.app
          ((proEtaleRingDerivedExtension a).obj M) ≫
      (restriction (inverseMap f a)).mapDerivedCategory.map ((scalarPullback f a).hom.app M) ≫
      (derivedTensorIso (inverseMap f a) z).hom.app ((pull f A).obj M) ≫
      z.tensor.map (Prod.mkHom (𝟙 _) (derivedCoefficientPullback f a).inv) =
    (pull f A).map ((derivedTensorIso a t).hom.app M) ≫
      (proEtaleCanonicalTensorComparison f A (inverseRing f A) (Iso.refl _) t z).hom.app
        (M, DerivedCategory.Q.obj (coefficientComplex a))  := by
  classical
  let U := pull f A
  let rT := (restriction a).mapDerivedCategory
  let rZ := (restriction (inverseMap f a)).mapDerivedCategory
  let E := proEtaleRingDerivedExtension a
  let b := proEtaleRingRestrictionDerivedPullback f A B (inverseRing f A) (inverseRing f B)
    a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)
  let eT := derivedTensorIso a t
  let eZ := derivedTensorIso (inverseMap f a) z
  let c : U.obj (DerivedCategory.Q.obj (coefficientComplex a)) ≅
      DerivedCategory.Q.obj (coefficientComplex (inverseMap f a)) :=
    derivedCoefficientPullback f a
  let mu := proEtaleCanonicalTensorComparison f A (inverseRing f A) (Iso.refl _) t z
  let L : E ⋙ rT ⋙ U ⟶ U ⋙ (Functor.curryObj z.tensor).flip.obj
      (U.obj (DerivedCategory.Q.obj (coefficientComplex a))) :=
    Functor.whiskerLeft E b.inv ≫ Functor.whiskerRight (scalarPullback f a).hom rZ ≫
      Functor.whiskerLeft U eZ.hom ≫
      Functor.whiskerLeft U ((Functor.curryObj z.tensor).flip.map c.inv)
  let R : E ⋙ rT ⋙ U ⟶ U ⋙ (Functor.curryObj z.tensor).flip.obj
      (U.obj (DerivedCategory.Q.obj (coefficientComplex a))) :=
    Functor.whiskerRight eT.hom U ≫
      { app := fun X ↦ mu.hom.app (X, DerivedCategory.Q.obj (coefficientComplex a))
        naturality := by
          intro X Y v
          have hn := mu.hom.naturality
            (Prod.mkHom v (𝟙 (DerivedCategory.Q.obj (coefficientComplex a))))
          dsimp only [Functor.comp_map, Functor.prod_map] at hn
          erw [(pull f A).map_id] at hn
          simpa only [Functor.comp_map, Functor.flip_obj_map, Functor.curryObj] using hn }
  have rep (P : CochainComplex (proEtaleRingModules T A) ℤ)
      (hp : proEtaleFlatRepresentatives T A P) :
      L.app (DerivedCategory.Q.obj P) = R.app (DerivedCategory.Q.obj P) := by
    let P' := ((proEtaleRingModulePullback f A (inverseRing f A)
      (Iso.refl _)).mapHomologicalComplex (.up ℤ)).obj P
    let d : U.obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj P' :=
      (proEtaleRingDerivedPullbackFactors f A (inverseRing f A) (Iso.refl _)).hom.app P
    have hp' := (proEtaleCanonicalTensorPullback f A (inverseRing f A)
      (Iso.refl _) t z).1 P hp
    have : IsIso (tensorScalarCoordinates (inverseMap f a) z P') :=
      coordinates_isIso (inverseMap f a) z P' hp'
    have : IsIso (Prod.mkHom d c.hom) :=
      (CategoryTheory.isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    let post := z.tensor.map (Prod.mkHom d c.hom) ≫
      tensorScalarCoordinates (inverseMap f a) z P'
    have : IsIso post := by dsimp only [post, d, c]; infer_instance
    apply (cancel_mono post).1
    have hc : z.tensor.map (Prod.mkHom (𝟙 _) c.inv) ≫
        z.tensor.map (Prod.mkHom d c.hom) = z.tensor.map (Prod.mkHom d (𝟙 _)) := by
      rw [← z.tensor.map_comp]
      congr 1
      exact Prod.ext (Category.id_comp d) c.inv_hom_id
    dsimp only [L, R, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, post, Functor.flip_map_app, Functor.curryObj]
    simp only [Category.assoc]
    rw [← Category.assoc (z.tensor.map (Prod.mkHom (𝟙 _) c.inv)), hc]
    have he := eZ.hom.naturality d
    change rZ.map ((proEtaleRingDerivedExtension (inverseMap f a)).map d) ≫
        eZ.hom.app (DerivedCategory.Q.obj P') =
      eZ.hom.app (U.obj (DerivedCategory.Q.obj P)) ≫
        z.tensor.map (Prod.mkHom d (𝟙 _)) at he
    have ht := tensorScalar_oneSided_pullback f a t z P hp
    unfold tensorScalarCoordinates at ht ⊢
    erw [← reassoc_of% he]
    erw [Iso.hom_inv_id_app_assoc]
    exact (scalarMate_ordinary_tensor_route f a P hp).trans ht.symm
  obtain ⟨P, hp, ⟨i⟩⟩ := flat_representative A M
  have hL := L.naturality i.hom
  have hR := R.naturality i.hom
  have h : L.app M = R.app M := by
    apply (cancel_epi ((E ⋙ rT ⋙ U).map i.hom)).1
    exact hL.trans ((congrArg (fun q ↦ q ≫
      (U ⋙ (Functor.curryObj z.tensor).flip.obj
        (U.obj (DerivedCategory.Q.obj (coefficientComplex a)))).map i.hom)
      (rep P hp)).trans hR.symm)
  simpa only [L, R, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.flip_map_app, Functor.curryObj, Category.assoc] using h

end AlgebraicGeometry.Scheme.DerivedScalarMate
