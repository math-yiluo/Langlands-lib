/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ProEtaleSheafificationTensorComparison
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Tensor comparison for the intrinsic constant-ring realization

## References

* Stacks Project, Modules on Sites, Tags 03EK and 03EL, and Tag 00YV
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

private theorem intrinsic_sheafify (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    Nonempty (ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} A) ⋙
      PresheafOfModules.sheafification (ProEtale.finiteCoefficientIntrinsicScalarMap T A) ≅
    presheafToSheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) ⋙
      (Scheme.sfIntrinsicModuleEquivalence T A).functor) := by
  let J := Scheme.ProEt.topology T
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let P := ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} A)
  let S := PresheafOfModules.sheafification.{u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap T A)
  let c : P ⋙ S ⟶ presheafToSheaf J B ⋙ (Scheme.sfIntrinsicModuleEquivalence T A).functor :=
    Functor.whiskerRight (sheafificationAdjunction J B).unit (P ⋙ S)
  have : IsIso c := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro F
    change IsIso (S.map (P.map (toSheafify J F)))
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
    change IsIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map
      (Functor.whiskerRight (toSheafify J F) (forget₂ B AddCommGrpCat.{u + 1})))
    rw [← J.W_iff]
    rw [J.W_iff_isLocallyBijective]
    constructor
    · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J (toSheafify J F) x y h⟩
    · exact ⟨fun x ↦ Presheaf.imageSieve_mem J (toSheafify J F) x⟩
  exact ⟨asIso c⟩
private noncomputable def encode_tensorRight (T : Scheme.{u})
    (A : Type u) [CommRing A]
    (N : T.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :
    let P := ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} A)
    let O := (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A))
    letI : MonoidalCategory (PresheafOfModules.{u + 1}
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A)))) :=
    PresheafOfModules.monoidalCategory (R := O)
    P ⋙ tensorRight (P.obj N) ≅ tensorRight N ⋙ P := by
  let O := (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A))
  let : MonoidalCategory (PresheafOfModules.{u + 1}
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A)))) :=
    PresheafOfModules.monoidalCategory (R := O)
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine PresheafOfModules.isoMk (fun U ↦ Iso.refl _) ?_
    intro U V f
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    rfl
  · intro M M' f
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    rfl

attribute [local irreducible] SheafOfModules.monoidalCategory
  PresheafOfModules.sheafification

set_option backward.isDefEq.respectTransparency false in
/-- The canonical realization over the constant ring respects right tensoring. -/
theorem proEtale_intrinsic_tensorRight_comparison
    (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (N : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    Nonempty (
      (Scheme.sfIntrinsicModuleEquivalence T A).functor ⋙
          SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
            (J := Scheme.ProEt.topology T)
            (A := Scheme.proEtaleConstantRing T A)
            ((Scheme.sfIntrinsicModuleEquivalence T A).functor.obj N) ≅
        tensorRight N ⋙ (Scheme.sfIntrinsicModuleEquivalence T A).functor) := by
  let J := Scheme.ProEt.topology T
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let R := Scheme.proEtaleConstantRing T A
  let O := (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A))
  let P := ProEtale.finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1, u} A)
  let S := PresheafOfModules.sheafification.{u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap T A)
  let i := sheafToPresheaf J B
  let a := presheafToSheaf J B
  let E := (Scheme.sfIntrinsicModuleEquivalence T A).functor
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let : MonoidalCategory (PresheafOfModules.{u + 1}
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A)))) :=
    PresheafOfModules.monoidalCategory (R := O)
  obtain ⟨e, -⟩ := PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses
    (O := O) (R := R) (ProEtale.finiteCoefficientIntrinsicScalarMap T A)
  let q : E ⋙ tensorRight (E.obj N) ≅ i ⋙ P ⋙ tensorRight (P.obj N.obj) ⋙ S := by
    refine NatIso.ofComponents (fun M ↦ e.app (P.obj M.obj, P.obj N.obj)) ?_
    intro M M' f
    have h := e.hom.naturality (X := (P.obj M.obj, P.obj N.obj))
      (Y := (P.obj M'.obj, P.obj N.obj)) (P.map f.hom, 𝟙 (P.obj N.obj))
    change (S.map (P.map f.hom) ⊗ₘ S.map (𝟙 (P.obj N.obj))) ≫
        (e.app (P.obj M'.obj, P.obj N.obj)).hom =
      (e.app (P.obj M.obj, P.obj N.obj)).hom ≫
        S.map (P.map f.hom ⊗ₘ 𝟙 (P.obj N.obj)) at h
    rw [S.map_id, tensorHom_id, tensorHom_id] at h
    exact h
  obtain ⟨r⟩ := intrinsic_sheafify T A
  let c : i ⋙ a ≅ 𝟭 _ := asIso (sheafificationAdjunction J B).counit
  let k : i ⋙ tensorRight N.obj ⋙ a ≅ tensorRight N :=
    Functor.isoWhiskerLeft i (Functor.Monoidal.commTensorRight a N.obj).symm ≪≫
      Functor.isoWhiskerRight c (tensorRight (a.obj N.obj)) ≪≫
      (curriedTensor _).flip.mapIso (c.app N)
  exact ⟨Functor.isoWhiskerLeft E (SheafOfModules.siteSheafTensorRightIso R (E.obj N)) ≪≫
    q ≪≫ Functor.isoWhiskerLeft i
      (Functor.isoWhiskerRight (encode_tensorRight T A N.obj) S) ≪≫
    Functor.isoWhiskerLeft (i ⋙ tensorRight N.obj) r ≪≫
    Functor.isoWhiskerRight k E⟩

end AlgebraicGeometry
