/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumTensorTestComparison
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ProEtaleSheafificationTensorComparison
public import Mathlib.Algebra.Category.Ring.FilteredColimits
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
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
/-!
# Tensor compatibility of constant-coefficient realization

Source: Stacks Project, Modules on Sites, Tags 0GMW, 093I and 03CV.
The realization is identified with module sheafification of the constant-scalar
presheaf encoding, which carries the sectionwise tensor product unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory PresheafOfModules
namespace AlgebraicGeometry.Scheme.ConstantTensorAux
universe w
open Opposite
set_option backward.isDefEq.respectTransparency false

private def nativeEncoding (T : Scheme.{w}) (A : Type (w + 1)) [CommRing A] :
    (T.Etaleᵒᵖ ⥤ ModuleCat.{w + 1} A) ⥤
      PresheafOfModules.{w + 1}
      (((Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of A)) ⋙
        forget₂ CommRingCat.{w + 1} RingCat.{w + 1}) where
  obj F :=
    letI (W : T.Etaleᵒᵖ) : Module
        ((((Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of A)) ⋙
          forget₂ CommRingCat.{w + 1} RingCat.{w + 1}).obj W)
        ((F ⋙ forget₂ (ModuleCat.{w + 1} A) AddCommGrpCat.{w + 1}).obj W) :=
      (F.obj W).isModule
    PresheafOfModules.ofPresheaf
      (R := ((Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of A)) ⋙
        forget₂ CommRingCat.{w + 1} RingCat.{w + 1})
      (F ⋙ forget₂ (ModuleCat.{w + 1} A) AddCommGrpCat.{w + 1})
      (fun {_ _} f r m ↦ (F.map f).hom.map_smul r m)
  map {F G} f := PresheafOfModules.homMk
    (Functor.whiskerRight f (forget₂ (ModuleCat.{w + 1} A) AddCommGrpCat.{w + 1}))
    (fun W r m ↦ (f.app W).hom.map_smul r m)
  map_id F := by ext W x; rfl
  map_comp f g := by ext W x; rfl

private abbrev coeffRing (T : Scheme.{w}) (A : Type (w + 1)) [CommRing A] :=
  (constantSheaf T.smallEtaleTopology CommRingCat.{w + 1}).obj (CommRingCat.of A)

private def coeffMap (T : Scheme.{w}) (A : Type (w + 1)) [CommRing A] :
    ((Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of A)) ⋙
        forget₂ CommRingCat.{w + 1} RingCat.{w + 1} ⟶
      ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj (coeffRing T A)).obj :=
  toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A)) ≫
    (constantModuleHomRingIso T.smallEtaleTopology A).hom.hom

private instance coeffMap_locallyInjective (T : Scheme.{w}) (A : Type (w + 1))
    [CommRing A] : Presheaf.IsLocallyInjective T.smallEtaleTopology (coeffMap T A) := by
  let : IsIso ((constantModuleHomRingIso T.smallEtaleTopology A).hom.hom) :=
    inferInstanceAs (IsIso ((sheafToPresheaf T.smallEtaleTopology RingCat).map
      (constantModuleHomRingIso T.smallEtaleTopology A).hom))
  let : PreservesFilteredColimitsOfSize.{w + 1, w + 1}
      (CategoryTheory.forget RingCat.{w + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{w + 1, w + 1, w + 1, w + 1} _
  have : T.smallEtaleTopology.WEqualsLocallyBijective RingCat.{w + 1} := by
    infer_instance
  dsimp only [coeffMap]
  let : Presheaf.IsLocallyInjective T.smallEtaleTopology
      (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A))) :=
    (T.smallEtaleTopology.W_toSheafify _).isLocallyInjective
  exact Presheaf.isLocallyInjective_comp T.smallEtaleTopology _ _

private instance coeffMap_locallySurjective (T : Scheme.{w}) (A : Type (w + 1))
    [CommRing A] : Presheaf.IsLocallySurjective T.smallEtaleTopology (coeffMap T A) := by
  let : IsIso ((constantModuleHomRingIso T.smallEtaleTopology A).hom.hom) :=
    inferInstanceAs (IsIso ((sheafToPresheaf T.smallEtaleTopology RingCat).map
      (constantModuleHomRingIso T.smallEtaleTopology A).hom))
  let : PreservesFilteredColimitsOfSize.{w + 1, w + 1}
      (CategoryTheory.forget RingCat.{w + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{w + 1, w + 1, w + 1, w + 1} _
  have : T.smallEtaleTopology.WEqualsLocallyBijective RingCat.{w + 1} := by
    infer_instance
  dsimp only [coeffMap]
  let : Presheaf.IsLocallySurjective T.smallEtaleTopology
      (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A))) :=
    (T.smallEtaleTopology.W_toSheafify _).isLocallySurjective
  exact Presheaf.isLocallySurjective_comp T.smallEtaleTopology _ _

private def realizationUnit (T : Scheme.{w}) (A : Type (w + 1)) [CommRing A]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{w + 1} A)) :
    (nativeEncoding T A).obj F.obj ⟶
      (PresheafOfModules.restrictScalars (coeffMap T A)).obj
        (((etaleSumTensorTestRealization T A).obj F).val) := by
  refine PresheafOfModules.homMk (𝟙 _) ?_
  intro W r m
  change r • m =
    ((constantModuleHomRingIso T.smallEtaleTopology A).inv.hom.app W
      ((constantModuleHomRingIso T.smallEtaleTopology A).hom.hom.app W
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A))).app W r))) •
            (show ((etaleConstantModuleFunctor T A).obj F).val.obj W from m)
  let h := (PresheafOfModules.toSheafify
    (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A)))
    (M₀ := etaleConstantModulePresheaf T A F)
    (A := (sheafCompose T.smallEtaleTopology
      (forget₂ (ModuleCat.{w + 1} A) AddCommGrpCat.{w + 1})).obj F)
    (𝟙 _)).app W
  have hi := congrArg (fun f ↦ f.hom.app W)
    (constantModuleHomRingIso T.smallEtaleTopology A).hom_inv_id
  have hir : (constantModuleHomRingIso T.smallEtaleTopology A).inv.hom.app W
      ((constantModuleHomRingIso T.smallEtaleTopology A).hom.hom.app W
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A))).app W r)) =
      (toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A))).app W r :=
    ConcreteCategory.congr_hom hi _
  rw [hir]
  change r • m = (toSheafify T.smallEtaleTopology
    ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of A))).app W r •
      (show ((etaleConstantModuleFunctor T A).obj F).val.obj W from m)
  exact h.hom.map_smul r m

private def realizeSheafMap (T : Scheme.{w}) (A : Type (w + 1)) [CommRing A]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{w + 1} A)) :
    (PresheafOfModules.sheafification.{w + 1} (coeffMap T A)).obj
      ((nativeEncoding T A).obj F.obj) ⟶ (etaleSumTensorTestRealization T A).obj F :=
  (PresheafOfModules.sheafificationHomEquiv.{w + 1} (coeffMap T A)).symm (realizationUnit T A F)

private theorem realizeSheafMap_isIso (T : Scheme.{w}) (A : Type (w + 1))
    [CommRing A] (F : Sheaf T.smallEtaleTopology (ModuleCat.{w + 1} A)) :
    IsIso (realizeSheafMap T A F) := by
  apply (isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)).mp
  rw [realizeSheafMap, PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
  change IsIso (((sheafificationAdjunction T.smallEtaleTopology AddCommGrpCat.{w + 1}).homEquiv
    _ _).symm (𝟙 _))
  rw [Adjunction.homEquiv_symm_id]
  change IsIso ((sheafificationAdjunction T.smallEtaleTopology AddCommGrpCat.{w + 1}).counit.app
    ((sheafCompose T.smallEtaleTopology
      (forget₂ (ModuleCat.{w + 1} A) AddCommGrpCat)).obj F))
  infer_instance

private def realizeSheafIso (T : Scheme.{w}) (A : Type (w + 1)) [CommRing A] :
    sheafToPresheaf T.smallEtaleTopology (ModuleCat.{w + 1} A) ⋙ nativeEncoding T A ⋙
      PresheafOfModules.sheafification.{w + 1} (coeffMap T A) ≅
        etaleSumTensorTestRealization T A := by
  refine NatIso.ofComponents (fun F ↦ ?_) ?_
  · letI := realizeSheafMap_isIso T A F
    exact asIso (realizeSheafMap T A F)
  · intro F G f
    apply (PresheafOfModules.sheafificationHomEquiv.{w + 1} (coeffMap T A)).injective
    change (PresheafOfModules.sheafificationAdjunction.{w + 1} (coeffMap T A)).homEquiv _ _
      (_ ≫ _) = (PresheafOfModules.sheafificationAdjunction.{w + 1}
        (coeffMap T A)).homEquiv _ _ (_ ≫ _)
    dsimp only [Functor.comp_map, asIso_hom]
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [realizeSheafMap,
      PresheafOfModules.sheafificationAdjunction_homEquiv_apply]
    change _ ≫ (PresheafOfModules.sheafificationHomEquiv _
      ((PresheafOfModules.sheafificationHomEquiv _).symm _)) =
        (PresheafOfModules.sheafificationHomEquiv _
          ((PresheafOfModules.sheafificationHomEquiv _).symm _)) ≫ _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    ext W x
    rfl

private def realizeSheafificationIso (T : Scheme.{w}) (A : Type (w + 1)) [CommRing A] :
    nativeEncoding T A ⋙ PresheafOfModules.sheafification.{w + 1} (coeffMap T A) ≅
      presheafToSheaf T.smallEtaleTopology (ModuleCat.{w + 1} A) ⋙
        etaleSumTensorTestRealization T A := by
  let J := T.smallEtaleTopology
  let B := ModuleCat.{w + 1} A
  have : J.PreservesSheafification (forget₂ B AddCommGrpCat.{w + 1}) :=
    GrothendieckTopology.instPreservesSheafification J _
      (FD := fun M N : B ↦ M →ₗ[A] N) (CD := fun M : B ↦ M)
      (FE := fun M N : AddCommGrpCat.{w + 1} ↦ M →+ N)
      (CE := fun M : AddCommGrpCat.{w + 1} ↦ M)
  let P := nativeEncoding T A
  let S := PresheafOfModules.sheafification.{w + 1} (coeffMap T A)
  let c := Functor.whiskerRight (sheafificationAdjunction J B).unit (P ⋙ S)
  have hc : IsIso c := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro F
    change IsIso (S.map (P.map (toSheafify J F)))
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
    change IsIso ((presheafToSheaf J AddCommGrpCat.{w + 1}).map
      (Functor.whiskerRight (toSheafify J F) (forget₂ B AddCommGrpCat.{w + 1})))
    rw [← J.W_iff]
    exact J.W_of_preservesSheafification (forget₂ B AddCommGrpCat.{w + 1}) _
      (J.W_toSheafify F)
  exact asIso c ≪≫ Functor.isoWhiskerLeft (presheafToSheaf J B) (realizeSheafIso T A)

private def encode_tensor (T : Scheme.{w}) (A : Type (w + 1)) [CommRing A] :
    let O := (Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of A)
    letI := PresheafOfModules.monoidalCategory (R := O)
    (nativeEncoding T A).prod (nativeEncoding T A) ⋙ tensor _ ≅
      tensor _ ⋙ nativeEncoding T A := by
  let O := (Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of A)
  letI := PresheafOfModules.monoidalCategory (R := O)
  refine NatIso.ofComponents (fun MN ↦ ?_) ?_
  · refine PresheafOfModules.isoMk (fun W ↦ Iso.refl _) ?_
    intro W V f
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    rfl
  · intro MN MN' f
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    rfl

end AlgebraicGeometry.Scheme.ConstantTensorAux

namespace AlgebraicGeometry.Scheme

-- The tensor comparisons require elaborating several large sheafification functor composites.
/-- The constant-scalar tensor comparison is natural in both factors.
Source: Stacks Project, Modules on Sites, Tag 0GMW
(blueprint: lem-pur-etale-constant-module-tensor).
Proof: identify realization with module sheafification of the sectionwise constant
scalar encoding. Apply the natural tensor comparison for module sheafification,
then the monoidal comparison for sheafification of module-valued presheaves. The
sheafification counit identifies the two original sheaves. -/
theorem etaleConstantModule_tensor_comparison (T : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    let R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
      (CommRingCat.of A)
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory R
    Nonempty ((etaleSumTensorTestRealization T A).prod
      (etaleSumTensorTestRealization T A) ⋙ tensor _ ≅
      tensor _ ⋙ etaleSumTensorTestRealization T A) := by
  let J := T.smallEtaleTopology
  let B := ModuleCat.{u + 1} A
  let R := (constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of A)
  let O := (Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of A)
  let P := ConstantTensorAux.nativeEncoding T A
  let S := PresheafOfModules.sheafification.{u + 1} (ConstantTensorAux.coeffMap T A)
  let i := sheafToPresheaf J B
  let a := presheafToSheaf J B
  let E := etaleSumTensorTestRealization T A
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := PresheafOfModules.monoidalCategory (R := O)
  obtain ⟨e, _⟩ := PresheafOfModules.exists_sheafificationTensorIso_proEtaleUniverses
    (O := O) (R := R) (ConstantTensorAux.coeffMap T A)
  let r := ConstantTensorAux.realizeSheafIso T A
  let q : E.prod E ⋙ tensor _ ≅ (i ⋙ P).prod (i ⋙ P) ⋙ tensor _ ⋙ S :=
    Functor.isoWhiskerRight (NatIso.prod r.symm r.symm) (tensor _) ≪≫
      Functor.isoWhiskerLeft ((i ⋙ P).prod (i ⋙ P)) e
  let c : i ⋙ a ≅ 𝟭 _ := asIso (sheafificationAdjunction J B).counit
  let k : i.prod i ⋙ tensor _ ⋙ a ≅ tensor _ :=
    Functor.isoWhiskerLeft (i.prod i) (Functor.Monoidal.μNatIso a).symm ≪≫
      Functor.isoWhiskerRight (NatIso.prod c c) (tensor _)
  exact ⟨q ≪≫ Functor.isoWhiskerLeft (i.prod i)
    (Functor.isoWhiskerRight (ConstantTensorAux.encode_tensor T A) S) ≪≫
    Functor.isoWhiskerLeft (i.prod i ⋙ tensor _)
      (ConstantTensorAux.realizeSheafificationIso T A) ≪≫
    Functor.isoWhiskerRight k E⟩

-- The tensor comparisons require elaborating several large sheafification functor composites.
/-- Realizing constant coefficients commutes naturally with right tensor.
Source: Stacks Project, Modules on Sites, Sections 03EK, 093I and 03CV
(blueprint: lem-pur-etale-constant-module-tensor).

Proof: the universal bilinear map on module-valued sheaves is A-balanced. On any
cover on which a section of the constant ring sheaf is a constant scalar, that map
is also balanced over the ring sheaf. Refine the covers for the finitely many
coefficients in each tensor expression. The separatedness axiom then gives the
ring-sheaf balanced relation globally. The universal property of the sectionwise
tensor, followed by module sheafification, therefore gives a morphism from tensor
of realizations to realization of the A-tensor. Conversely the universal pure-tensor
map for the sectionwise ring-sheaf tensor is A-balanced by the scalar-extension unit;
sheafifying gives a map in the opposite direction. Both composites fix all pure
tensors, so tensor generation and uniqueness of sheafification make them identities.
The two maps commute with a morphism in the first factor on every pure tensor,
which proves naturality. The canonical coefficient-ring isomorphism changes scalar
actions by restriction only, so the same formulas commute with its transport.
Empty covers, zero coefficients and zero sheaves use the same universal properties.
The statement involves neither flatness nor an extension-by-zero morphism. -/
theorem etaleConstantModule_tensorRight_comparison (T : Scheme.{u})
    (A : Type (u + 1)) [CommRing A]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Nonempty (etaleSumTensorTestRealization T A ⋙
      SheafOfModules.siteSheafTensorRight.{_, _, _, u + 1} (J := T.smallEtaleTopology)
        (A := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of A)) ((etaleSumTensorTestRealization T A).obj F) ≅
      tensorRight F ⋙ etaleSumTensorTestRealization T A)  := by
  let R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
    (CommRingCat.of A)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  obtain ⟨e⟩ := etaleConstantModule_tensor_comparison T A
  refine ⟨Functor.isoWhiskerLeft (etaleSumTensorTestRealization T A)
    (SheafOfModules.siteSheafTensorRightIso R
      ((etaleSumTensorTestRealization T A).obj F)) ≪≫ ?_⟩
  exact NatIso.ofComponents (fun M ↦ e.app (M, F)) (fun {M N} f ↦ by
    simpa using e.hom.naturality (X := (M, F)) (Y := (N, F)) (f, 𝟙 F))

end AlgebraicGeometry.Scheme
