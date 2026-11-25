/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarTensorOrdinary
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionFormulaArrows
public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaBaseChangeNaturality
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Algebra.Homology.ScalarPullback.KFlatScalarComparisonNormalization
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarTensorRepresentatives
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
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

/-! # Normalized scalar tensor and geometric mate data

Source: blueprint main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md,
paragraph (3), agent-extracted ring-sheaf subargument; Stacks Tags 03EL, 06YY,
07A4, 07A6, 0G7E, 0FPT and 014A
(blueprint: lem-sfb-derived-scalar-tensor-identification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme.DerivedScalarMate
attribute [local irreducible] SheafOfModules.monoidalCategory

/-- The full normalization of h on two flat K-flat representatives, resolving B too.
The equation uses Q → B[0] only after tensoring with the K-flat first factor.
Source: Stacks 06YY, 07A4 (blueprint: lem-sfb-derived-scalar-tensor-identification). -/
def IsDerivedTensor {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B)
    (a : Scheme.ProEtaleTensorModel W A)
    (h : Scheme.proEtaleRingDerivedExtension φ ⋙ (restriction φ).mapDerivedCategory ≅
      (Functor.curryObj a.tensor).flip.obj
        (DerivedCategory.Q.obj (coefficientComplex φ))) : Prop :=
  ∀ (P Q : CochainComplex (Scheme.proEtaleRingModules W
      A) ℤ)
    (hp : Scheme.proEtaleFlatRepresentatives W A P)
    (hq : Scheme.proEtaleFlatRepresentatives W A Q)
    (q : Q ⟶ coefficientComplex φ), QuasiIso q →
    a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
      a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q)) ≫
      h.inv.app (DerivedCategory.Q.obj P) ≫
      (restriction φ).mapDerivedCategory.map
        (cast (by rfl) ((Scheme.proEtaleRingDerivedExtensionCounit
          φ).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) ≫
      (restriction φ).mapDerivedCategoryFactorsh.hom.app
        (((Scheme.proEtaleRingExtension
          φ).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) =
    cast (by rfl) (DerivedCategory.Q.map
      (HomologicalComplex.mapBifunctorMap (𝟙 P) q
        (Scheme.proEtaleOrdinaryTensor W A)
        (ComplexShape.up ℤ) ≫ (ordinaryComplexIso φ P).inv))

set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] ordinaryTensorIso CategoryTheory.Functor.leftAdjoint
  CategoryTheory.presheafToSheaf HomologicalComplex₂.total ordinaryComplexIso

private theorem representativeWhiskering
    (W : Scheme.{u}) (A : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :
    Nonempty (((Functor.whiskeringLeft
      ((proEtaleFlatRepresentatives W A).FullSubcategory ×
        (proEtaleFlatRepresentatives W A).FullSubcategory)
      (DerivedCategory (proEtaleRingModules W A) ×
        DerivedCategory (proEtaleRingModules W A))
      (DerivedCategory (proEtaleRingModules W A))).obj
      (((proEtaleFlatRepresentatives W A).ι ⋙ DerivedCategory.Q).prod
        ((proEtaleFlatRepresentatives W A).ι ⋙ DerivedCategory.Q))).FullyFaithful) := by
  let M := proEtaleRingModules W A
  let PR := proEtaleFlatRepresentatives W A
  let H : ObjectProperty (HomotopyCategory M (.up ℤ)) := fun K ↦ PR K.as
  have hres : ∀ K : HomotopyCategory M (.up ℤ),
      ∃ (V : H.FullSubcategory) (q : V.obj ⟶ K), HomotopyCategory.quasiIso M (.up ℤ) q := by
    intro K
    obtain ⟨P, q, hp, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := A) K.as
    have hflat : ∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology W) (R := A)
        (P.X n) := fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso A (P.X n)).symm (hf n)
    refine ⟨⟨(HomotopyCategory.quotient M (.up ℤ)).obj P,
      (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hp, hflat⟩,
      (HomotopyCategory.quotient M (.up ℤ)).map q, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq
  obtain ⟨ff⟩ := CategoryTheory.resolvingRepresentativesFullyFaithfulWhiskering
    (K := CochainComplex M ℤ) (H := HomotopyCategory M (.up ℤ))
    (D := DerivedCategory M) (DerivedCategory M)
    (HomotopyCategory.quotient M (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso M (.up ℤ)) DerivedCategory.Qh PR H (fun _ ↦ Iff.rfl) hres
  exact ⟨ff.ofIso ((Functor.whiskeringLeft _ _ (DerivedCategory M)).mapIso
    (NatIso.prod (Functor.isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso M))
      (Functor.isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso M))))⟩

private theorem unaryWhiskering
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (L : C ⥤ D)
    (ff : ((Functor.whiskeringLeft (C × C) (D × D) E).obj (L.prod L)).FullyFaithful) :
    Nonempty (((Functor.whiskeringLeft C D E).obj L).FullyFaithful) := by
  let U := (Functor.whiskeringLeft C D E).obj L
  have : U.Faithful := ⟨by
    intro F G a b hab
    have he : Functor.whiskerLeft (CategoryTheory.Prod.fst D D) a =
        Functor.whiskerLeft (CategoryTheory.Prod.fst D D) b := by
      apply ff.map_injective
      ext X
      exact congr_app hab X.1
    ext X
    exact congr_app he (X, X)⟩
  have : U.Full := ⟨by
    intro F G a
    let a₂ : (L.prod L) ⋙ CategoryTheory.Prod.fst D D ⋙ F ⟶
        (L.prod L) ⋙ CategoryTheory.Prod.fst D D ⋙ G :=
      { app := fun X ↦ a.app X.1
        naturality := by
          intro X Y f
          exact a.naturality f.1 }
    let b₂ := ff.preimage a₂
    refine ⟨Functor.whiskerLeft (Functor.diag D) b₂, ?_⟩
    ext X
    exact congr_app (ff.map_preimage a₂) (X, X)⟩
  exact ⟨Functor.FullyFaithful.ofFullyFaithful U⟩

private def scalarCounit {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : A ⟶ B) :
    DerivedCategory.Q ⋙ proEtaleRingDerivedExtension φ ⋙ (restriction φ).mapDerivedCategory ⟶
      (proEtaleRingExtension φ).mapHomologicalComplex (.up ℤ) ⋙
        (restriction φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q where
  app P := (restriction φ).mapDerivedCategory.map
      ((proEtaleRingDerivedExtensionCounit φ).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
    (restriction φ).mapDerivedCategoryFactorsh.hom.app
      (((proEtaleRingExtension φ).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
  naturality := by
    intro P P' v
    have h := (proEtaleRingDerivedExtensionCounit φ).naturality
      ((HomotopyCategory.quotient _ (.up ℤ)).map v)
    have h' := (restriction φ).mapDerivedCategoryFactorsh.hom.naturality
      (((proEtaleRingExtension φ).mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient _ (.up ℤ)).map v))
    dsimp only [Functor.comp_map]
    dsimp only [Functor.comp_map] at h h'
    erw [← Functor.map_comp_assoc, h, Functor.map_comp, Category.assoc, h']
    rw [Category.assoc]
    rfl

private theorem scalarCounit_isIso {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : A ⟶ B)
    (P : CochainComplex (proEtaleRingModules W A) ℤ)
    (hp : proEtaleFlatRepresentatives W A P) : IsIso ((scalarCounit φ).app P) := by
  have : IsIso ((proEtaleRingDerivedExtensionCounit φ).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) :=
    (reductionDerivedExistence W φ).choose_spec.choose_spec.2.2 P
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp.1)
  dsimp only [scalarCounit]
  infer_instance

private theorem coefficientResolution {W : Scheme.{u}}
    {A B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : A ⟶ B) :
    ∃ (Q : CochainComplex (proEtaleRingModules W A) ℤ)
      (_hq : proEtaleFlatRepresentatives W A Q) (q : Q ⟶ coefficientComplex φ), QuasiIso q := by
  obtain ⟨Q, q, hk, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := A)
      (coefficientComplex φ)
  exact ⟨Q, ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q).1 hk,
    fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso A (Q.X n)).symm (hf n)⟩, q, hq⟩

/-- The restricted extension is the derived tensor with B, with its full normalization.
Source: Stacks 06YY, 07A4 (blueprint: lem-sfb-derived-scalar-tensor-identification).
Proof: use step 1 of the node. Resolve the first input P and B[0] by flat K-flat
complexes. The ordinary complex identification is identity on the balanced tensor,
with the symmetry putting B last. Tensoring P with the resolution of B is a
quasi-isomorphism because P is K-flat, even when B is nonflat. The scalar derived
counit is invertible on P. These maps construct h and give the displayed equation.
Naturality descends from the ordinary comparison through the resolving-class
localization. Every derived object has such a representative, so the equation
uniquely determines h, including compatibility with changes of resolutions. -/
theorem derivedTensorIso_existsUnique
    {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B)
    (a : Scheme.ProEtaleTensorModel W A) :
    ∃! h : Scheme.proEtaleRingDerivedExtension φ ⋙ (restriction φ).mapDerivedCategory ≅
        (Functor.curryObj a.tensor).flip.obj
          (DerivedCategory.Q.obj (coefficientComplex φ)),
      IsDerivedTensor φ a h := by
  classical
  let M := proEtaleRingModules W A
  let PR := proEtaleFlatRepresentatives W A
  let L := PR.ι ⋙ (DerivedCategory.Q : CochainComplex M ℤ ⥤ DerivedCategory M)
  let F := proEtaleRingDerivedExtension φ ⋙ (restriction φ).mapDerivedCategory
  let G := (Functor.curryObj a.tensor).flip.obj (DerivedCategory.Q.obj (coefficientComplex φ))
  obtain ⟨b, hb⟩ := representativeScalarTensorIso φ a
  obtain ⟨Q, hQ, q, hq⟩ := coefficientResolution φ
  have : QuasiIso q := hq
  obtain ⟨ff₂⟩ := representativeWhiskering W A
  obtain ⟨ff⟩ := unaryWhiskering L ff₂
  let h : F ≅ G := ff.preimageIso b
  have hi (P : PR.FullSubcategory) : h.inv.app (L.obj P) = b.inv.app P :=
    congr_app (ff.map_preimage b.inv) P
  have hn : IsDerivedTensor φ a h := by
    intro P H hp hH v hv
    change a.representative.hom.app (⟨P, hp⟩, ⟨H, hH⟩) ≫
      a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map v)) ≫
      h.inv.app (L.obj ⟨P, hp⟩) ≫ (scalarCounit φ).app P = _
    rw [hi]
    dsimp only [scalarCounit]
    exact hb P H hp hH v hv
  refine ⟨h, hn, ?_⟩
  intro h' hn'
  have hinv : h'.inv = h.inv := by
    apply ff.map_injective
    ext P
    change h'.inv.app (L.obj P) = h.inv.app (L.obj P)
    have h₁ := hn' P.obj Q P.property hQ q hq
    have h₂ := hn P.obj Q P.property hQ q hq
    have : IsIso (a.tensor.map
        (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P.obj)) (DerivedCategory.Q.map q))) :=
      (a.tensor.mapIso (Iso.prod (Iso.refl _) (asIso (DerivedCategory.Q.map q)))).isIso_hom
    have : IsIso ((scalarCounit φ).app P.obj) :=
      scalarCounit_isIso φ P.obj P.property
    apply (cancel_epi (a.representative.hom.app (P, ⟨Q, hQ⟩) ≫
      a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P.obj))
        (DerivedCategory.Q.map q)))).mp
    apply (cancel_mono ((scalarCounit φ).app P.obj)).mp
    obtain ⟨P, hp⟩ := P
    have hh := h₁.trans h₂.symm
    dsimp only [L, Functor.comp_obj, ObjectProperty.ι_obj, scalarCounit]
    simp only [Category.assoc]
    exact hh
  have his : h'.symm = h.symm := Iso.ext hinv
  exact congrArg Iso.symm his

/-- The comparison h selected by its unique representative normalization.
Source: Stacks 06YY (blueprint: lem-sfb-derived-scalar-tensor-identification). -/
noncomputable def derivedTensorIso
    {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B)
    (a : Scheme.ProEtaleTensorModel W A) :=
  Classical.choose (derivedTensorIso_existsUnique φ a).exists

/-- Literal inverse-image coefficient ring, on the original small site.
Source: Stacks 03EL (blueprint: lem-sfb-derived-scalar-tensor-identification). -/
abbrev inverseRing {Z T : Scheme.{u}} (f : Z ⟶ T)
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj A

/-- Literal inverse-image coefficient map.
Source: Stacks 03EL (blueprint: lem-sfb-derived-scalar-tensor-identification). -/
abbrev inverseMap {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B) :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map a

/-- The canonical exact derived inverse image with identified coefficients.
Source: Stacks 07A6 (blueprint: lem-sfb-derived-scalar-tensor-identification). -/
abbrev pull {Z T : Scheme.{u}} (f : Z ⟶ T)
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  proEtaleRingDerivedPullback f A (inverseRing f A) (Iso.refl _)

/-- The ordinary unbounded derived direct image with identified coefficients.
Source: Stacks 07A6 (blueprint: lem-sfb-derived-scalar-tensor-identification). -/
abbrev push {Z T : Scheme.{u}} (f : Z ⟶ T)
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  proEtaleRingDerivedDirectImage f A (inverseRing f A) (Iso.refl _)

/-- The existing canonical, tensor-unit normalized derived module adjunction.
Source: Stacks 07A6 (blueprint: lem-sfb-derived-scalar-tensor-identification). -/
abbrev adjunction {Z T : Scheme.{u}} (f : Z ⟶ T)
    (A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :=
  proEtaleRingDerivedAdjunction f A (inverseRing f A) (Iso.refl _)

/-- The existing balanced scalar/pullback comparison, in the direction lambda.
It is the inverse mate of the exact restriction square with normalized scalar adjunctions.
Source: Stacks 03EL, 06YY (blueprint: lem-sfb-derived-scalar-tensor-identification). -/
def scalarPullback {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B) :=
  proEtaleReductionPullbackIso f A B (inverseRing f A) (inverseRing f B)
    a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)

/-- The prescribed beta, the geometric adjunction mate of lambda followed by T(epsilon).
Source: Stacks 07A6 (blueprint: lem-sfb-derived-scalar-tensor-identification). -/
def beta {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B) :
    push f A ⋙ proEtaleRingDerivedExtension a ⟶
      proEtaleRingDerivedExtension (inverseMap f a) ⋙ push f B :=
  (mateEquiv (adjunction f A) (adjunction f B) (scalarPullback f a).hom)

/-- The canonical restriction/direct-image comparison d, with its adjunction normalization.
Source: Stacks 0D6E (blueprint: lem-sfb-derived-scalar-tensor-identification). -/
def restrictionPush {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B) :=
  proEtaleRingRestrictionDerivedDirectImage f A B (inverseRing f A) (inverseRing f B)
    a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp)

/-- The ordinary identification f_A^*(r_T B_T) = r_Z B_Z, from the restriction square
and the uniquely unit-normalized pullback of the B-ring module.
Source: Stacks 03EL (blueprint: lem-sfb-derived-scalar-tensor-identification). -/
def coefficientPullback {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B) :=
  (@asIso _ _ _ _
    (proEtaleRingRestrictionPullbackInv f A B (inverseRing f A) (inverseRing f B)
      a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp))
    (proEtaleRingRestrictionPullbackInv_isIso f A B (inverseRing f A) (inverseRing f B)
      a (inverseMap f a) (Iso.refl _) (Iso.refl _) (by simp))).app
        (SheafOfModules.unit ((sheafCompose (ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)) ≪≫
    (restriction (inverseMap f a)).mapIso
      (Classical.choose (proEtaleProjectionUnit_existsUnique f B (inverseRing f B)
        (Iso.refl _)).exists)

/-- The same coefficient identification in the derived category, in degree zero.
Source: Stacks 07A4 (blueprint: lem-sfb-derived-scalar-tensor-identification). -/
def derivedCoefficientPullback {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B) :=
  (proEtaleRingDerivedPullbackFactors f A (inverseRing f A) (Iso.refl _)).app
      (coefficientComplex a) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (proEtaleRingModulePullback f A (inverseRing f A) (Iso.refl _))
        (ComplexShape.up ℤ) 0).app (coefficient a)) ≪≫
    DerivedCategory.Q.mapIso
      ((CochainComplex.singleFunctor (proEtaleRingModules Z (inverseRing f A))
        (0 : ℤ)).mapIso (coefficientPullback f a))

/-- The full isomorphism locus of the prescribed scalar mate.
Source: blueprint, direct-image proof (3)
(blueprint: lem-sfb-derived-scalar-tensor-identification). -/
def locus {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B) :
    ObjectProperty (DerivedCategory (proEtaleRingModules Z (inverseRing f A))) :=
  fun K ↦ IsIso ((beta f a).app K)

/-- Canonical signed-total shifts on the tensor model, using the existing general
representative-normalization predicate, including the unsigned first-factor shift.
Source: Stacks 06YU (blueprint: lem-sfb-derived-scalar-tensor-identification). -/
def CanonicalTensorShifts {W : Scheme.{u}}
    {A : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : ProEtaleTensorModel W A) [(Functor.curryObj a.tensor).CommShift₂Int] : Prop :=
  SheafOfModules.MateCanonicalShiftData (proEtaleOrdinaryTensor W A) DerivedCategory.Q
    a.tensor (proEtaleFlatRepresentatives W A)
    (fun P Q hp hq ↦ a.representative.app (⟨P, hp⟩, ⟨Q, hq⟩))

/-- The source identification e_T after direct image, with the functor associator explicit.
Source: Stacks 06YY (blueprint: lem-sfb-derived-scalar-tensor-identification). -/
def sourceIso {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (t : ProEtaleTensorModel T A) :=
  (Functor.associator (push f A) (proEtaleRingDerivedExtension a)
      (restriction a).mapDerivedCategory) ≪≫
    Functor.isoWhiskerLeft (push f A) (derivedTensorIso a t)

/-- The target identification d followed by e_Z and the canonical pulled-back coefficient
identification, oriented to the exact projection functor.
Source: Stacks 0D6E, 06YY (blueprint: lem-sfb-derived-scalar-tensor-identification). -/
def targetIso {Z T : Scheme.{u}} (f : Z ⟶ T)
    {A B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : A ⟶ B)
    (z : ProEtaleTensorModel Z (inverseRing f A)) :=
  (Functor.associator (proEtaleRingDerivedExtension (inverseMap f a))
    (push f B) (restriction a).mapDerivedCategory) ≪≫
  Functor.isoWhiskerLeft (proEtaleRingDerivedExtension (inverseMap f a))
    (restrictionPush f a) ≪≫
  (Functor.associator (proEtaleRingDerivedExtension (inverseMap f a))
    (restriction (inverseMap f a)).mapDerivedCategory (push f A)).symm ≪≫
  Functor.isoWhiskerRight (derivedTensorIso (inverseMap f a) z) (push f A) ≪≫
  Functor.isoWhiskerRight
    ((Functor.curryObj z.tensor).flip.mapIso (derivedCoefficientPullback f a).symm)
    (push f A)

end AlgebraicGeometry.Scheme.DerivedScalarMate
