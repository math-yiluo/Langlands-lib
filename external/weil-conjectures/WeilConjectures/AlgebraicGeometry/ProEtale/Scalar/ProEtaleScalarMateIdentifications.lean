/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Direct.DirectImageScalarOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionFormulaArrows
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateThickLocus

/-! # Normalized pro-etale scalar mate identifications

## References

* Stacks 0B56
* Stacks 03EK, 06YY
* Stacks 0D6E
* Stacks 03EL, 0D6D
* Stacks 07A4
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The actual scalar restriction, with unchanged underlying abelian sheaf. -/
noncomputable abbrev scalarMateRestriction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u}) :=
  Scheme.proEtaleRingRestrictScalars (Scheme.proEtaleConstantRingMap (T := W) φ)

/-- The coefficient B_W with its A_W action, without deriving or resolving B. -/
noncomputable abbrev scalarMateCoefficient {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u}) :=
  (scalarMateRestriction φ W).obj (SheafOfModules.unit
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing W B)))

/-- The degree-zero coefficient complex B_W, as an A_W-module complex. -/
noncomputable abbrev scalarMateCoefficientComplex {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u}) :=
  (CochainComplex.singleFunctor (Scheme.proEtaleRingModules W
    (Scheme.proEtaleConstantRing W A)) (0 : ℤ)).obj (scalarMateCoefficient φ W)

/-- The existing ordinary tensor with B as its last factor. -/
noncomputable abbrev scalarMateOrdinaryTensor {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u}) :=
  (Scheme.proEtaleOrdinaryTensor W (Scheme.proEtaleConstantRing W A)).flip.obj
    (scalarMateCoefficient φ W)

/-- The original sheafification image of b tensor m in scalar extension. -/
noncomputable def scalarMateTensorSection {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u})
    (M : Scheme.proEtaleRingModules W (Scheme.proEtaleConstantRing W A))
    (U : W.ProEtᵒᵖ) (b : (Scheme.proEtaleConstantRing W B).obj.obj U)
    (m : M.val.obj U) :
    (SheafOfModules.changeOfRings (Scheme.proEtaleConstantRingMap (T := W) φ) M).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (R := (sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing W B))
    (𝟙 _)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
            (Scheme.proEtaleConstantRingMap (T := W) φ) M)).app U)
    (b ⊗ₜ[_, ((Scheme.proEtaleConstantRingMap (T := W) φ).hom.app U).hom] m)

/-- The normalization on all sectionwise pure tensors, including nonconstant local scalars. -/
def IsScalarMateOrdinaryTensor {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u})
    (e : Scheme.proEtaleRingExtension (Scheme.proEtaleConstantRingMap (T := W) φ) ⋙
      scalarMateRestriction φ W ≅ scalarMateOrdinaryTensor φ W) : Prop :=
  ∀ (M : Scheme.proEtaleRingModules W (Scheme.proEtaleConstantRing W A))
    (U : W.ProEtᵒᵖ) (b : (Scheme.proEtaleConstantRing W B).obj.obj U)
    (m : M.val.obj U),
    ((scalarMateRestriction φ W).map
      (eqToHom (Scheme.proEtaleRingExtension_obj
        (Scheme.proEtaleConstantRingMap (T := W) φ) M).symm) ≫
      e.hom.app M).val.app U (scalarMateTensorSection φ W M U b m) =
        Scheme.proEtaleTensorPair W (Scheme.proEtaleConstantRing W A) M
          (scalarMateCoefficient φ W) U m b

/-- The canonical ordinary identification, uniquely fixed by balanced pure tensors. -/
theorem scalarMateOrdinaryTensorIso_existsUnique
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u}) :
    ∃! e : Scheme.proEtaleRingExtension (Scheme.proEtaleConstantRingMap (T := W) φ) ⋙
        scalarMateRestriction φ W ≅ scalarMateOrdinaryTensor φ W,
      IsScalarMateOrdinaryTensor φ W e := by
  exact Scheme.DerivedScalarMate.ordinaryTensorIso_existsUnique
    (Scheme.proEtaleConstantRingMap (T := W) φ)

/-- The uniquely normalized ordinary identification; its data are determined by the formula. -/
noncomputable def scalarMateOrdinaryTensorIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u}) :=
  Classical.choose (scalarMateOrdinaryTensorIso_existsUnique φ W).exists

/-- The canonical restriction/direct-image comparison of the recorded ring-sheaf adjunction. -/
noncomputable def scalarMateRestrictionPush
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {T V : Scheme.{u}} (f : T ⟶ V) :=
  Scheme.proEtaleRingRestrictionDerivedDirectImage f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V B)
    (Scheme.proEtaleConstantRing T A) (Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingMap (T := V) φ)
    (Scheme.proEtaleConstantRingMap (T := T) φ)
    (Scheme.proEtaleConstantRingComparison f A) (Scheme.proEtaleConstantRingComparison f B)
    (Scheme.proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm

/-- On complexes, reverse the balanced tensors degreewise and use the degree-zero
single-factor identification. This is an actual chain isomorphism. -/
noncomputable def scalarMateOrdinaryComplexIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u})
    (P : CochainComplex (Scheme.proEtaleRingModules W (Scheme.proEtaleConstantRing W A)) ℤ) :=
  (Functor.mapHomologicalComplexCompIso (scalarMateOrdinaryTensorIso φ W)
    (ComplexShape.up ℤ)).app P ≪≫
      (CochainComplex.mapBifunctorSingle₂Iso
        (Scheme.proEtaleOrdinaryTensor W (Scheme.proEtaleConstantRing W A))
        (scalarMateCoefficient φ W) P).symm

/-- The full normalization of h on two flat K-flat representatives, resolving B too.
The equation uses Q → B[0] only after tensoring with the K-flat first factor. -/
def IsScalarMateDerivedTensor {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (W : Scheme.{u})
    (a : Scheme.ProEtaleTensorModel W (Scheme.proEtaleConstantRing W A))
    (h : directImageScalarExtension φ W ⋙ (scalarMateRestriction φ W).mapDerivedCategory ≅
      (Functor.curryObj a.tensor).flip.obj
        (DerivedCategory.Q.obj (scalarMateCoefficientComplex φ W))) : Prop :=
  ∀ (P Q : CochainComplex (Scheme.proEtaleRingModules W
      (Scheme.proEtaleConstantRing W A)) ℤ)
    (hp : Scheme.proEtaleFlatRepresentatives W (Scheme.proEtaleConstantRing W A) P)
    (hq : Scheme.proEtaleFlatRepresentatives W (Scheme.proEtaleConstantRing W A) Q)
    (q : Q ⟶ scalarMateCoefficientComplex φ W), QuasiIso q →
    a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
      a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q)) ≫
      h.inv.app (DerivedCategory.Q.obj P) ≫
      (scalarMateRestriction φ W).mapDerivedCategory.map
        (cast (by rfl) ((Scheme.proEtaleRingDerivedExtensionCounit
          (Scheme.proEtaleConstantRingMap (T := W) φ)).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) ≫
      (scalarMateRestriction φ W).mapDerivedCategoryFactorsh.hom.app
        (((Scheme.proEtaleRingExtension
          (Scheme.proEtaleConstantRingMap (T := W) φ)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) =
    cast (by rfl) (DerivedCategory.Q.map
      (HomologicalComplex.mapBifunctorMap (𝟙 P) q
        (Scheme.proEtaleOrdinaryTensor W (Scheme.proEtaleConstantRing W A))
        (ComplexShape.up ℤ) ≫ (scalarMateOrdinaryComplexIso φ W P).inv))

/-- The restricted extension is the derived tensor with B, with its full normalization. -/
theorem scalarMateDerivedTensorIso_existsUnique
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u})
    (a : Scheme.ProEtaleTensorModel W (Scheme.proEtaleConstantRing W A)) :
    ∃! h : directImageScalarExtension φ W ⋙ (scalarMateRestriction φ W).mapDerivedCategory ≅
        (Functor.curryObj a.tensor).flip.obj
          (DerivedCategory.Q.obj (scalarMateCoefficientComplex φ W)),
      IsScalarMateDerivedTensor φ W a h := by
  exact Scheme.DerivedScalarMate.derivedTensorIso_existsUnique
    (Scheme.proEtaleConstantRingMap (T := W) φ) a

/-- The comparison h selected by its unique representative normalization. -/
noncomputable def scalarMateDerivedTensorIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (W : Scheme.{u})
    (a : Scheme.ProEtaleTensorModel W (Scheme.proEtaleConstantRing W A)) :=
  Classical.choose (scalarMateDerivedTensorIso_existsUnique φ W a).exists

/-- The tensor unit in the existing constant-ring module category. -/
noncomputable abbrev scalarMateUnit (B : Type u) [CommRing B] (W : Scheme.{u}) :=
  SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing W B))

/-- The normalized ordinary B-unit pullback, supplied by the projection-arrow interface. -/
noncomputable def scalarMateUnitPullback (B : Type u) [CommRing B]
    {T V : Scheme.{u}} (f : T ⟶ V) :=
  Classical.choose (Scheme.proEtaleProjectionUnit_existsUnique f
    (Scheme.proEtaleConstantRing V B) (Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingComparison f B)).exists

/-- The ordinary identification u_A^*(B_V)=B_T, using scalar restriction and unit pullback. -/
noncomputable def scalarMateCoefficientPullback
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {T V : Scheme.{u}} (f : T ⟶ V) :=
  letI := Scheme.proEtaleRingRestrictionPullbackInv_isIso f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V B)
    (Scheme.proEtaleConstantRing T A) (Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingMap (T := V) φ)
    (Scheme.proEtaleConstantRingMap (T := T) φ)
    (Scheme.proEtaleConstantRingComparison f A) (Scheme.proEtaleConstantRingComparison f B)
    (Scheme.proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm
  (asIso (Scheme.proEtaleRingRestrictionPullbackInv f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing V B)
    (Scheme.proEtaleConstantRing T A) (Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingMap (T := V) φ)
    (Scheme.proEtaleConstantRingMap (T := T) φ)
    (Scheme.proEtaleConstantRingComparison f A) (Scheme.proEtaleConstantRingComparison f B)
    (Scheme.proEtaleConstantInverseImageMap_naturality f
      (CommRingCat.ofHom (RingHom.ulift φ))).symm)).app (scalarMateUnit B V) ≪≫
    (scalarMateRestriction φ T).mapIso (scalarMateUnitPullback B f)

/-- The coefficient identification on degree-zero complexes, with exact pullback factors. -/
noncomputable def scalarMateDerivedCoefficientPullback
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    {T V : Scheme.{u}} (f : T ⟶ V) :=
  (Scheme.proEtaleRingDerivedPullbackFactors f
    (Scheme.proEtaleConstantRing V A) (Scheme.proEtaleConstantRing T A)
    (Scheme.proEtaleConstantRingComparison f A)).app (scalarMateCoefficientComplex φ V) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.proEtaleConstantRingPullback A f) (ComplexShape.up ℤ) 0).app
          (scalarMateCoefficient φ V)) ≪≫
    DerivedCategory.Q.mapIso
      ((CochainComplex.singleFunctor
        (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A)) (0 : ℤ)).mapIso
          (scalarMateCoefficientPullback φ f))

end AlgebraicGeometry.ProEtale
