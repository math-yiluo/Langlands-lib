/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.HomologicalComplex
public import WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealization.AdmissibleScalarRealizationExactSupplement
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Sites.Localization
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.AlgebraicGeometry.InverseImageModuleFlat
import WeilConjectures.Algebra.Homology.FlatTermKFlatFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ExtensionIsoQuotientFormula

/-! # Normalized constant-to-integral coefficient pullback

Constant coefficients are represented by their canonical pullback from the point;
constantSchemeIso identifies them with ordinary constant sheaves. All complexes are
integer-indexed and unrestricted. The quotient clause is the pushout description
R tensor_C (C/pi^n) = R/pi^n, including the prescribed quotient projection.

## References

* Stacks 093J
* Stacks 03CS
* Stacks 06YN and 03ER
* Stacks 093M and 0G7E
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralCoefficientSquare

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The discrete constant ring on the point, with its existing monoidal ring structure. -/
abbrev constantPoint :=
  (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} A))

/-- Internal modules over the specified coefficients pulled back to a scheme. -/
abbrev Modules (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (T : Scheme.{u}) := Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T)

/-- The constant-to-continuous map pulled back from the point; no completion choice. -/
abbrev scalar (T : Scheme.{u}) := AdmissibleScalarRealization.scalarMap A T

/-- Restriction along the specified constant-function map, on all modules. -/
abbrev restriction (T : Scheme.{u}) :
    Modules (Profinite.continuousCoefficientRingObj A) T ⥤ Modules (constantPoint A) T :=
  Mod.comap (scalar A T)

/-- Termwise restriction, retaining the original differential. -/
abbrev restrictComplex (T : Scheme.{u}) :=
  (restriction A T).mapHomologicalComplex (.up ℤ)

/-- The tensor-defined module pullback, applied in every degree. -/
abbrev pullComplex (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  (CondensedRing.upperStar Λ g).mapHomologicalComplex (.up ℤ)

/-- The specified extension-to-inverse-image identification on underlying abelian sheaves. -/
def underlyingIso (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Modules Λ Y) :
    ((CondensedRing.upperStar Λ g).obj M).X ≅
      (upperStar Ab.{u + 1} g).obj M.X :=
  (Mod.forget (condensedRingObj Λ X)).mapIso
    ((cartesianCoefficientPullbackIso Λ g).app M)

/-- Both generator formulas fixing the underlying Cartesian scalar-extension isomorphism.
The first sends r tensor h to alpha inverse(r)h; the second sends h to 1 tensor h. -/
def GeneratorNormalization (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) : Prop :=
  ∀ M : Modules Λ Y,
    Mod.extendπ (condensedPullbackHom Λ g)
        (((upperStar Ab.{u + 1} g).mapMod _).obj M) ≫ (underlyingIso Λ g M).hom =
      inv (condensedPullbackHom Λ g) ▷ (upperStar Ab.{u + 1} g).obj M.X ≫
        γ[(upperStar Ab.{u + 1} g).obj (condensedRingObj Λ Y),
          (upperStar Ab.{u + 1} g).obj M.X] ∧
    (underlyingIso Λ g M).inv = Mod.extendUnitHom (condensedPullbackHom Λ g)
      (((upperStar Ab.{u + 1} g).mapMod _).obj M)

/-- K-flatness and flat terms in the existing section-module presentation.
This uses the recorded predicates, rather than another definition of K-flatness or flatness. -/
def FlatKFlat (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    (P : CochainComplex (Modules Λ T) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients
    (((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
      (condensedRingObj Λ T)).functor.mapHomologicalComplex (.up ℤ)).obj P) ∧
  ∀ q : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
    ((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
      (condensedRingObj Λ T)).functor.obj (P.X q))

/-- The actual completed ring, identified by its constant scalar projections, with its
normalized quotient squares. The pushout is precisely the ring quotient by pi^(n+1). -/
def RingAssertions (p : A) (T : Scheme.{u}) : Prop :=
  ∃ e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T)
      (condensedRingObj (Profinite.continuousCoefficientRingObj A) T) ≅
      Scheme.adicLisseCompletedRing T
        (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))),
    (∀ (U : T.ProEtᵒᵖ) (a : A) (n : ℕ),
      ((limit.π (Scheme.adicLisseRingSystem T
        (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)))) (op n)).hom.app U)
        ((e.hom.hom.app U)
          ((FiniteDiscreteOrdinary.canonicalAbelianMap A T).hom.app U
            ((toSheafify (D := Ab.{u + 1}) (Scheme.ProEt.topology T)
              ((Functor.const T.ProEtᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{u + 1} A)))).app U (ULift.up a)))) =
      (toSheafify (D := CommRingCat.{u + 1}) (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
          (ULift.{u + 1} A ⧸
            Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)) ^ (n + 1))))).app U
        (Ideal.Quotient.mk
          (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)) ^ (n + 1)) (ULift.up a))) ∧
    ∀ n : ℕ, IsPushout
      (Scheme.CompletedConstantReduction.base T
        (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A))) ≫ e.inv)
      ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk
          (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)) ^ (n + 1)))))
      (e.hom ≫ limit.π (Scheme.adicLisseRingSystem T
        (Ideal.span ({ULift.up p} : Set (ULift.{u + 1} A)))) (op n)) (𝟙 _)

/-- All clauses for the actual coefficient ring, square, chain comparison and flat K-flat
pullbacks. The natural isomorphism is on whole cochain complexes, with normalization in
all integer degrees; there is no boundedness, completeness or constructibility condition. -/
def Assertions (p : A) {X Y : Scheme.{u}} (g : X ⟶ Y) : Prop :=
  RingAssertions A p X ∧ RingAssertions A p Y ∧
  (∀ T : Scheme.{u}, T = X ∨ T = Y → SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
    ((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
      (condensedRingObj (constantPoint A) T)).functor.obj
      ((restriction A T).obj
        (Mod.regular (condensedRingObj (Profinite.continuousCoefficientRingObj A) T))))) ∧
  (upperStar Ab.{u + 1} g).map (scalar A Y) ≫
      condensedPullbackHom (Profinite.continuousCoefficientRingObj A) g =
    condensedPullbackHom (constantPoint A) g ≫ scalar A X ∧
  GeneratorNormalization (Profinite.continuousCoefficientRingObj A) g ∧
  GeneratorNormalization (constantPoint A) g ∧
  (∃ d : pullComplex (Profinite.continuousCoefficientRingObj A) g ⋙ restrictComplex A X ≅
      restrictComplex A Y ⋙ pullComplex (constantPoint A) g,
    ∀ (H : CochainComplex (Modules (Profinite.continuousCoefficientRingObj A) Y) ℤ)
      (q : ℤ),
      ((d.hom.app H).f q).hom ≫
          (underlyingIso (constantPoint A) g ((restriction A Y).obj (H.X q))).hom =
        (underlyingIso (Profinite.continuousCoefficientRingObj A) g (H.X q)).hom) ∧
  exactFunctor _ _ (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A) g) ∧
  exactFunctor _ _ (CondensedRing.upperStar (constantPoint A) g) ∧
  ∀ P : CochainComplex (Modules (Profinite.continuousCoefficientRingObj A) Y) ℤ,
    FlatKFlat (Profinite.continuousCoefficientRingObj A) Y P →
    FlatKFlat (constantPoint A) Y ((restrictComplex A Y).obj P) ∧
    FlatKFlat (Profinite.continuousCoefficientRingObj A) X
      ((pullComplex (Profinite.continuousCoefficientRingObj A) g).obj P) ∧
    FlatKFlat (constantPoint A) X
      ((pullComplex (constantPoint A) g).obj ((restrictComplex A Y).obj P))

attribute [local irreducible] Mod.extendScalarsObj Mod.extendScalarsIsoComapInv
attribute [local irreducible] upperStarFromPoint upperStarFromPointComp upperStar
attribute [local irreducible] FiniteConstantModel.scalarToContinuous
set_option backward.isDefEq.respectTransparency.types false

private theorem generators
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    GeneratorNormalization Λ g := by
  intro M
  have h := Mod.extensionIso_quotient_formula (condensedPullbackHom Λ g)
    (((upperStar Ab.{u + 1} g).mapMod (condensedRingObj Λ Y)).obj M)
  exact ⟨h.2.1, h.2.2.2.1⟩

private def pointScalar : constantPoint A ⟶ Profinite.continuousCoefficientRingObj A :=
  FiniteConstantModel.scalarToContinuous A

private instance pointScalar_isMonHom : IsMonHom (pointScalar A) :=
  inferInstanceAs (IsMonHom (FiniteConstantModel.scalarToContinuous A))

private theorem scalar_square_general
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [MonObj Λ'] (a : Λ ⟶ Λ')
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (upperStar Ab.{u + 1} g).map ((upperStarFromPoint Y).map a) ≫
        condensedPullbackHom Λ' g =
      condensedPullbackHom Λ g ≫ (upperStarFromPoint X).map a :=
  (upperStarFromPointComp g).hom.naturality a

section Comparison
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a] {X Y : Scheme.{u}} (g : X ⟶ Y)

omit [IsCommMonObj Λ] [IsCommMonObj Λ'] [IsMonHom a] in
private theorem inverse_square_general :
    (upperStarFromPoint X).map a ≫ inv (condensedPullbackHom Λ' g) =
      inv (condensedPullbackHom Λ g) ≫
        (upperStar Ab.{u + 1} g).map ((upperStarFromPoint Y).map a) := by
  apply (cancel_epi (condensedPullbackHom Λ g)).mp
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [← scalar_square_general a g, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private def comparisonGeneral :
    CondensedRing.upperStar Λ' g ⋙ Mod.comap ((upperStarFromPoint X).map a) ≅
      Mod.comap ((upperStarFromPoint Y).map a) ⋙ CondensedRing.upperStar Λ g :=
  Functor.isoWhiskerRight (cartesianCoefficientPullbackIso Λ' g)
      (Mod.comap ((upperStarFromPoint X).map a)) ≪≫
    Mod.comapMapModComapIso (upperStar Ab.{u + 1} g)
      ((upperStarFromPoint Y).map a) ((upperStarFromPoint X).map a)
      (inv (condensedPullbackHom Λ g)) (inv (condensedPullbackHom Λ' g))
      (inverse_square_general a g) ≪≫
    Functor.isoWhiskerLeft (Mod.comap ((upperStarFromPoint Y).map a))
      (cartesianCoefficientPullbackIso Λ g).symm

end Comparison

private theorem scalar_square {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (upperStar Ab.{u + 1} g).map (scalar A Y) ≫
        condensedPullbackHom (Profinite.continuousCoefficientRingObj A) g =
      condensedPullbackHom (constantPoint A) g ≫ scalar A X :=
  scalar_square_general (pointScalar A) g

private def moduleComparison {X Y : Scheme.{u}} (g : X ⟶ Y) :
    CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A) g ⋙ restriction A X ≅
      restriction A Y ⋙ CondensedRing.upperStar (constantPoint A) g :=
  comparisonGeneral (pointScalar A) g

private theorem flat_restricted_regular
    (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [PreservesFiniteLimits (Mod.extendScalars φ)] :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      ((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology T)
        R).functor.obj ((Mod.comap φ).obj (Mod.regular S))) := by
  let N := (Mod.comap φ).obj (Mod.regular S)
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft N ⋙ Mod.forget R) :=
    preservesFiniteLimits_of_natIso (Mod.extendForgetTensorIso φ)
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft N) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (Mod.forget R)
  exact (InternalAbelianSheafModule.flat_iff_sectionModule
    (Scheme.ProEt.topology T) R N).mp
      ((ObjectProperty.flat_iff_preservesFiniteLimits N).mpr inferInstance)

universe v w

private theorem internal_kflat_iff
    {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    (K : CochainComplex C ℤ) :
    (∀ P : CochainComplex C ℤ, P.Acyclic →
      (CochainComplex.mapBifunctor P K (curriedTensor C)).Acyclic) ↔
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff, HomotopyCategory.kFlat_iff_preserves_acyclic]
  constructor
  · intro h Z hZ
    obtain ⟨Z, rfl⟩ := Z.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hZ
    have hr := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (CochainComplex.mapBifunctor Z K (curriedTensor C))).2 (h Z hZ)
    exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hr, hr⟩
  · intro h P hP
    exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
      (h _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic P).2 hP)).2

end AlgebraicGeometry.ProEtale.IntegralCoefficientSquare
