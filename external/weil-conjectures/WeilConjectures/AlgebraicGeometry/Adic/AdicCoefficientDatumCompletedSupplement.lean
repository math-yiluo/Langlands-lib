/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantFiniteComplexRealization
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
import WeilConjectures.Algebra.Homology.Scalar.ScalarHomExtensionKFlat
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantFiniteComplexRealization
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumCompleted

/-!
# Completed adic coefficient datum and its strict reduction tower

Source: blueprint, proper base change, order 1239; Stacks Tags 099L and 099M
(blueprint: def-weil-pbc-adic-coefficient-datum).

The site has object universe t+1 and morphism universe t. Coefficients and modules
are in t+1. The ambient ring is the actual inverse limit of the finite constant
quotient sheaves, not the constant sheaf associated to the original ring.

## Main definitions

* `ProEtaleAdicCoefficientDatum`: coefficient hypotheses.
* `adicDatumRing`: the actual completed coefficient sheaf.
* `adicDatumAdjunction`: normalized derived scalar adjunction.
* `adicDatumDerivedTower`: universal strict quotient tower.
* `adicDatumModelTower`: its explicit K-flat computation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t r u v uC vC wC uD vD wD

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory

attribute [local irreducible] Functor.mapHomotopyCategory
  Functor.mapHomotopyCategoryFactors

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

section FiniteCoefficientComparison
variable (P : Type (t + 1)) [CommRing P] [Finite P]
variable [TopologicalSpace P] [DiscreteTopology P]

end FiniteCoefficientComparison

/-- The ambient unbounded derived category, with the standard localization.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumDerived := completedConstantDerived (adicDatumModules T d)

section ScalarChange

variable {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)

/-- The two presentations select the same ordinary tensor functor.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: both are the ordinary functor in the same independent-coefficient witness,
with the same standard derived-category instances. -/
theorem adicDatumOrdinaryExtension_eq :
    completedConstantExtension T φ = reductionChange T φ := by
  rfl

/-- The homotopy localization with the same standard derived-category instance.
Source: Tag 05RU (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumQh (B : Sheaf (ProEt.topology T) CommRingCat.{t + 1}) :=
  @DerivedCategory.Qh (completedConstantModules T B) _ _ (HasDerivedCategory.standard _)

/-- The scalar derived pair with its specification stated in this coefficient presentation.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: take the universal pair in derivedChangeOfRingsIndependentCoefficients, using
its specified ordinary extension functor and the standard localizations. -/
theorem adicDatumScalarDerived_exists :
    ∃ (F : completedConstantDerived (completedConstantModules T R) ⥤
        completedConstantDerived (completedConstantModules T S))
      (ε : adicDatumQh T R ⋙ F ⟶
        (reductionChange T φ).mapHomotopyCategory (.up ℤ) ⋙ adicDatumQh T S),
      F.IsLeftDerivedFunctor ε
          (HomotopyCategory.quasiIso (completedConstantModules T R) (.up ℤ)) ∧
        (∃ (_ : F.CommShift ℤ), F.IsTriangulated) ∧
        ∀ C : CochainComplex (completedConstantModules T R) ℤ,
          CochainComplex.IsKFlatIndependentCoefficients (R := R) C →
          IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj C)) := by
  change ∃ F, reductionDerivedSpec T φ F
  exact reductionDerivedExistence T φ

/-- The universal scalar pair as data, retaining its counit and K-flat computation.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
structure AdicDatumScalarPair where
  functor : completedConstantDerived (completedConstantModules T R) ⥤
    completedConstantDerived (completedConstantModules T S)
  counit : adicDatumQh T R ⋙ functor ⟶
    (reductionChange T φ).mapHomotopyCategory (.up ℤ) ⋙ adicDatumQh T S
  universal : functor.IsLeftDerivedFunctor counit
    (HomotopyCategory.quasiIso (completedConstantModules T R) (.up ℤ))
  triangulated : ∃ (_ : functor.CommShift ℤ), functor.IsTriangulated
  computation (C : CochainComplex (completedConstantModules T R) ℤ)
    (hC : CochainComplex.IsKFlatIndependentCoefficients (R := R) C) :
    IsIso (counit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj C))

/-- The specified universal pair, packaged once so its fields have a stable interface.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum). -/
@[irreducible]
def adicDatumScalarPair : AdicDatumScalarPair T φ where
  functor := (adicDatumScalarDerived_exists T φ).choose
  counit := (adicDatumScalarDerived_exists T φ).choose_spec.choose
  universal := (adicDatumScalarDerived_exists T φ).choose_spec.choose_spec.1
  triangulated := (adicDatumScalarDerived_exists T φ).choose_spec.choose_spec.2.1
  computation := (adicDatumScalarDerived_exists T φ).choose_spec.choose_spec.2.2

private theorem completedExtension_obj (M : completedConstantModules T R) :
    (reductionChange T φ).obj M = SheafOfModules.changeOfRings φ M :=
  reductionChange_obj_eq T φ M

private theorem completedExtension_map {M N : completedConstantModules T R} (a : M ⟶ N) :
    (reductionChange T φ).map a =
      eqToHom (completedExtension_obj T φ M) ≫ SheafOfModules.changeOfRingsHom φ M a ≫
        eqToHom (completedExtension_obj T φ N).symm :=
  reductionChange_map_eq T φ a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem adicDatumOrdinaryAdjunction_formula :
    ∃ a : reductionChange T φ ⊣
        SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ),
      ∀ (M : completedConstantModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x = adicDatumTensorSection T φ M U 1 x := by
  refine ⟨(ordinaryAdjunction_exists T φ).choose, ?_⟩
  intro M U x
  exact reductionUnit_apply T φ M U x

end ScalarChange

/-- The actual limit projection to the positive quotient level n+1.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumProjection (n : ℕ) :
    adicDatumRing T d ⟶ (adicLisseRingSystem T d.ideal).obj (op n) :=
  limit.π (adicLisseRingSystem T d.ideal) (op n)

attribute [local irreducible] adicDatumRing adicLisseRingSystem

attribute [local instance 20000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- The existing module-sheaf Abelian structure with a variable site.
Keeping the site variable retains the coefficient-universe proof arguments directly.
Source: Stacks 03DA (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumSiteModulesAbelian {B : Type (t + 1)} [Category.{t} B]
    [EssentiallySmall.{t + 1} B] (J : GrothendieckTopology B)
    (R : Sheaf J RingCat.{t + 1}) : Abelian (SheafOfModules.{t + 1} R) := inferInstance

/-- The existing Abelian structure with the geometric coefficient-universe instance.
This fixed data interface prevents implicit instance choices from unfolding the
large sheafification construction in derived comparison types.
Source: Stacks 03DA (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumModulesAbelian (U : Scheme.{t})
    (R : Sheaf (ProEt.topology U) CommRingCat.{t + 1}) :
    Abelian (proEtaleRingModules U R) :=
  adicDatumSiteModulesAbelian (ProEt.topology U)
    ((sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)

attribute [local instance 40000] adicDatumModulesAbelian
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory


section Balancing
variable {R S B : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
variable (φ : R ⟶ S) (ψ : S ⟶ B)

section GenericKFlatTransport

open SheafOfModules

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Transport K-flat preservation from an existing normalized scalar pair.
Source: Stacks Tag 0G7E (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the scalar pair exists by the universal derived scalar adjunction. Its
ordinary object and map formulas identify its extension functor with E by functor
extensionality. Apply scalarExtension_preservesKFlat to that functor. -/
private theorem adicDatumExtension_kflat_site
    {D : Type u} [Category.{v} D] [EssentiallySmall.{r} D]
    {J : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasWeakSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} (ρ : R ⟶ S)
    (E : SheafOfModules.{r} ((sheafCompose J
        (forget₂ CommRingCat.{r} RingCat.{r})).obj R) ⥤
      SheafOfModules.{r} ((sheafCompose J
        (forget₂ CommRingCat.{r} RingCat.{r})).obj S))
    [E.Additive] (h : ∀ M, E.obj M = changeOfRings ρ M)
    (hm : ∀ {M N} (g : M ⟶ N), E.map g =
      eqToHom (h M) ≫ changeOfRingsHom ρ M g ≫ eqToHom (h N).symm)
    (K : CochainComplex (SheafOfModules.{r} ((sheafCompose J
      (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (R := R) K) :
    CochainComplex.IsKFlatIndependentCoefficients (R := S)
      ((E.mapHomologicalComplex (.up ℤ)).obj K) := by
  let := HasDerivedCategory.standard (scalarModules J R)
  let := HasDerivedCategory.standard (scalarModules J S)
  obtain ⟨s⟩ := scalarDerivedPair_exists ρ
  have hE : s.extension = E := by
    refine CategoryTheory.Functor.ext
      (fun M ↦ (s.extension_obj M).trans (h M).symm) ?_
    intro M N f
    rw [s.extension_map, hm]
    simp
  cases hE
  exact scalarExtension_preservesKFlat ρ s K hK

end GenericKFlatTransport

open SheafOfModules MonoidalCategory in
/-- K-flatness survives ordinary extension, with no flatness hypothesis on the ring map.
Source: order 1239; Tag 06YY (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: tensor an acyclic S-complex N with the extended R-complex. Balancing identifies
it with the tensor of the original K-flat complex and the restricted N. Restriction
is exact, so the latter is acyclic. This is exactly the K-flatness criterion over S. -/
theorem adicDatumExtension_kflat (C : CochainComplex (completedConstantModules T R) ℤ)
    (hC : CochainComplex.IsAcyclicTensorKFlat (R := R) C) :
    CochainComplex.IsAcyclicTensorKFlat (R := S)
      (((reductionChange T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) := by
  apply (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1
  exact adicDatumExtension_kflat_site φ (reductionChange T φ)
    (completedExtension_obj T φ) (completedExtension_map T φ) C
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat C).2 hC)

end Balancing

end AlgebraicGeometry.Scheme
