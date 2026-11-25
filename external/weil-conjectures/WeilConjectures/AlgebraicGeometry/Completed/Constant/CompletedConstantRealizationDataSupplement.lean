/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
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
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.AlgebraicGeometry.CompletedConstantRealizationData
/-! # Data for completed constant realization

Source: Stacks Tags 093J--093M and 06YU.
(blueprint: def-weil-pbc-completed-constant-realization-data).

The constructions and interfaces are moved verbatim from
`CompletedConstantFiniteComplexRealization` so that the module and complex calculations
can be stated independently without an import cycle.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u v w vD vE
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme
/-- The localization functor for `completedConstantDerived`.
Source: Stacks Tag 05RU
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
abbrev completedConstantQ (D : Type v) [Category.{w} D] [Abelian D] :
    CochainComplex D ℤ ⥤ completedConstantDerived D :=
  @DerivedCategory.Q D _ _ (HasDerivedCategory.standard D)
/-- The finite module subcategory, so exactness refers to its finite limits and colimits.
Source: Stacks Tag 00MB
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def completedConstantFiniteModules (A : Type (u + 1)) [CommRing A] :
    ObjectProperty (ModuleCat.{u + 1} A) :=
  fun N ↦ Module.Finite A N
/-- The quotient module over a ring mapping to the completed coefficient sheaf.
Source: Stacks Tag 06YU, restriction along the quotient projection
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
abbrev completedConstantQuotient (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) (n : ℕᵒᵖ) :=
  (SheafOfModules.restrictScalars.{u + 1}
    ((adicLisseForget X).map (β ≫ limit.π (adicLisseRingSystem X I) n))).obj
      (SheafOfModules.unit ((adicLisseForget X).obj ((adicLisseRingSystem X I).obj n)))
/-- A quotient diagram with the actual quotient maps, characterized on every section.
`level` and `transition` fix all objects and arrows; this is no arbitrary diagram.
Source: Stacks Tags 093M and 06YU, proof steps 5--8
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
structure CompletedConstantQuotientTower (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) where
  diagram : ℕᵒᵖ ⥤ completedConstantModules X R
  level : ∀ n : ℕᵒᵖ, diagram.obj n = completedConstantQuotient X I R β n
  transition : ∀ (m n : ℕᵒᵖ) (g : m ⟶ n) (U : X.ProEtᵒᵖ)
      (x : ((adicLisseRingSystem X I).obj m).obj.obj U),
    ((eqToHom (level m).symm ≫ diagram.map g ≫ eqToHom (level n)).val.app U) x =
      ((adicLisseRingSystem X I).map g).hom.app U x
/-- The total tensor bifunctor, using the existing monoidal structure and total differential.
Source: Stacks Tags 06YN and 06YU
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def completedConstantTensor (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    CochainComplex (completedConstantModules X R) ℤ ⥤
      CochainComplex (completedConstantModules X R) ℤ ⥤
        CochainComplex (completedConstantModules X R) ℤ :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients R
  letI := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  letI := SheafOfModules.symmetricCategory R
  letI : HasCoproducts.{0} (completedConstantModules X R) := inferInstance
  (MonoidalCategory.curriedTensor _).map₂CochainComplex
/-- Completed realization by extension of the constant completion ring to completed
sheaf scalars. The theorem identifies this actual tensor construction with the limit.
Source: Stacks Tag 093M and proof step 2
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def completedConstantRealization (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I) :=
  adicLisseConstantModules X (AdicCompletion I A) ⋙ completedConstantExtension X φ
/-- A finite reduction on complexes: tensor the module complex with `P_(n+1)`,
make it constant, and restrict its scalars along the specified projection.
Source: Stacks Tag 06YU, proof step 5
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def completedConstantReductionLevel (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I) (n : ℕ)
    (h : (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).Additive) :
    CochainComplex (ModuleCat.{u + 1} (AdicCompletion I A)) ℤ ⥤
      CochainComplex (completedConstantModules X R) ℤ :=
  letI := h
  letI := (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1}
    (AdicCompletion.evalₐ I (n + 1)).toRingHom).isLeftAdjoint
  (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (AdicCompletion.evalₐ I (n + 1)).toRingHom ⋙
    adicLisseConstantModules X (A ⧸ I ^ (n + 1)) ⋙
    SheafOfModules.restrictScalars.{u + 1} ((adicLisseForget X).map
      (β ≫ limit.π (adicLisseRingSystem X I) (op n)))).mapHomologicalComplex
        (ComplexShape.up ℤ)
/-- Constant reductions, with all quotient transitions fixed on tensor generators.
Applied to a bounded-above finite-free resolution F, this represents precisely
`underline(Q tensor^L_C P_n)`, with its specified R-action. The generator condition
prevents replacing quotient transitions by arbitrary maps.
Source: Stacks Tag 06YU, proof steps 5 and 8
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
structure CompletedConstantReductionTower (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (β : R ⟶ adicLisseCompletedRing X I)
    (h : ∀ n : ℕ, (adicLisseConstantModules X (A ⧸ I ^ (n + 1))).Additive) where
  functor : CochainComplex (ModuleCat.{u + 1} (AdicCompletion I A)) ℤ ⥤
    (ℕᵒᵖ ⥤ CochainComplex (completedConstantModules X R) ℤ)
  level : ∀ (F : CochainComplex (ModuleCat.{u + 1} (AdicCompletion I A)) ℤ) (n : ℕ),
    (functor.obj F).obj (op n) = (completedConstantReductionLevel X I R β n (h n)).obj F
  map_level : ∀ (F G : CochainComplex (ModuleCat.{u + 1} (AdicCompletion I A)) ℤ)
      (f : F ⟶ G) (n : ℕ),
    eqToHom (level F n).symm ≫ (functor.map f).app (op n) ≫ eqToHom (level G n) =
      (completedConstantReductionLevel X I R β n (h n)).map f
  transition : ∀ (F : CochainComplex (ModuleCat.{u + 1} (AdicCompletion I A)) ℤ)
      (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ) (p : A ⧸ I ^ (n + 2)) (x : F.X i),
    (((eqToHom (level F (n + 1)).symm ≫ (functor.obj F).map
        (homOfLE (Nat.le_succ n)).op ≫ eqToHom (level F n)).f i).val.app U)
      (completedConstantGenerator X _
        ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (AdicCompletion.evalₐ I (n + 2)).toRingHom).obj
          (F.X i))
        U (p ⊗ₜ[(AdicCompletion I A), (AdicCompletion.evalₐ I (n + 2)).toRingHom] x)) =
      completedConstantGenerator X _
        ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
          (AdicCompletion.evalₐ I (n + 1)).toRingHom).obj
          (F.X i))
        U ((Ideal.Quotient.factorPowSucc I (n + 1) p) ⊗ₜ[(AdicCompletion I A),
          (AdicCompletion.evalₐ I (n + 1)).toRingHom] x)
/-- Restrict a completion-module to A. On this module I^n N = (IC)^n N, so its
quotient and completed constant sheaf are exactly those in the node's statement.
Source: Stacks Tag 00MA, proof step 1
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
abbrev completedConstantUnderlyingModule {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (N : ModuleCat.{u + 1} (AdicCompletion I A)) :=
  (ModuleCat.restrictScalars.{u + 1} (algebraMap A (AdicCompletion I A))).obj N
/-- The A-linear map on the actual quotients induced by an A-linear map.
Source: Stacks Tag 093J and the componentwise limit construction
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def completedConstantQuotientMap {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) {M N : ModuleCat.{u + 1} A} (f : M ⟶ N) (n : ℕ) :
    ModuleCat.of A (M ⧸ (I ^ (n + 1) • ⊤ : Submodule A M)) ⟶
      ModuleCat.of A (N ⧸ (I ^ (n + 1) • ⊤ : Submodule A N)) :=
  ModuleCat.ofHom ((f.hom.reduceModIdeal (I ^ (n + 1))).restrictScalars A)
/-- The constant A-action on the completed coefficient ring.
Source: Stacks Tag 093M and the limit projections
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
def completedConstantBaseMap (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A)
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I) :=
  ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (algebraMap A (AdicCompletion I A)))) ≫ φ
/-- The module-level assertions and the specified realization isomorphisms.
The limit is formed from the dependency's actual quotient-module system. Its
linearity condition fixes the completed-scalar action on every finite projection;
naturality fixes the maps of the realization functor. Restriction to A changes
no quotient: I^n N = (IC)^n N for a C-module.
Source: Stacks Tags 093J--093M, 09BT, and 09BV, proof steps 1--3
(blueprint: def-weil-pbc-completed-constant-realization-data). -/
structure CompletedConstantModuleRealization (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A] (I : Ideal A) where
  scalar : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I
  scalar_projection : ∀ n : ℕ,
    scalar ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom)
  additive : (completedConstantRealization X I scalar).Additive
  exact_finite :
    PreservesFiniteLimits ((completedConstantFiniteModules (AdicCompletion I A)).ι ⋙
      completedConstantRealization X I scalar) ∧
    PreservesFiniteColimits ((completedConstantFiniteModules (AdicCompletion I A)).ι ⋙
      completedConstantRealization X I scalar)
  lisse : ∀ (N : ModuleCat.{u + 1} (AdicCompletion I A)),
    Module.Finite (AdicCompletion I A) N →
      IsAdicLisseModule X I ((completedConstantRealization X I scalar).obj N)
  realization : ∀ (N : ModuleCat.{u + 1} (AdicCompletion I A))
    (_hN : Module.Finite (AdicCompletion I A) N),
      (SheafOfModules.restrictScalars ((adicLisseForget X).map
        (completedConstantBaseMap X I scalar))).obj
          ((completedConstantRealization X I scalar).obj N) ≅
        adicLisseCompletedModule X I (completedConstantUnderlyingModule I N)
  linearity : ∀ (N : ModuleCat.{u + 1} (AdicCompletion I A))
      (hN : Module.Finite (AdicCompletion I A) N) (n : ℕ) (U : X.ProEtᵒᵖ)
      (r : ((adicLisseCompletedRing X I).obj.obj U))
      (a : (adicLisseConstantRing X A).obj.obj U)
      (x : ((completedConstantRealization X I scalar).obj N).val.obj U),
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))).hom.app U a =
        (limit.π (adicLisseRingSystem X I) (op n)).hom.app U r →
    (limit.π (adicLisseModuleSystem X I (completedConstantUnderlyingModule I N))
      (op n)).val.app U ((realization N hN).hom.val.app U (r • x)) =
      a • (limit.π (adicLisseModuleSystem X I (completedConstantUnderlyingModule I N))
        (op n)).val.app U ((realization N hN).hom.val.app U x)
  naturality : ∀ (M N : ModuleCat.{u + 1} (AdicCompletion I A))
      (hM : Module.Finite (AdicCompletion I A) M)
      (hN : Module.Finite (AdicCompletion I A) N) (f : M ⟶ N) (n : ℕ)
      (U : X.ProEtᵒᵖ) (x : ((completedConstantRealization X I scalar).obj M).val.obj U),
    (limit.π (adicLisseModuleSystem X I (completedConstantUnderlyingModule I N))
        (op n)).val.app U ((realization N hN).hom.val.app U
          (((completedConstantRealization X I scalar).map f).val.app U x)) =
      (((adicLisseConstantModules X A).map (completedConstantQuotientMap I
        ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map f) n)).val.app U)
          ((limit.π (adicLisseModuleSystem X I (completedConstantUnderlyingModule I M))
            (op n)).val.app U ((realization M hM).hom.val.app U x))
end AlgebraicGeometry.Scheme
