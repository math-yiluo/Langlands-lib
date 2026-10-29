import Langlands.Cohomology.PerfectModuleComplex
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Canonical scalar extension adjunction for strictly perfect sources -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Cohomology.ModuleComplex

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- The actual degreewise tensor-unit chain map. -/
def scalarExtensionComplexUnit (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    K ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj
      ((baseChange φ).obj K) where
  f i := (ModuleCat.extendRestrictScalarsAdj φ).unit.app (K.X i)
  comm' i j _ := ((ModuleCat.extendRestrictScalarsAdj φ).unit.naturality (K.d i j)).symm

attribute [local instance] HasDerivedCategory.standard

/-- The tensor unit in the actual derived category, using exact scalar restriction. -/
def scalarExtensionDerivedUnit (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.obj K ⟶ (ModuleCat.restrictScalars φ).mapDerivedCategory.obj
      (DerivedCategory.Q.obj ((baseChange φ).obj K)) :=
  DerivedCategory.Q.map (scalarExtensionComplexUnit φ K) ≫
    (ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.inv.app ((baseChange φ).obj K)

/-- The canonical tensor-unit map induces the Hom adjunction for strictly perfect
sources, without requiring the ring homomorphism to be flat. -/
def PerfectScalarAdjunctionStatement : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] (φ : R →+* S)
    (K : CochainComplex (ModuleCat.{u} R) ℤ),
    IsStrictlyPerfect K →
    ∀ (L : CochainComplex (ModuleCat.{u} S) ℤ),
      Function.Bijective (fun f :
        (DerivedCategory.Q.obj ((baseChange φ).obj K) ⟶ DerivedCategory.Q.obj L) =>
          scalarExtensionDerivedUnit φ K ≫
            (ModuleCat.restrictScalars φ).mapDerivedCategory.map f)

end Langlands.Cohomology.ModuleComplex
