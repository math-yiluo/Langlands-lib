import Langlands.Cohomology.PerfectModuleComplex
import Mathlib.RingTheory.Flat.Basic

set_option autoImplicit false

universe u

open CategoryTheory

namespace Langlands.Cohomology.ModuleComplex

attribute [local instance] HasDerivedCategory.standard

/-- A bounded flat module complex with finite cycle quotients has one strictly
perfect representative computing all ordinary scalar extensions. -/
def BoundedFlatCategoricalReplacementStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ) [∀ i, Module.Flat R (C.X i)]
    (n : ℕ) (_hbound : ∀ i : ℕ, n < i → Subsingleton (C.X i))
    (_hfin0 : Module.Finite R (LinearMap.ker (C.d 0 1).hom))
    (_hfin : ∀ i : ℕ, Module.Finite R
      (LinearMap.ker (C.d (i + 1) (i + 2)).hom ⧸
        (LinearMap.range (C.d i (i + 1)).hom).comap
          (LinearMap.ker (C.d (i + 1) (i + 2)).hom).subtype)),
    ∃ K : CochainComplex (ModuleCat.{u} R) ℤ,
      IsStrictlyPerfect K ∧
      Nonempty (DerivedCategory.Q.obj K ≅
        DerivedCategory.Q.obj (C.extend ComplexShape.embeddingUpNat)) ∧
      ∀ (A : Type u) [CommRing A] (f : R →+* A),
        Nonempty (DerivedCategory.Q.obj ((baseChange f).obj K) ≅
          DerivedCategory.Q.obj
            ((((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).extend
              ComplexShape.embeddingUpNat))

end Langlands.Cohomology.ModuleComplex
