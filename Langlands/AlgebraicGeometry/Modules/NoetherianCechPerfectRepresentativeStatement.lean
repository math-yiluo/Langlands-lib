import Langlands.Cohomology.PerfectModuleComplex
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

attribute [local instance] HasDerivedCategory.standard

/-- One strictly perfect representative for the original and all scalar Čech models. -/
def NoetherianCechPerfectRepresentativeStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (X : Scheme.{u}) (π : X ⟶ Spec (.of R)) [IsProper π] [Flat π]
    (M : X.Modules)
    (_htriv : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf))
    (𝒰 : X.OrderedAffineCover),
    let C := OModulePresheaf.ofModules π M
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      Langlands.Cohomology.ModuleComplex.IsStrictlyPerfect P ∧
      Nonempty (DerivedCategory.Q.obj P ≅
        DerivedCategory.Q.obj
          ((CochainComplex.of (fun i => ModuleCat.of R (C.cochain 𝒰 i))
            (fun i => ModuleCat.ofHom (C.d 𝒰 i)) (fun i => by
              apply ModuleCat.hom_ext
              exact C.d_comp_d 𝒰 i)).extend ComplexShape.embeddingUpNat)) ∧
      ∀ (A : Type u) [CommRing A] (f : R →+* A),
        letI := f.toAlgebra
        let CA := OModulePresheaf.ofModules
          (pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)
        Nonempty
          (DerivedCategory.Q.obj
              ((Langlands.Cohomology.ModuleComplex.baseChange f).obj P) ≅
            DerivedCategory.Q.obj
              ((CochainComplex.of
                (fun i => ModuleCat.of A (CA.cochain (𝒰.baseChange π A) i))
                (fun i => ModuleCat.ofHom (CA.d (𝒰.baseChange π A) i))
                (fun i => by
                  apply ModuleCat.hom_ext
                  exact CA.d_comp_d (𝒰.baseChange π A) i)).extend
                ComplexShape.embeddingUpNat))

end Langlands.AlgebraicGeometry.Modules
