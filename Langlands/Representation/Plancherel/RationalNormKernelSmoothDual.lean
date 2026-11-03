import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.Representation.Smooth.Contragredient.OpenRestriction

/-! # Smooth dual restriction to the actual rational-character norm kernel -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

universe uR uF uV

variable {R : Type uR} [CommRing R]
  {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  {V : Type uV} [AddCommGroup V] [Module R V]

local instance instRationalNormKernelSmoothDual1 : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance instRationalNormKernelSmoothDual2 : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

/-- The actual open norm kernel has exactly the ambient smooth dual vectors. -/
theorem isSmoothVector_dual_rationalNormKernel_iff
    (ρ : Representation R (GroupScheme.rationalPoints G) V) (ℓ : Module.Dual R V) :
    IsSmoothVector (Representation.dual (ρ.comp (rationalCommonNormKernel G).subtype)) ℓ ↔
      IsSmoothVector ρ.dual ℓ :=
  isSmoothVector_restrict_open_iff ρ.dual (rationalCommonNormOpenSubgroup G) ℓ

/-- Canonical restriction comparison for the complete smooth dual of an actual
rational-point action, using the proved openness of the common norm kernel. -/
def rationalNormKernelSmoothDualEquiv
    (ρ : Representation R (GroupScheme.rationalPoints G) V) :
    Representation.Equiv ((smoothContragredient ρ).comp (rationalCommonNormKernel G).subtype)
      (smoothContragredient (ρ.comp (rationalCommonNormKernel G).subtype)) :=
  smoothContragredientRestrictOpenEquiv ρ (rationalCommonNormOpenSubgroup G)

@[simp]
theorem rationalNormKernelSmoothDualEquiv_apply
    (ρ : Representation R (GroupScheme.rationalPoints G) V)
    (ℓ : SmoothDual ρ) (v : V) :
    (rationalNormKernelSmoothDualEquiv G ρ ℓ).val v = ℓ.val v := rfl

@[simp]
theorem rationalNormKernelSmoothDualEquiv_symm_apply
    (ρ : Representation R (GroupScheme.rationalPoints G) V)
    (ℓ : SmoothDual (ρ.comp (rationalCommonNormKernel G).subtype)) (v : V) :
    ((rationalNormKernelSmoothDualEquiv G ρ).symm ℓ).val v = ℓ.val v := rfl

end Langlands.Plancherel
