import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.IntegralModel.BaseChangeCoefficientHom
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IsSepClosed

/-! # Extension of generic homomorphisms to smooth integral models (KP 2.10.10) -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

open Langlands.LocalGalois.Separable GaloisPointComparison

section Necessity

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  {M : IntegralModel R K G} {N : IntegralModel R K H} {f : G ⟶ H}

/-- The necessary direction of KP Corollary 2.10.10 over the given base:
a compatible model homomorphism carries the actual integral-point image of
the source model into that of the target model. -/
theorem Hom.integralPoints_map_le (φ : M.Hom N f) :
    ∀ g ∈ M.integralPoints, rationalPoints.map f g ∈ N.integralPoints :=
  fun _ hg => φ.map_mem_integralPoints hg

end Necessity

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  {M : IntegralModel ↥𝒪[F] F G} {N : IntegralModel ↥𝒪[F] F H} {f : G ⟶ H}

local instance smoothHomExtensionAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance smoothHomExtensionScalarTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- The necessary direction of the unramified form: a compatible model
homomorphism over `𝒪[F]` carries the integral-point image of the source model
over the integers of the maximal unramified extension into that of the target,
along the actual base change of the generic homomorphism. -/
theorem Hom.unramifiedIntegralPoints_map_le (φ : M.Hom N f) :
    ∀ g ∈ M.baseChangeUnramified.integralPoints,
      rationalPoints.map ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map f) g ∈
        N.baseChangeUnramified.integralPoints :=
  fun _ hg =>
    (φ.baseChangeCoefficients (fixedFieldIntegers F) (inertiaFixedField F)).map_mem_integralPoints hg

end Unramified

/-- **KP Corollary 2.10.10 and Remark 2.10.19 over a strictly Henselian base.**
Let `R` be a Henselian discrete valuation ring with separably closed residue
field and fraction field `K`. For a smooth integral model `M` of `G`, an
arbitrary integral model `N` of `H`, and a homomorphism `f : G ⟶ H` of the
generic groups, if `f` carries the integral points of `M` into those of `N`,
then `f` extends to a homomorphism of integral models `M.Hom N f`. -/
def SmoothHomExtensionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G H : GroupScheme (Spec (CommRingCat.of K))) (f : G ⟶ H)
    (M : IntegralModel R K G) (N : IntegralModel R K H),
    M.IsSmooth →
    (∀ g ∈ M.integralPoints, rationalPoints.map f g ∈ N.integralPoints) →
    Nonempty (M.Hom N f)

/-- **KP Corollary 2.10.10 and Remark 2.10.19 over a nonarchimedean local field.**
For a smooth integral model `M` over `𝒪[F]` of `G`, an arbitrary integral
model `N` over `𝒪[F]` of `H`, and a homomorphism `f : G ⟶ H`, if the base
change of `f` to the maximal unramified extension carries the integral points
of `M.baseChangeUnramified` into those of `N.baseChangeUnramified`, then `f`
extends to a homomorphism of integral models over `𝒪[F]`. -/
def UnramifiedSmoothHomExtensionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G H : GroupScheme (Spec (CommRingCat.of F))) (f : G ⟶ H)
    (M : IntegralModel ↥𝒪[F] F G) (N : IntegralModel ↥𝒪[F] F H),
    M.IsSmooth →
    (∀ g ∈ M.baseChangeUnramified.integralPoints,
      rationalPoints.map ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map f) g ∈
        N.baseChangeUnramified.integralPoints) →
    Nonempty (M.Hom N f)

end Langlands.GroupScheme.IntegralModel
