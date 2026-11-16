import Langlands.GroupScheme.IntegralModel.FiniteInnerInertiaSemilinearity

/-! # Smooth inner descent of a supplied stable integral model -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.LocalGalois Langlands.LocalGalois.Separable
open scoped ValuativeRel CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.IntegralModel
open Descent Descent.FiniteUnramified GaloisPointComparison

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance smoothInnerNormedField : NontriviallyNormedField F := localNormedField F
local instance smoothInnerUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance smoothInnerComplete : CompleteSpace F := localNormedField_complete F

/-- A supplied model is recovered by a smooth model over the given integers,
with the actual generic comparison and every inner Galois action retained. -/
def HasSmoothInnerDescent
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
      rationalPoints (baseChanged F (inertiaFixedField F) G)) : Prop :=
  ∃ (H : GroupScheme (Spec (CommRingCat.of F))) (M : IntegralModel ↥𝒪[F] F H)
    (f : baseChanged F (inertiaFixedField F) H ≅ baseChanged F (inertiaFixedField F) G),
    M.IsSmooth ∧ Nonempty (M.baseChangeUnramified.Iso P f) ∧
      M.baseChangeUnramified.integralPoints.map (rationalPoints.map f.hom) = P.integralPoints ∧
      InnerGaloisCompatible F (inertiaFixedField F) H G c f

section AtField

variable (E : IntermediateField F (SeparableClosure F)) [hEinertia : Fact (E ≤ inertiaFixedField F)]

local instance smoothInnerFieldAlgebra : Algebra E (inertiaFixedField F) :=
  (IntermediateField.inclusion (show E ≤ inertiaFixedField F from hEinertia.out)).toAlgebra
local instance smoothInnerFieldTower : IsScalarTower F E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance smoothInnerIntegerAlgebra :
    Algebra (extensionIntegers F E) (fixedFieldIntegers F) :=
  (spectralIntegerInclusion F E (show E ≤ inertiaFixedField F from hEinertia.out)).toAlgebra
local instance smoothInnerIntegerFieldAlgebra :
    Algebra (extensionIntegers F E) (inertiaFixedField F) :=
  ((IntermediateField.inclusion (show E ≤ inertiaFixedField F from hEinertia.out)).toRingHom.comp
    (algebraMap (extensionIntegers F E) E)).toAlgebra
local instance smoothInnerGenericTower :
    IsScalarTower (extensionIntegers F E) E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance smoothInnerIntegralTower :
    IsScalarTower (extensionIntegers F E) (fixedFieldIntegers F) (inertiaFixedField F) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact spectralIntegerInclusion_inertia F E (show E ≤ inertiaFixedField F from hEinertia.out) x
local instance smoothInnerCoefficientFlat :
    Flat (Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F)) :=
  (spectralIntegerMap_fpqc F E (show E ≤ inertiaFixedField F from hEinertia.out)).2.1
local instance smoothInnerCoefficientSurjective :
    Surjective (Spec.algebraMap (extensionIntegers F E) (fixedFieldIntegers F)) :=
  (spectralIntegerMap_fpqc F E (show E ≤ inertiaFixedField F from hEinertia.out)).1

local instance smoothInnerIntegerFlat : Flat (integerMap F E) :=
  (integerMap_fpqc F E).2.1
local instance smoothInnerIntegerSurjective : Surjective (integerMap F E) :=
  (integerMap_fpqc F E).1

variable [FiniteDimensional F E] [IsGalois F E]

set_option maxHeartbeats 800000 in
/-- Consume exact common finite recovery to obtain the smooth inner form,
its actual model recovery and all-automorphism compatibility. -/
theorem innerDescent_of_finiteInnerRecoveryAt
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
      rationalPoints (baseChanged F (inertiaFixedField F) G))
    (hP : P.IsSmooth)
    (hstable : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      ∀ g ∈ P.integralPoints,
        c σ * rationalConjugate F (inertiaFixedField F) G σ g * (c σ)⁻¹ ∈ P.integralPoints)
    (hstable' : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      ∀ g ∈ P.integralPoints,
        rationalConjugate F (inertiaFixedField F) G σ.symm
          ((c σ)⁻¹ * g * c σ) ∈ P.integralPoints)
    (hUnram : ArithmeticUnramified F E)
    (hrec : HasFiniteInnerRecoveryAt F E G P c) : HasSmoothInnerDescent F G P c := by
  obtain ⟨⟨N, ⟨e⟩⟩, d, hd, hall⟩ := hrec
  have hlift := recovery_at_liftAutomorphism F E G c d hall
  exact ⟨finiteInnerGenericGroup F E G N P e c d hlift hP hstable hstable' hd hUnram,
    givenFiniteInnerModel F E G N P e c d hlift hP hstable hstable' hd hUnram,
    finiteInnerInertiaGenericComparison F E G N P e c d hlift hP hstable hstable' hd hUnram,
    givenFiniteInnerModel_smooth F E G N P e c d hlift hP hstable hstable' hd hUnram,
    ⟨givenFiniteInnerModelIso F E G N P e c d hlift hP hstable hstable' hd hUnram⟩,
    givenFiniteInnerModel_map_integralPoints F E G N P e c d hlift hP hstable hstable' hd hUnram,
    finiteInnerInertiaGenericComparison_innerGaloisCompatible
      F E G N P e c d hlift hP hstable hstable' hd hUnram hall⟩

end AtField

/-- A finite-trivial cocycle preserving a supplied smooth model in both
 directions has smooth effective inner descent over the given integers. -/
theorem exists_smoothInnerDescent
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hP : P.IsSmooth)
    (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
      rationalPoints (baseChanged F (inertiaFixedField F) G))
    (hc : ∀ σ τ, c (σ * τ) = c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ))
    (hfinite : ∃ C : IntermediateField F (inertiaFixedField F),
      FiniteDimensional F C ∧ ∀ σ ∈ C.fixingSubgroup, c σ = 1)
    (hstable : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      ∀ g ∈ P.integralPoints,
        c σ * rationalConjugate F (inertiaFixedField F) G σ g * (c σ)⁻¹ ∈ P.integralPoints)
    (hstable' : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      ∀ g ∈ P.integralPoints,
        rationalConjugate F (inertiaFixedField F) G σ.symm
          ((c σ)⁻¹ * g * c σ) ∈ P.integralPoints) :
    HasSmoothInnerDescent F G P c := by
  obtain ⟨E, hE, hgal, hfin, hunram, hrec⟩ :=
    exists_common_finiteInnerRecovery F G P hP c hc hfinite
  let : Fact (E ≤ inertiaFixedField F) := hE
  let : IsGalois F E := hgal
  let : FiniteDimensional F E := hfin
  exact innerDescent_of_finiteInnerRecoveryAt F E G P c hP hstable hstable' hunram hrec

end Langlands.GroupScheme.IntegralModel
