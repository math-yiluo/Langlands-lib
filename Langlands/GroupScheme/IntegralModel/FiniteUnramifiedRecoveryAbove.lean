import Langlands.GroupScheme.IntegralModel.FiniteRecoveryExistence

/-! # Exact finite unramified recovery containing prescribed coefficients -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open Langlands.LocalGalois Langlands.LocalGalois.Separable
open scoped ValuativeRel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.Descent.FiniteUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance recoveryAboveNormedField : NontriviallyNormedField F := localNormedField F
local instance recoveryAboveUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance recoveryAboveComplete : CompleteSpace F := localNormedField_complete F

/-- Two finite subfields of the inertia fixed field lie in one finite
Galois arithmetically unramified subfield of the separable closure. -/
theorem exists_common_finiteUnramified
    (E₀ E₁ : IntermediateField F (SeparableClosure F))
    [FiniteDimensional F E₀] [FiniteDimensional F E₁]
    (h₀ : E₀ ≤ inertiaFixedField F) (h₁ : E₁ ≤ inertiaFixedField F) :
    ∃ E : IntermediateField F (SeparableClosure F),
      FiniteDimensional F E ∧ IsGalois F E ∧ E₀ ≤ E ∧ E₁ ≤ E ∧
        E ≤ inertiaFixedField F ∧ ArithmeticUnramified F E := by
  let B := E₀ ⊔ E₁
  have hB : B ≤ inertiaFixedField F := sup_le h₀ h₁
  let A := fieldFactorization F B (IntermediateField.inclusion hB)
  have hvalue (x : B) :
      ((A.embedding x : A.field) : SeparableClosure F) = (x : SeparableClosure F) :=
    congrArg (fun b : B →ₐ[F] inertiaFixedField F =>
      ((b x : inertiaFixedField F) : SeparableClosure F)) A.factorization
  have hcontains : B ≤ A.field := by
    intro x hx
    have hx' : ((A.embedding ⟨x, hx⟩ : A.field) : SeparableClosure F) = x :=
      hvalue ⟨x, hx⟩
    exact hx' ▸ (A.embedding ⟨x, hx⟩).property
  exact ⟨A.field, A.finite, A.galois,
    le_sup_left.trans hcontains, le_sup_right.trans hcontains, A.inertia, A.unramified⟩

/-- Enlarge a spectral group model, retaining its actual integral recovery. -/
def SpectralGroupModel.enlarge
    {H : GroupScheme (Spec (CommRingCat.of (fixedFieldIntegers F)))}
    (D : SpectralGroupModel F H)
    (E : IntermediateField F (SeparableClosure F))
    [FiniteDimensional F E] [IsGalois F E]
    (h : D.field ≤ E) (hE : E ≤ inertiaFixedField F)
    (hUnram : ArithmeticUnramified F E) : SpectralGroupModel F H where
  field := E
  finite := inferInstance
  galois := inferInstance
  inertia := hE
  unramified := hUnram
  group := (GroupScheme.baseChange (stageIntegerMap F h)).obj D.group
  affine := MorphismProperty.pullback_snd _ _ D.affine
  smooth := MorphismProperty.pullback_snd _ _ D.smooth
  iso := D.iso ≪≫ (stageIntegralComparison F h D.inertia hE D.group).symm

end Langlands.GroupScheme.Descent.FiniteUnramified

namespace Langlands.GroupScheme.IntegralModel

open Descent Descent.FiniteUnramified GaloisPointComparison

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance finiteRecoveryAboveNormedField : NontriviallyNormedField F := localNormedField F
local instance finiteRecoveryAboveUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance finiteRecoveryAboveComplete : CompleteSpace F := localNormedField_complete F

set_option maxHeartbeats 400000 in
/-- A supplied smooth integral model has exact finite unramified recovery over
a field containing any prescribed finite subfield of the inertia fixed field. -/
theorem finiteUnramifiedRecovery_above
    (E₀ : IntermediateField F (SeparableClosure F))
    [FiniteDimensional F E₀] (h₀ : E₀ ≤ inertiaFixedField F)
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hP : P.IsSmooth) :
    ∃ (E : IntermediateField F (SeparableClosure F))
      (hE : Fact (E ≤ inertiaFixedField F)),
      FiniteDimensional F E ∧ IsGalois F E ∧ ArithmeticUnramified F E ∧
        E₀ ≤ E ∧ @HasFiniteRecoveryAt F _ _ _ _ E hE G P := by
  let : IsAffine P.group.X.left := isAffine_of_isAffineHom P.group.X.hom
  let : Smooth P.group.X.hom := hP
  obtain ⟨K, hfinK, hgalK, hK, hunK, H, hHaff, hHsm, d⟩ :=
    spectralGroupModel F P.group
  let D₀ : SpectralGroupModel F P.group :=
    ⟨K, hfinK, hgalK, hK, hunK, H, hHaff, hHsm, d⟩
  let : FiniteDimensional F D₀.field := D₀.finite
  obtain ⟨B, hfinB, hgalB, h₀B, hKB, hB, hunB⟩ :=
    exists_common_finiteUnramified F E₀ D₀.field h₀ D₀.inertia
  let : FiniteDimensional F B := hfinB
  let : IsGalois F B := hgalB
  let D := D₀.enlarge F B hKB hB hunB
  obtain ⟨A⟩ := nonempty_modelIsoStage F P D
  let : Fact (A.field ≤ inertiaFixedField F) := ⟨A.inertia⟩
  refine ⟨A.field, ⟨A.inertia⟩, A.finite, A.galois, A.unramified,
    h₀B.trans A.contains, ?_⟩
  exact finiteRecoveryAt_of_rawStage F A.field G P D.field A.contains D.inertia
    D.group D.affine D.smooth D.iso A.iso A.recovery

end Langlands.GroupScheme.IntegralModel
