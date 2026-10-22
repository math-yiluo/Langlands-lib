import Langlands.LocalFactor.Abelian.SpectralTransport

/-! # Supplied self-dual Haar measures under actual field transport -/

noncomputable section

open MeasureTheory

namespace Langlands.PadicField.AbelianTransport

open HarmonicAnalysis ConductorTransport LocalFactor.PadicAbelian

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (e : F.Carrier ≃ₐ[Padic p] E.Carrier)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : TopologicalSpace E.Carrier := E.canonicalTopologicalData.topology
local instance : MeasurableSpace F.Carrier := borel F.Carrier
local instance : MeasurableSpace E.Carrier := borel E.Carrier
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance : BorelSpace E.Carrier := ⟨rfl⟩
local instance : IsTopologicalRing F.Carrier := by
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  infer_instance
local instance : IsTopologicalRing E.Carrier := by
  let := E.canonicalTopologicalData.valuativeRel
  let := E.canonicalTopologicalData.localField
  infer_instance
local instance : LocallyCompactSpace F.Carrier := by
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  infer_instance
local instance : LocallyCompactSpace E.Carrier := by
  let := E.canonicalTopologicalData.valuativeRel
  let := E.canonicalTopologicalData.localField
  infer_instance
local instance : T2Space F.Carrier := by
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  infer_instance
local instance : T2Space E.Carrier := by
  let := E.canonicalTopologicalData.valuativeRel
  let := E.canonicalTopologicalData.localField
  let := IsTopologicalAddGroup.rightUniformSpace E.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := E.Carrier)
  infer_instance
local instance : TotallyDisconnectedSpace F.Carrier := by
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance : TotallyDisconnectedSpace E.Carrier := by
  let := E.canonicalTopologicalData.valuativeRel
  let := E.canonicalTopologicalData.localField
  let : NonarchimedeanRing E.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing E.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

private theorem continuous_fieldEquiv : Continuous e := by
  let := F.canonicalNormedField
  let := E.canonicalNormedField
  exact (Weil.Local.extension_isometry F E e.toAlgHom).continuous

/-- Intrinsic Fourier self-duality is preserved and reflected by the actual transports. -/
theorem isSelfDual_iff (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : AdditiveHaarMeasure F.Carrier) :
    IsSelfDual (additiveCharacter F E e ψ) (haarMeasure F E e μ) ↔ IsSelfDual ψ μ :=
  FieldTransport.isSelfDual_iff e.toRingEquiv
    (continuous_fieldEquiv F E e) (continuous_fieldEquiv E F e.symm) ψ μ

/-- Equivalence of supplied self-dual Haar measures; it asserts no existence. -/
def selfDualHaarEquiv (ψ : UnitaryAdditiveCharacter F.Carrier) :
    SelfDualHaar F.canonicalTopologicalData ψ ≃
      SelfDualHaar E.canonicalTopologicalData (additiveCharacter F E e ψ) :=
  (FieldTransport.haarMeasureEquiv e.toRingEquiv
    (continuous_fieldEquiv F E e) (continuous_fieldEquiv E F e.symm)).subtypeEquiv
      (fun μ => (isSelfDual_iff F E e ψ μ).symm)

@[simp] theorem selfDualHaarEquiv_val (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : SelfDualHaar F.canonicalTopologicalData ψ) :
    (selfDualHaarEquiv F E e ψ μ).val = haarMeasure F E e μ.val := rfl

@[simp] theorem selfDualHaarEquiv_symm_val (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : SelfDualHaar E.canonicalTopologicalData (additiveCharacter F E e ψ)) :
    ((selfDualHaarEquiv F E e ψ).symm ν).val =
      haarMeasure E F e.symm ν.val := rfl

/-- Langlands' half-argument constant agrees at corresponding supplied witnesses. -/
theorem langlandsConstantAtSelfDual_eq (χ : Quasicharacter F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : SelfDualHaar F.canonicalTopologicalData ψ) :
    langlandsConstantAtSelfDual E.canonicalTopologicalData (quasicharacter F E e χ)
      (additiveCharacter F E e ψ) (selfDualHaarEquiv F E e ψ μ) =
        langlandsConstantAtSelfDual F.canonicalTopologicalData χ ψ μ :=
  centeredConstant_eq F E e χ ψ μ.val

/-- The actual spectral expression agrees at the same parameter and transported witness. -/
theorem langlandsEpsilonAtSelfDual_eq (χ : Quasicharacter F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : SelfDualHaar F.canonicalTopologicalData ψ) (s : ℂ) :
    langlandsEpsilonAtSelfDual E.canonicalTopologicalData (quasicharacter F E e χ)
      (additiveCharacter F E e ψ) (selfDualHaarEquiv F E e ψ μ) s =
        langlandsEpsilonAtSelfDual F.canonicalTopologicalData χ ψ μ s :=
  epsilon_eq F E e χ ψ μ.val s

end Langlands.PadicField.AbelianTransport
