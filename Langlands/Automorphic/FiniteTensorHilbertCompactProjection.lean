import Langlands.Automorphic.FiniteTensorHilbertFullSphericalProjection
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Finite-rank compact projections from genuine admissible smooth models -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV uI
set_option autoImplicit false
set_option maxHeartbeats 40000

namespace Langlands.TensorHilbertHeckeAux

universe uH uG uA

section FiniteAmbient

variable {ι : Type uI}
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (K : Submodule ℂ H) [FiniteDimensional ℂ K]
variable (T : ι → K →L[ℂ] K) (c : ι → ℂ)

theorem ambientJointEigenspace_finite :
    FiniteDimensional ℂ (ambientJointEigenspace K T c) :=
  Submodule.finiteDimensional_of_le (ambientJointEigenspace_le K T c)

theorem ambientJointEigenspace_finrank_le :
    Module.finrank ℂ (ambientJointEigenspace K T c) ≤ Module.finrank ℂ K :=
  Submodule.finrank_mono (ambientJointEigenspace_le K T c)

variable [CompleteSpace H]

/-- Finite rank concerns the actual range of the full-domain projection. -/
theorem ambientJointProjection_finite :
    FiniteDimensional ℂ (ambientJointProjection K T c).range := by
  rw [ambientJointProjection_range]
  exact ambientJointEigenspace_finite K T c

theorem ambientJointProjection_finrank_le :
    Module.finrank ℂ (ambientJointProjection K T c).range ≤ Module.finrank ℂ K := by
  rw [ambientJointProjection_range]
  exact ambientJointEigenspace_finrank_le K T c

/-- The full joint projection factors through the same finite-dimensional
submodule with its inherited topology. -/
theorem ambientJointProjection_isCompact :
    IsCompactOperator (ambientJointProjection K T c) := by
  rw [ambientJointProjection_eq_comp]
  exact ((isCompactOperator_of_locallyCompactSpace_dom
    (jointOrthogonalProjection T c)).clm_comp K.subtypeL).comp_clm
      K.orthogonalProjectionOnto

end FiniteAmbient

section FiniteFixed

open MeasureTheory

variable {G : Type uG} [Group G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable (τ : Representation ℂ G H) (S : Subrepresentation τ)
variable (hS : IsClosed (S : Set H))
variable (hτ : ∀ (g : G) (x : H), ‖τ g x‖ = ‖x‖)

/-- This is compactness of the genuine orthogonal projection onto every
subgroup-fixed vector, rather than an assumed compact operator. -/
theorem fullFixedOrthogonalProjection_isCompact (K : Subgroup G)
    (hfinite : FiniteDimensional ℂ (fixedVectors S.toRepresentation K)) :
    IsCompactOperator (fullFixedOrthogonalProjection τ S hS hτ K) := by
  let : CompleteSpace S.toSubmodule := hS.completeSpace_coe
  let : FiniteDimensional ℂ (fixedVectors S.toRepresentation K) := hfinite
  exact (isCompactOperator_of_locallyCompactSpace_dom
    (fixedVectors S.toRepresentation K).orthogonalProjectionOnto).clm_comp
      (fixedVectors S.toRepresentation K).subtypeL

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem factorFullFixedOrthogonalProjection_isCompact
    {A : Type uA} [AddCommGroup A] [Module ℂ A]
    {σ : Representation ℂ G A}
    (e : σ.Equiv (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation)
    (hσ : IsAdmissible σ) (K : OpenSubgroup G) :
    IsCompactOperator (fullFixedOrthogonalProjection τ S hS hτ K.toSubgroup) :=
  fullFixedOrthogonalProjection_isCompact τ S hS hτ K.toSubgroup
    (TensorHilbertFixedAux.factorFixed_finite τ S e K (hσ.2 K))

variable [MeasurableSpace G] [BorelSpace G]
variable {ι : Type uI} (μ : Measure G) [μ.IsHaarMeasure]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

theorem cornerFullJointProjection_finite
    (hfinite : FiniteDimensional ℂ (fixedVectors S.toRepresentation K.toSubgroup))
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    FiniteDimensional ℂ (cornerFullJointProjection μ K hK τ S hS hτ f c).range := by
  let : CompleteSpace S.toSubmodule := hS.completeSpace_coe
  let : FiniteDimensional ℂ (fixedVectors S.toRepresentation K.toSubgroup) := hfinite
  dsimp only [cornerFullJointProjection]
  exact ambientJointProjection_finite _ _ c

theorem cornerFullJointProjection_finrank_le
    (hfinite : FiniteDimensional ℂ (fixedVectors S.toRepresentation K.toSubgroup))
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    Module.finrank ℂ (cornerFullJointProjection μ K hK τ S hS hτ f c).range ≤
      Module.finrank ℂ (fixedVectors S.toRepresentation K.toSubgroup) := by
  let : CompleteSpace S.toSubmodule := hS.completeSpace_coe
  let : FiniteDimensional ℂ (fixedVectors S.toRepresentation K.toSubgroup) := hfinite
  dsimp only [cornerFullJointProjection]
  exact ambientJointProjection_finrank_le _ _ c

theorem cornerFullJointProjection_isCompact
    (hfinite : FiniteDimensional ℂ (fixedVectors S.toRepresentation K.toSubgroup))
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    IsCompactOperator (cornerFullJointProjection μ K hK τ S hS hτ f c) := by
  let : CompleteSpace S.toSubmodule := hS.completeSpace_coe
  let : FiniteDimensional ℂ (fixedVectors S.toRepresentation K.toSubgroup) := hfinite
  dsimp only [cornerFullJointProjection]
  exact ambientJointProjection_isCompact _ _ c

variable {A : Type uA} [AddCommGroup A] [Module ℂ A]
variable {σ : Representation ℂ G A}
variable (e : σ.Equiv (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation)
variable (hσ : IsAdmissible σ)

include e hσ

/-- Admissibility supplies finiteness through the actual smooth-model fixed
equivalence, without assuming the completed representation is smooth. -/
theorem factorCornerFullJointProjection_finite
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    FiniteDimensional ℂ (cornerFullJointProjection μ K hK τ S hS hτ f c).range :=
  cornerFullJointProjection_finite τ S hS hτ μ K hK
    (TensorHilbertFixedAux.factorFixed_finite τ S e K (hσ.2 K)) f c

theorem factorCornerFullJointProjection_finrank_le
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    Module.finrank ℂ (cornerFullJointProjection μ K hK τ S hS hτ f c).range ≤
      Module.finrank ℂ (fixedVectors σ K.toSubgroup) := by
  have hfinite := TensorHilbertFixedAux.factorFixed_finite τ S e K (hσ.2 K)
  exact (cornerFullJointProjection_finrank_le τ S hS hτ μ K hK hfinite f c).trans_eq
    (TensorHilbertFixedAux.factorFixed_finrank τ S e K)

theorem factorCornerFullJointProjection_isCompact
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    IsCompactOperator (cornerFullJointProjection μ K hK τ S hS hτ f c) :=
  cornerFullJointProjection_isCompact τ S hS hτ μ K hK
    (TensorHilbertFixedAux.factorFixed_finite τ S e K (hσ.2 K)) f c

end FiniteFixed
end Langlands.TensorHilbertHeckeAux

namespace Langlands.Automorphic

open MeasureTheory
open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
variable {ι : Type uI}

local instance tensorCompactProjectionRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance tensorCompactProjectionContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorCompactProjectionSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance tensorCompactProjectionFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance tensorCompactProjectionFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorCompactProjectionLocalSpaceGroup (v : FinitePlace F)
    (L : LocalRealization F n v) : AddCommGroup L.Space := Submodule.addCommGroup _
local instance tensorCompactProjectionMeasurable (v : FinitePlace F) :
    MeasurableSpace (FiniteLocalGL F n v) := borel _
local instance tensorCompactProjectionBorel (v : FinitePlace F) :
    BorelSpace (FiniteLocalGL F n v) := ⟨rfl⟩

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- Orthogonal projection on the whole actual closed tensor slice onto all
its subgroup-fixed vectors, with the inherited global Hilbert norm. -/
def sliceHilbertFullFixedProjection (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (K : Subgroup (FiniteLocalGL F n v)) :=
  TensorHilbertHeckeAux.fullFixedOrthogonalProjection _
    (P.sliceHilbertRange b v y) (P.isClosed_sliceHilbertRange b v y)
    (fun g x => b.completedRepresentation_norm (localInclusion F n v g) x) K

end FiniteTensorPresentation
end Langlands.Automorphic
