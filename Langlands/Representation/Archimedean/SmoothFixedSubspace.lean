import Langlands.Representation.Archimedean.SmoothInvariantSubspace
import Langlands.Representation.Smooth.Definitions

/-! # Genuine smooth vectors at a commuting fixed level -/

noncomputable section

open scoped Manifold ContDiff Topology
open Topology

namespace Langlands.Archimedean.SmoothInvariantSubspace

universe u𝔤 uH uG uE uL

variable {L : Type uL} [Group L]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (σ : L →* (E →L[ℂ] E)) (J : Subgroup L)

/-- The existing algebraic fixed vectors of the supplied bounded action. -/
abbrev fixedSubspace : Submodule ℂ E :=
  Langlands.fixedVectors (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp σ) J

@[simp]
theorem mem_fixedSubspace_iff (v : E) :
    v ∈ fixedSubspace σ J ↔ ∀ j : J, σ (j : L) v = v := Iff.rfl

/-- Common fixed vectors of bounded operators form a closed subspace. -/
theorem isClosed_fixedSubspace : IsClosed (fixedSubspace σ J : Set E) := by
  have he : (fixedSubspace σ J : Set E) = ⋂ j : J, {v : E | σ (j : L) v = v} := by
    ext v
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [he]
  exact isClosed_iInter fun j => isClosed_eq (σ (j : L)).continuous continuous_id

instance fixedSubspace_completeSpace [CompleteSpace E] : CompleteSpace (fixedSubspace σ J) :=
  (isClosed_fixedSubspace σ J).completeSpace_coe

variable {G : Type uG} [Group G] (π : G →* (E →L[ℂ] E))
  (hcomm : ∀ g l v, π g (σ l v) = σ l (π g v))

include hcomm in
/-- A commuting bounded action preserves every supplied fixed level. -/
theorem fixedSubspace_invariant (g : G) (v : E) (hv : v ∈ fixedSubspace σ J) :
    π g v ∈ fixedSubspace σ J := by
  intro j
  change σ (j : L) (π g v) = π g v
  rw [← hcomm g (j : L) v, (mem_fixedSubspace_iff σ J v).mp hv j]

/-- The action on the full J-fixed subspace of the ambient Hilbert space. -/
def fixedRestriction : G →* (fixedSubspace σ J →L[ℂ] fixedSubspace σ J) :=
  restriction π (fixedSubspace σ J) (fixedSubspace_invariant σ J π hcomm)

@[simp]
theorem fixedRestriction_apply (g : G) (v : fixedSubspace σ J) :
    (fixedRestriction σ J π hcomm g v : E) = π g v := rfl

/-- The fixed-level restriction inherits a supplied isometry hypothesis. -/
theorem isometry_fixedRestriction (hπ : ∀ g, Isometry (π g)) (g : G) :
    Isometry (fixedRestriction σ J π hcomm g) :=
  isometry_restriction π (fixedSubspace σ J) (fixedSubspace_invariant σ J π hcomm) hπ g

/-- The fixed-level restriction inherits supplied joint continuity. -/
theorem isContinuousRepresentation_fixedRestriction [TopologicalSpace G]
    (hπ : IsContinuousRepresentation π) :
    IsContinuousRepresentation (fixedRestriction σ J π hcomm) :=
  isContinuousRepresentation_restriction π (fixedSubspace σ J)
    (fixedSubspace_invariant σ J π hcomm) hπ

variable {𝔤 : Type u𝔤} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
  [TopologicalSpace G] [ChartedSpace H G] [CompleteSpace E]

/-- Smoothness at the fixed level is exactly ambient smoothness of that vector. -/
theorem isSmoothVector_fixedRestriction_iff (v : fixedSubspace σ J) :
    IsSmoothVector I (fixedRestriction σ J π hcomm) v ↔ IsSmoothVector I π (v : E) :=
  isSmoothVector_iff π (fixedSubspace σ J) (fixedSubspace_invariant σ J π hcomm) I v

variable [LieGroup I ∞ G]

/-- Ambient derivative smooth vectors whose underlying vectors are J-fixed. -/
abbrev ambientFixedSmoothSubspace : Submodule ℂ (DerivativeSmoothVectors I π) :=
  ambientSmoothSubspace π (fixedSubspace σ J) I

omit [CompleteSpace E] in
@[simp]
theorem mem_ambientFixedSmoothSubspace (v : DerivativeSmoothVectors I π) :
    v ∈ ambientFixedSmoothSubspace σ J π I ↔
      ∀ j : J, σ (j : L) (DerivativeSmoothVectors.toSmooth I π v : E) =
        (DerivativeSmoothVectors.toSmooth I π v : E) := Iff.rfl

omit [CompleteSpace E] in
/-- The ambient J-fixed smooth vectors are closed for the genuine derivative topology. -/
theorem isClosed_ambientFixedSmoothSubspace :
    IsClosed (ambientFixedSmoothSubspace σ J π I : Set (DerivativeSmoothVectors I π)) :=
  isClosed_ambientSmoothSubspace π (fixedSubspace σ J) I (isClosed_fixedSubspace σ J)

/-- The genuine smooth space at fixed level is the closed ambient fixed subspace
for the genuine derivative topology. -/
def fixedDerivativeEquiv :
    DerivativeSmoothVectors I (fixedRestriction σ J π hcomm) ≃L[ℂ]
      ambientFixedSmoothSubspace σ J π I :=
  derivativeEquiv π (fixedSubspace σ J) (fixedSubspace_invariant σ J π hcomm) I

@[simp]
theorem coe_fixedDerivativeEquiv_apply
    (v : DerivativeSmoothVectors I (fixedRestriction σ J π hcomm)) :
    (fixedDerivativeEquiv σ J π hcomm I v : DerivativeSmoothVectors I π) =
      derivativeInclusion π (fixedSubspace σ J) (fixedSubspace_invariant σ J π hcomm) I v :=
  rfl

/-- The fixed-level inclusion is a closed embedding for the genuine derivative topology. -/
theorem isClosedEmbedding_fixedDerivativeInclusion :
    IsClosedEmbedding
      (derivativeInclusion π (fixedSubspace σ J) (fixedSubspace_invariant σ J π hcomm) I) :=
  isClosedEmbedding_derivativeInclusion π (fixedSubspace σ J)
    (fixedSubspace_invariant σ J π hcomm) I

/-- The fixed-level inclusion has exactly the ambient smooth vectors that are J-fixed
as its range. -/
theorem range_fixedDerivativeInclusion :
    (derivativeInclusion π (fixedSubspace σ J) (fixedSubspace_invariant σ J π hcomm) I).range =
      ambientFixedSmoothSubspace σ J π I :=
  range_derivativeInclusion π (fixedSubspace σ J) (fixedSubspace_invariant σ J π hcomm) I

end Langlands.Archimedean.SmoothInvariantSubspace
