import Langlands.Representation.Plancherel.RationalNormKernelTopology

/-! # Compact-open topology on actual unramified characters -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))

section PointTopology

variable [TopologicalSpace (GroupScheme.rationalPoints G)]

/-- The existing actual-image character equivalence preserves compact-open
topologies under the same projection-continuity premise. -/
def rationalImageUnramifiedContinuousEquiv
    (h : Continuous (rationalValuationImageProjection G)) :
    rationalImageCharacters G ≃ₜ*
      unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) where
  toMulEquiv := rationalImageUnramifiedEquiv G h
  continuous_toFun :=
    (rationalValuationImageContinuousProjection G h).continuous_comp_left.subtype_mk _
  continuous_invFun := by
    apply (ContinuousMonoidHom.isClosedEmbedding_coe
      (A := rationalDiscreteValuationImage G) (B := ℂˣ)).isInducing.continuous_iff.mpr
    apply continuous_pi
    intro a
    obtain ⟨g, rfl⟩ := rationalValuationImageProjection_surjective G a
    change Continuous (fun chi => (rationalImageUnramifiedEquiv G h).symm chi
      (rationalValuationImageProjection G g))
    have he : (fun chi => (rationalImageUnramifiedEquiv G h).symm chi
        (rationalValuationImageProjection G g)) =
        (fun chi => chi.val g) := by
      funext chi
      exact rationalImageUnramifiedDescend_projection G chi g
    rw [he]
    exact (continuous_eval_const g).comp continuous_subtype_val

@[simp] theorem rationalImageUnramifiedContinuousEquiv_toMulEquiv
    (h : Continuous (rationalValuationImageProjection G)) :
    (rationalImageUnramifiedContinuousEquiv G h).toMulEquiv =
      rationalImageUnramifiedEquiv G h := rfl

/-- Restrict the existing pullback/descent equivalence to norm-one characters. -/
def rationalUnitaryUnramifiedEquiv
    (h : Continuous (rationalValuationImageProjection G)) :
    unitaryCharacters (rationalDiscreteValuationImage G) ≃*
      unitaryUnramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) where
  toFun chi :=
    ⟨(rationalImageUnramifiedEquiv G h chi.val).val,
      ⟨(rationalImageUnramifiedEquiv G h chi.val).property,
        (rationalImageCharacterPullback_unitary_iff G chi.val).mpr chi.property⟩⟩
  invFun chi :=
    ⟨(rationalImageUnramifiedEquiv G h).symm ⟨chi.val, chi.property.1⟩, by
      intro a
      obtain ⟨g, rfl⟩ := rationalValuationImageProjection_surjective G a
      change ‖(rationalImageUnramifiedDescend G ⟨chi.val, chi.property.1⟩
        (rationalValuationImageProjection G g) : ℂ)‖ = 1
      rw [rationalImageUnramifiedDescend_projection]
      exact chi.property.2 g⟩
  left_inv chi := by
    apply Subtype.ext
    exact (rationalImageUnramifiedEquiv G h).symm_apply_apply chi.val
  right_inv chi := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro g
    exact rationalImageUnramifiedDescend_projection G _ g
  map_mul' chi eta := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro g
    rfl

/-- The norm-one restriction also preserves the existing subspace topologies. -/
def rationalUnitaryUnramifiedContinuousEquiv
    (h : Continuous (rationalValuationImageProjection G)) :
    unitaryCharacters (rationalDiscreteValuationImage G) ≃ₜ*
      unitaryUnramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) where
  toMulEquiv := rationalUnitaryUnramifiedEquiv G h
  continuous_toFun :=
    ((continuous_subtype_val.comp
      (rationalImageUnramifiedContinuousEquiv G h).continuous).comp
        continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((rationalImageUnramifiedContinuousEquiv G h).symm.continuous.comp
      (continuous_subtype_val.subtype_mk _)).subtype_mk _

end PointTopology

section CanonicalTopology

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance instRationalUnramifiedCharacterTopology1 : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- Actual image characters and continuous unramified characters are isomorphic
for compact-open topologies in the canonical rational-point topology. -/
def rationalCanonicalImageUnramifiedContinuousEquiv :
    rationalImageCharacters G ≃ₜ*
      unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) :=
  rationalImageUnramifiedContinuousEquiv G (continuous_rationalValuationImageProjection G)

@[simp] theorem rationalCanonicalImageUnramifiedContinuousEquiv_toMulEquiv :
    (rationalCanonicalImageUnramifiedContinuousEquiv G).toMulEquiv =
      rationalCanonicalImageUnramifiedEquiv G := rfl

@[simp] theorem rationalCanonicalImageUnramifiedContinuousEquiv_apply
    (chi : rationalImageCharacters G) (g : GroupScheme.rationalPoints G) :
    (rationalCanonicalImageUnramifiedContinuousEquiv G chi).val g =
      chi (rationalValuationImageProjection G g) := rfl

@[simp] theorem rationalCanonicalImageUnramifiedContinuousEquiv_symm_projection
    (chi : unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul))
    (g : GroupScheme.rationalPoints G) :
    (rationalCanonicalImageUnramifiedContinuousEquiv G).symm chi
        (rationalValuationImageProjection G g) = chi.val g :=
  rationalImageUnramifiedDescend_projection G chi g

/-- The circle-valued dual of the actual discrete valuation image is exactly
the existing unitary unramified subgroup, with its compact-open subspace topology. -/
def rationalCanonicalUnitaryImageUnramifiedContinuousEquiv :
    rationalUnitaryImageCharacters G ≃ₜ*
      unitaryUnramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) :=
  (rationalUnitaryImageContinuousEquiv G).trans
    (rationalUnitaryUnramifiedContinuousEquiv G
      (continuous_rationalValuationImageProjection G))

@[simp] theorem rationalCanonicalUnitaryImageUnramifiedContinuousEquiv_apply
    (chi : rationalUnitaryImageCharacters G) (g : GroupScheme.rationalPoints G) :
    (((rationalCanonicalUnitaryImageUnramifiedContinuousEquiv G chi).val g : ℂˣ) : ℂ) =
      (chi (rationalValuationImageProjection G g) : ℂ) := rfl

/-- Compactness of the actual unitary unramified character subgroup requires
no finite-rank assertion about the valuation image. -/
theorem compactSpace_rationalUnitaryUnramifiedCharacters :
    CompactSpace
      (unitaryUnramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul)) :=
  (rationalCanonicalUnitaryImageUnramifiedContinuousEquiv G).toHomeomorph.compactSpace

end CanonicalTopology

end Langlands.Plancherel
