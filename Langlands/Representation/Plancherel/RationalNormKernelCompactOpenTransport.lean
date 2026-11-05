import Langlands.Representation.Plancherel.RationalNormKernelSmoothDual
import Langlands.Representation.Smooth.FixedVectors.FiniteTypes

/-! # Actual compact-open inclusion from the rational norm kernel -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

universe uR uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalNormKernelCompactOpenTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X

/-- The given open subgroup of the actual norm kernel, viewed through its actual
inclusion as an open subgroup of the ambient rational-point group. -/
def rationalNormKernelAmbientLevel
    (K : OpenSubgroup (rationalCommonNormKernel G)) :
    OpenSubgroup (GroupScheme.rationalPoints G) where
  toSubgroup := K.toSubgroup.map (rationalCommonNormKernel G).subtype
  isOpen' := (isOpen_rationalCommonNormKernel G).isOpenMap_subtype_val _ K.isOpen

/-- The ambient level has exactly the image set under the actual inclusion. -/
theorem rationalNormKernelAmbientLevel_coe
    (K : OpenSubgroup (rationalCommonNormKernel G)) :
    (rationalNormKernelAmbientLevel G K : Set (GroupScheme.rationalPoints G)) =
      Subtype.val '' (K : Set (rationalCommonNormKernel G)) := rfl

/-- Compactness is preserved by the continuous actual subgroup inclusion. -/
theorem isCompact_rationalNormKernelAmbientLevel
    (K : OpenSubgroup (rationalCommonNormKernel G))
    (hK : IsCompact (K : Set (rationalCommonNormKernel G))) :
    IsCompact (rationalNormKernelAmbientLevel G K : Set (GroupScheme.rationalPoints G)) :=
  hK.image continuous_subtype_val

/-- The image subgroup lies in the original actual norm kernel. -/
theorem rationalNormKernelAmbientLevel_le
    (K : OpenSubgroup (rationalCommonNormKernel G)) :
    (rationalNormKernelAmbientLevel G K).toSubgroup ≤ rationalCommonNormKernel G := by
  rintro g ⟨h, _, rfl⟩
  exact h.property

/-- Pulling the ambient level back through the same inclusion recovers K. -/
@[simp]
theorem rationalNormKernelAmbientLevel_comap
    (K : OpenSubgroup (rationalCommonNormKernel G)) :
    (rationalNormKernelAmbientLevel G K).toSubgroup.comap
      (rationalCommonNormKernel G).subtype = K.toSubgroup := by
  ext h
  constructor
  · rintro ⟨k, hk, hkh⟩
    exact (Subtype.ext hkh : k = h) ▸ hk
  · intro hh
    exact ⟨h, hh, rfl⟩

variable {R : Type uR} [CommRing R]
  {V : Type uV} [AddCommGroup V] [Module R V]

/-- Actual restriction has precisely the ambient-level fixed vectors. -/
theorem fixedVectors_rationalNormKernelAmbientLevel
    (ρ : Representation R (GroupScheme.rationalPoints G) V)
    (K : OpenSubgroup (rationalCommonNormKernel G)) :
    fixedVectors (ρ.comp (rationalCommonNormKernel G).subtype) K.toSubgroup =
      fixedVectors ρ (rationalNormKernelAmbientLevel G K).toSubgroup := by
  simpa only [rationalNormKernelAmbientLevel_comap] using
    fixedVectors_comp_subtype ρ (rationalCommonNormKernel G)
      (rationalNormKernelAmbientLevel G K).toSubgroup
      (rationalNormKernelAmbientLevel_le G K)

/-- The invariant algebraic-dual condition uses exactly the same actual elements
on the restricted action and on the transported ambient level. -/
theorem dualInvariant_rationalNormKernelAmbientLevel_iff
    (ρ : Representation R (GroupScheme.rationalPoints G) V)
    (K : OpenSubgroup (rationalCommonNormKernel G)) (ℓ : Module.Dual R V) :
    (∀ k ∈ K, ∀ v, ℓ ((ρ.comp (rationalCommonNormKernel G).subtype) k v) = ℓ v) ↔
      (∀ k ∈ rationalNormKernelAmbientLevel G K, ∀ v, ℓ (ρ k v) = ℓ v) := by
  constructor
  · intro h k hk v
    obtain ⟨k', hk', rfl⟩ := hk
    exact h k' hk' v
  · intro h k hk v
    exact h k ⟨k, hk, rfl⟩ v

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- Inverse coefficients are unchanged when restricted through the actual
inclusion, on the same vector and underlying algebraic functional. -/
theorem inverseCoefficient_rationalNormKernel_restrict
    (ρ : Representation R (GroupScheme.rationalPoints G) V)
    (ℓ : Module.Dual R V) (v : V) (g : rationalCommonNormKernel G) :
    ℓ ((ρ.comp (rationalCommonNormKernel G).subtype) g⁻¹ v) =
      ℓ (ρ (g : GroupScheme.rationalPoints G)⁻¹ v) := rfl

end Langlands.Plancherel
