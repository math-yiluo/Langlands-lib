import Langlands.Representation.Compact.FiniteMean
import Langlands.Representation.Smooth.Definitions
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Averaging smooth complex representations over compact open subgroups

The normalized average uses a finite orbit, equivalently cosets of the vector's
stabilizer inside the compact subgroup. No topology is imposed on the module.
-/

namespace Langlands.Compact

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Smooth vectors have finite orbits under compact open subgroups. -/
theorem finite_orbit_of_smooth (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V) :
    Finite (orbit (ρ.comp K.toSubgroup.subtype) v) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  let : MulAction K V := representationAction (ρ.comp K.toSubgroup.subtype)
  obtain ⟨U, hU⟩ := hρ v
  have hle : U.toSubgroup.subgroupOf K.toSubgroup ≤ MulAction.stabilizer K v := by
    intro k hk
    exact hU ⟨k.val, hk⟩
  have hopen : IsOpen (MulAction.stabilizer K v : Set K) :=
    Subgroup.isOpen_mono hle
      (Subgroup.subgroupOf_isOpen K.toSubgroup U.toSubgroup U.isOpen)
  let : Finite (K ⧸ MulAction.stabilizer K v) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  exact Finite.of_equiv (K ⧸ MulAction.stabilizer K v)
    (MulAction.orbitEquivQuotientStabilizer K v).symm

/-- Normalized compact-subgroup averaging as a complex linear endomorphism. -/
noncomputable def averageMap (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) : V →ₗ[ℂ] V where
  toFun := orbitMean (ρ.comp K.toSubgroup.subtype)
  map_add' v w := by
    let := finite_orbit_of_smooth ρ hρ K hK v
    let := finite_orbit_of_smooth ρ hρ K hK w
    let := finite_orbit_of_smooth ρ hρ K hK (v + w)
    exact orbitMean_add _ v w
  map_smul' c v := by
    let := finite_orbit_of_smooth ρ hρ K hK v
    let := finite_orbit_of_smooth ρ hρ K hK (c • v)
    exact orbitMean_smul _ c v

/-- The linear map between fixed-vector submodules induced by an intertwiner. -/
noncomputable def fixedVectorMap (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (f : ρ.IntertwiningMap σ) (K : Subgroup G) :
    fixedVectors ρ K →ₗ[ℂ] fixedVectors σ K :=
  (f.toLinearMap.comp (fixedVectors ρ K).subtype).codRestrict
    (fixedVectors σ K) (by
      intro v k
      change σ k.val (f v.val) = f v.val
      rw [← f.isIntertwining ρ σ k.val v.val]
      exact congrArg f (v.property k))

end Langlands.Compact
