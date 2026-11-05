import Langlands.Geometry.Building.CocharacterUniformizerEvaluation
import Langlands.GroupScheme.Rational.PointTopology
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.BruhatTits.Unipotent.CocharacterContraction
import Mathlib.Topology.Maps.Proper.Basic

/-! # A positive torus character detects compact escape of cocharacter powers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology Filter
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.DynamicUnipotentContainment

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable {F : Type u} [Field F]
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))}
    (i : T.toGrp ⟶ G)

/-- The powers of a specified torus cocharacter value in the ambient group. -/
def cocharacterPointPowers (ζ : cocharacterLattice T) (t : Fˣ) :
    ℕ → rationalPoints G :=
  fun n => cocharPoint (CommGroupScheme.groupHom ζ ≫ i) t ^ n

/-- Intrinsic torus evaluation and the contraction coordinate give the same ambient point. -/
theorem cocharPoint_comp_eq_map_cocharacterPoints (ζ : cocharacterLattice T) (t : Fˣ) :
    cocharPoint (CommGroupScheme.groupHom ζ ≫ i) t =
      rationalPoints.map i (CocharacterUniformizer.cocharacterPoints F T ζ t) := by
  rw [cocharPoint_eq]
  rfl

variable [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
    [IsAffine T.X.left] [IsAffine G.X.left]
    [IsClosedImmersion i.hom.hom.left]

local instance : TopologicalSpace (rationalPoints T.toGrp) := rationalPointTopology F T.X
local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- A positive character forces powers of an actual cocharacter value to leave
every ambient compact set, for any unit whose field powers tend to zero. -/
theorem eventually_cocharacterPoints_pow_notMem
    (ζ : cocharacterLattice T) (t : Fˣ)
    (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0))
    (α : characterLattice T) (hα : 0 < latticePairing T α ζ)
    (C : Set (rationalPoints G)) (hC : IsCompact C) :
    ∀ᶠ n : ℕ in atTop,
      (rationalPoints.map i (CocharacterUniformizer.cocharacterPoints F T ζ t)) ^ n ∉ C := by
  let χ : rationalCharacters T.toGrp := (rationalCharacters.equivCharacterLattice T).symm α
  let f : rationalPoints T.toGrp → F := fun a => (rationalCharacterEval χ a : F)
  have hf : Continuous f :=
    Units.continuous_val.comp (continuous_rationalCharacterEval T.toGrp χ)
  have he : IsClosedEmbedding (rationalPoints.map i) :=
    isClosedEmbedding_rationalPointMap F i.hom.hom
  let D : Set (rationalPoints T.toGrp) := rationalPoints.map i ⁻¹' C
  have hD : IsCompact D := he.isProperMap.isCompact_preimage hC
  have hclosed : IsClosed (f '' D) := (hD.image hf).isClosed
  have hzero : (0 : F) ∉ f '' D := by
    rintro ⟨a, _, ha⟩
    exact (rationalCharacterEval χ a).ne_zero ha
  let d : ℕ := (latticePairing T α ζ).toNat
  have hd : 0 < d := by
    dsimp [d]
    omega
  have hcast : (d : ℤ) = latticePairing T α ζ := Int.toNat_of_nonneg hα.le
  have hvalue : ∀ n : ℕ, f ((CocharacterUniformizer.cocharacterPoints F T ζ t) ^ n) =
      ((t : F) ^ n) ^ d := by
    intro n
    dsimp only [f]
    rw [map_pow, CocharacterUniformizer.rationalCharacterEval_cocharacterPoints,
      ← hcast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_right_comm]
  have hlim : Tendsto (fun n : ℕ =>
      f ((CocharacterUniformizer.cocharacterPoints F T ζ t) ^ n)) atTop (𝓝 0) := by
    simp_rw [hvalue]
    simpa only [zero_pow (Nat.ne_of_gt hd)] using ht.pow d
  filter_upwards [hlim (hclosed.isOpen_compl.mem_nhds hzero)] with n hn
  intro hnC
  apply hn
  refine ⟨(CocharacterUniformizer.cocharacterPoints F T ζ t) ^ n, ?_, rfl⟩
  change rationalPoints.map i ((CocharacterUniformizer.cocharacterPoints F T ζ t) ^ n) ∈ C
  simpa only [map_pow] using hnC

/-- The same compact escape in the explicit cocharacter-point convention used by contraction. -/
theorem eventually_cocharPoint_pow_notMem
    (ζ : cocharacterLattice T) (t : Fˣ)
    (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0))
    (α : characterLattice T) (hα : 0 < latticePairing T α ζ)
    (C : Set (rationalPoints G)) (hC : IsCompact C) :
    ∀ᶠ n : ℕ in atTop, cocharPoint (CommGroupScheme.groupHom ζ ≫ i) t ^ n ∉ C := by
  rw [cocharPoint_comp_eq_map_cocharacterPoints]
  exact eventually_cocharacterPoints_pow_notMem i ζ t ht α hα C hC

/-- The defined ambient power sequence eventually avoids every compact set. -/
theorem eventually_cocharacterPointPowers_notMem
    (ζ : cocharacterLattice T) (t : Fˣ)
    (ht : Tendsto (fun n : ℕ => (t : F) ^ n) atTop (𝓝 0))
    (α : characterLattice T) (hα : 0 < latticePairing T α ζ)
    (C : Set (rationalPoints G)) (hC : IsCompact C) :
    ∀ᶠ n : ℕ in atTop, cocharacterPointPowers i ζ t n ∉ C :=
  eventually_cocharPoint_pow_notMem i ζ t ht α hα C hC

end Langlands.BruhatTits.DynamicUnipotentContainment
