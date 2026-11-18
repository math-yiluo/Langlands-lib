import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.AffinePointClosedImmersion
import Langlands.GroupScheme.Torus.SplitPointTopology
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Compact real points and anisotropy -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

local instance realPointsTopology (G : GroupScheme (Spec (CommRingCat.of ℝ))) :
    TopologicalSpace (G.affinePoints (CommAlgCat.of ℝ ℝ)) :=
  G.affinePointsTopologicalSpace _

local instance realSplitTorusAffine (I : Type) [Finite I] :
    IsAffine (splitTorus (Spec (CommRingCat.of ℝ)) I).X.left := by
  have := isAffineHom_splitTorus_spec (CommRingCat.of ℝ) I
  exact isAffine_of_isAffineHom (splitTorus (Spec (CommRingCat.of ℝ)) I).X.hom

/-- Compactness of the full real point set in the regular-evaluation topology. -/
def HasCompactRealPoints (G : GroupScheme (Spec (CommRingCat.of ℝ))) : Prop :=
  IsCompact (Set.univ : Set (G.affinePoints (CommAlgCat.of ℝ ℝ)))

namespace RealCompactPoints

/-- The real unit group is not compact in its usual units topology. -/
theorem not_isCompact_univ_units :
    ¬ IsCompact (Set.univ : Set ℝˣ) := by
  intro hc
  obtain ⟨b, hb⟩ := (hc.image Units.continuous_val).bddAbove
  let a : ℝ := max b 0 + 1
  have ha : 0 < a := by
    dsimp [a]
    linarith [le_max_right b 0]
  have hba := hb ⟨Units.mk0 a (ne_of_gt ha), Set.mem_univ _, rfl⟩
  change a ≤ b at hba
  dsimp [a] at hba
  linarith [le_max_left b 0]

/-- A split torus with compact real points has no coordinates. -/
theorem isEmpty_of_hasCompactRealPoints_splitTorus (I : Type) [Finite I]
    (hc : HasCompactRealPoints (splitTorus (Spec (CommRingCat.of ℝ)) I)) :
    IsEmpty I := by
  classical
  let := Fintype.ofFinite I
  let e := splitTorus.affinePointsHomeomorph I (CommRingCat.of ℝ)
    (CommAlgCat.of ℝ ℝ)
  refine ⟨fun i => ?_⟩
  have he : Function.Surjective (fun p => e p i) := by
    intro a
    obtain ⟨p, hp⟩ := e.surjective (fun _ => a)
    exact ⟨p, congrFun hp i⟩
  have hu : (fun p => e p i) '' Set.univ = Set.univ :=
    Set.image_univ_of_surjective he
  exact not_isCompact_univ_units
    (hu ▸ hc.image ((continuous_apply i).comp e.continuous))

end RealCompactPoints

/-- Compact real points rule out every positive-dimensional closed split subtorus. -/
theorem isAnisotropic_of_hasCompactRealPoints
    (G : GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left]
    (hc : HasCompactRealPoints G) : IsAnisotropic G := by
  apply isAnisotropic_iff.mpr
  intro I _ i hi
  have : IsClosedImmersion i.hom.hom.left := hi
  have he := isClosedEmbedding_affinePointsTarget
    (splitTorus (Spec (CommRingCat.of ℝ)) I) G (CommAlgCat.of ℝ ℝ) i
  apply RealCompactPoints.isEmpty_of_hasCompactRealPoints_splitTorus I
  simpa only [HasCompactRealPoints, Set.preimage_univ] using he.isCompact_preimage hc

end Langlands.GroupScheme
