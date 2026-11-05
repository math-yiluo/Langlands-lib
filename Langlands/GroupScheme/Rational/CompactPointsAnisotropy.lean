import Langlands.GroupScheme.Rational.CompactPointsAnisotropyStatement
import Langlands.GroupScheme.Torus.SplitPointTopology
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedCompactness

/-! # Compact canonical rational points force anisotropy -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance splitTorusAffine (I : Type u) [Finite I] :
    IsAffine (splitTorus (Spec (CommRingCat.of F)) I).X.left := by
  have := isAffineHom_splitTorus_spec (CommRingCat.of F) I
  exact isAffine_of_isAffineHom (splitTorus (Spec (CommRingCat.of F)) I).X.hom

/-- The full unit group of a nonarchimedean local field is not compact. -/
theorem not_isCompact_univ_units :
    ¬ IsCompact (Set.univ : Set Fˣ) := by
  intro hc
  obtain ⟨b, hb, hbound⟩ :=
    IsCompact.exists_valuative_bound (hc.image Units.continuous_val)
  obtain ⟨a, ha⟩ := Valuation.IsNontrivial.exists_one_lt
    (v := ValuativeRel.valuation F)
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have h := hbound (a * b) ⟨Units.mk0 (a * b) (mul_ne_zero ha0 hb), Set.mem_univ _, rfl⟩
  have hvb : 0 < ValuativeRel.valuation F b := by
    exact zero_lt_iff.mpr ((ValuativeRel.valuation F).ne_zero_iff.mpr hb)
  have hle : ValuativeRel.valuation F a ≤ 1 := by
    have hh := (ValuativeRel.valuation F).vle_iff_le.mp h
    rw [map_mul] at hh
    exact (mul_le_iff_le_one_left hvb).mp hh
  exact ha.not_ge hle

/-- Compactness of the full point set of a split torus forces its index type to be empty. -/
theorem isEmpty_of_isCompact_splitTorus (I : Type u) [Finite I] :
    letI : TopologicalSpace (rationalPoints (splitTorus (Spec (CommRingCat.of F)) I)) :=
      rationalPointTopology F (splitTorus (Spec (CommRingCat.of F)) I).X
    IsCompact (Set.univ : Set (rationalPoints (splitTorus (Spec (CommRingCat.of F)) I))) →
      IsEmpty I := by
  classical
  let := Fintype.ofFinite I
  let T := splitTorus (Spec (CommRingCat.of F)) I
  let : TopologicalSpace (rationalPoints T) := rationalPointTopology F T.X
  let : TopologicalSpace (T.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    T.affinePointsTopologicalSpace _
  intro hc
  refine ⟨fun i => ?_⟩
  let e := (rationalPointsAffineHomeomorph T).trans
    (splitTorus.affinePointsHomeomorph I (CommRingCat.of F)
      (CommAlgCat.of (CommRingCat.of F) F)).toHomeomorph
  have he : Function.Surjective (fun p : rationalPoints T => e p i) := by
    intro a
    obtain ⟨p, hp⟩ := e.surjective (fun _ => a)
    exact ⟨p, congrFun hp i⟩
  have hu : (fun p : rationalPoints T => e p i) '' Set.univ = Set.univ :=
    Set.image_univ_of_surjective he
  exact not_isCompact_univ_units F
    (hu ▸ hc.image ((continuous_apply i).comp e.continuous))

/-- A compact actual affine rational-point group contains no nontrivial split subtorus. -/
theorem isAnisotropic_of_isCompact_rationalPoints
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsCompact (Set.univ : Set (rationalPoints G)) → IsAnisotropic G := by
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro hc
  apply isAnisotropic_iff.mpr
  intro I _ i hi
  have : IsClosedImmersion i.hom.hom.left := hi
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  let : TopologicalSpace (rationalPoints (splitTorus (Spec (CommRingCat.of F)) I)) :=
    rationalPointTopology F (splitTorus (Spec (CommRingCat.of F)) I).X
  have he := isClosedEmbedding_rationalPointMap F i.hom.hom
  exact isEmpty_of_isCompact_splitTorus F I (by
    simpa only [Set.preimage_univ] using he.isCompact_preimage hc)

/-- Exact proof of the published auxiliary compactness-to-anisotropy target. -/
theorem compactPointsAnisotropy_proof : CompactPointsAnisotropyStatement.{u} := by
  intro F _ _ _ _ G _
  exact isAnisotropic_of_isCompact_rationalPoints F G

end Langlands.GroupScheme
