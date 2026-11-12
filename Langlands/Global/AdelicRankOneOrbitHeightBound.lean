import Langlands.Global.AdelicPositiveRootCharacterRelation
import Langlands.Global.AdelicHeightMinimumLeviRestriction
import Langlands.GroupScheme.Rational.RankOneStandardParabolicLineCharacter

/-! # The arithmetic rank-one height input and its minimum/torus consequences -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix NNReal

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) {n : ℕ}

/-- A positive uniform bound after an actual rational translate, on ambient
norm-one points and for the specified actual vector representation. -/
def HasUniformNormOneRationalOrbitHeightBound
    (ρ : MatrixRepresentation G (Fin n)) (v : Fin n → F) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ g : normOneSubgroup F G,
    ∃ q : RationalGroupPoints F G,
      orbitHeight F G ρ v ((g : AdelicGroupPoints F G) * rational F G q) ≤ C

/-- The full actual rational-group approximate-minimum inequality. -/
def IsRationalOrbitHeightApproximateMinimum
    (ρ : MatrixRepresentation G (Fin n)) (v : Fin n → F)
    (c : ℝ) (g : AdelicGroupPoints F G) : Prop :=
  ∀ q : RationalGroupPoints F G,
    orbitHeight F G ρ v g ≤
      c * orbitHeight F G ρ v (g * rational F G q)

/-- The uniform rational-orbit bound controls every nonnegative-factor
approximate minimum, with the same constant. -/
theorem HasUniformNormOneRationalOrbitHeightBound.bounds_approximate_minima
    {ρ : MatrixRepresentation G (Fin n)} {v : Fin n → F}
    (h : HasUniformNormOneRationalOrbitHeightBound F G ρ v) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 ≤ c →
      ∀ g : normOneSubgroup F G,
        IsRationalOrbitHeightApproximateMinimum F G ρ v c g →
          orbitHeight F G ρ v g ≤ c * C := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun c hc g hmin => ?_⟩
  obtain ⟨q, hq⟩ := hbound g
  exact (hmin q).trans (mul_le_mul_of_nonneg_left hq hc)

/-- Conversely, bounding the exact minima suffices: actual minima exist on
each rational orbit of every nonzero rational vector. -/
theorem hasUniformNormOneRationalOrbitHeightBound_iff_bound_on_minima
    (ρ : MatrixRepresentation G (Fin n)) (v : Fin n → F) (hv : v ≠ 0) :
    HasUniformNormOneRationalOrbitHeightBound F G ρ v ↔
      ∃ C : ℝ, 0 < C ∧ ∀ g : normOneSubgroup F G,
        IsRationalOrbitHeightApproximateMinimum F G ρ v 1 g →
          orbitHeight F G ρ v g ≤ C := by
  constructor
  · intro h
    obtain ⟨C, hC, hmin⟩ := h.bounds_approximate_minima F G
    exact ⟨C, hC, fun g hg => by simpa only [one_mul] using hmin 1 zero_le_one g hg⟩
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, fun g => ?_⟩
    let Q : Subgroup (RationalGroupPoints F G) := ⊤
    let q : Q := minimumOrbitTranslate F G ρ Q v hv g
    let y : normOneSubgroup F G := g * rationalNormOne F G q
    have hy : IsRationalOrbitHeightApproximateMinimum F G ρ v 1 y := by
      intro r
      simpa only [y, Subgroup.coe_mul, rationalNormOne_val, one_mul] using
        minimumOrbitTranslate_min F G ρ Q v hv g (⟨r, Subgroup.mem_top r⟩ : Q)
    exact ⟨q, hbound y hy⟩

/-- An actual unipotent line stabilizer and an intrinsic norm-one line
stabilizer do not change the selected-vector height of a torus factor.
No minimum inequality is transported through these right factors. -/
theorem orbitHeight_unipotent_mul_normOne_mul_torus
    (U L : GroupScheme (Spec (CommRingCat.of F)))
    (zU : U ⟶ G) (zL : L ⟶ G) (hU : IsUnipotent U)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hUline : (ρ.restrict zU).PreservesCoordinateLine j)
    (hLline : (ρ.restrict zL).PreservesCoordinateLine j)
    (hTline : (ρ.restrict i).PreservesCoordinateLine j)
    (x : AdelicGroupPoints F U) (m : normOneSubgroup F L)
    (s : AdelicGroupPoints F T.toGrp) :
    orbitHeight F G ρ (Pi.single j 1)
        (map F U G zU x * map F L G zL m * map F T.toGrp G i s) =
      orbitHeight F G ρ (Pi.single j 1) (map F T.toGrp G i s) := by
  have hfix := isOrbitVectorFixedBy_range_of_isUnipotent F G U zU ρ j hUline hU
  have hx :
      orbitHeight F G ρ (Pi.single j 1) (map F U G zU x) =
        orbitHeight F G ρ (Pi.single j 1) 1 := by
    simpa only [one_mul] using
      orbitHeight_mul_eq_of_fixed F G ρ (Pi.single j 1)
        (map F U G zU).toMonoidHom.range hfix 1 (map F U G zU x) ⟨x, rfl⟩
  rw [orbitHeight_mul_map_eq_lineCharacterNorm F G T.toGrp i ρ j hTline,
    orbitHeight_mul_map_normOne F G L zL ρ j hLline, hx]
  simpa only [one_mul] using
    (orbitHeight_mul_map_eq_lineCharacterNorm F G T.toGrp i ρ j hTline 1 s).symm

/-- A supplied arithmetic bound controls the torus-coordinate heights of
norm-one approximate minima with actual unipotent and norm-one Levi factors. -/
theorem hasUniformTorusLineHeightBound_of_factored_approximate_minima
    (U L : GroupScheme (Spec (CommRingCat.of F)))
    (zU : U ⟶ G) (zL : L ⟶ G) (hU : IsUnipotent U)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hUline : (ρ.restrict zU).PreservesCoordinateLine j)
    (hLline : (ρ.restrict zL).PreservesCoordinateLine j)
    (hTline : (ρ.restrict i).PreservesCoordinateLine j)
    (hbound : HasUniformNormOneRationalOrbitHeightBound F G ρ (Pi.single j 1))
    (c : ℝ) (hc : 0 < c) (S : Set (AdelicGroupPoints F T.toGrp))
    (hS : ∀ s ∈ S,
      ∃ (x : AdelicGroupPoints F U) (m : normOneSubgroup F L)
        (p : normOneSubgroup F G),
        (p : AdelicGroupPoints F G) =
          map F U G zU x * map F L G zL m * map F T.toGrp G i s ∧
          IsRationalOrbitHeightApproximateMinimum F G ρ (Pi.single j 1) c p) :
    HasUniformTorusLineHeightBound F G T ρ j i S := by
  obtain ⟨C, hC, hmin⟩ := hbound.bounds_approximate_minima F G
  refine ⟨c * C, mul_pos hc hC, ?_⟩
  intro s hs
  obtain ⟨x, m, p, hp, hpm⟩ := hS s hs
  have h := hmin c hc.le p hpm
  rw [hp, orbitHeight_unipotent_mul_normOne_mul_torus F G U L zU zL hU
    T i ρ j hUline hLline hTline] at h
  exact h

/-- The remaining arithmetic rank-one input. The singleton is the actual
simple-relative-root set, and the line stabilizer is the actual minimal
standard parabolic on all scheme tests. This is a statement, not a proof. -/
def RankOneParabolicRationalOrbitHeightBoundStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G),
        IsMaximalSplitTorus i →
          ∀ (ν : cocharacterLattice T), IsGenericCocharacter i ν →
            ∀ α : characterLattice T, simpleRelativeRoots i ν = {α} →
              ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)) (j : Fin n),
                ρ.HasExactCoordinateLineStabilizer (standardParabolic i ν ∅) j →
                  HasUniformNormOneRationalOrbitHeightBound F G ρ (Pi.single j 1)

end Langlands.Global.RepresentationGrowth
