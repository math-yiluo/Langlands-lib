import Langlands.Global.AdelicRankOneOrbitHeightBound
import Langlands.Global.AdelicSiegelNormOne
import Langlands.GroupScheme.Rational.CentralRootRestriction

/-! # Transferring centrally normalized heights to original torus roots -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix NNReal

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (T A : CommGroupScheme (Spec (CommRingCat.of F))) (f : A ⟶ T)

namespace PositiveRealTorus

/-- Remove an actual central torus coordinate from a torus point. The definition
itself does not require centrality or positivity. -/
def centralAdjustedTorusPoint (a : AdelicGroupPoints F A.toGrp)
    (s : AdelicGroupPoints F T.toGrp) : AdelicGroupPoints F T.toGrp :=
  (map F A.toGrp T.toGrp (CommGroupScheme.groupHom f) a)⁻¹ * s

/-- A root trivial on the adjusting torus has exactly the same normalized
idele norm before and after the adjustment. -/
theorem normCharacter_centralAdjustedTorusPoint_of_comp_eq_zero
    (α : characterLattice T) (hα : f ≫ α = 0)
    (a : AdelicGroupPoints F A.toGrp) (s : AdelicGroupPoints F T.toGrp) :
    normCharacter F T α (centralAdjustedTorusPoint F T A f a s) =
      normCharacter F T α s := by
  have ha : normCharacter F T α
      (map F A.toGrp T.toGrp (CommGroupScheme.groupHom f) a) = 1 := by
    change characterNorm F T.toGrp α.toMul _ = 1
    rw [← characterNorm_comp]
    change characterNorm F A.toGrp (f ≫ α).toMul a = 1
    rw [hα]
    exact characterNorm_zero F A.toGrp a
  rw [centralAdjustedTorusPoint, map_mul, map_inv, ha, inv_one, one_mul]

/-- Actual roots are unchanged by adjustment along an actual central split
torus, without any ambient norm-one inference. -/
theorem normCharacter_centralAdjustedTorusPoint
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : T.toGrp ⟶ G) (hA : IsSplitTorus A.toGrp)
    (hc : IsCentral (CommGroupScheme.groupHom f ≫ i))
    (α : characterLattice T) (hα : α ∈ relativeRoots i)
    (a : AdelicGroupPoints F A.toGrp) (s : AdelicGroupPoints F T.toGrp) :
    normCharacter F T α (centralAdjustedTorusPoint F T A f a s) =
      normCharacter F T α s :=
  normCharacter_centralAdjustedTorusPoint_of_comp_eq_zero F T A f α
    (root_restrict_eq_zero_of_isCentral i f hA hc hα) a s

end PositiveRealTorus

namespace RepresentationGrowth

variable (G : GroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (U L : GroupScheme (Spec (CommRingCat.of F))) (zU : U ⟶ G) (zL : L ⟶ G)

/-- Removing the central factor from an actual normalized parabolic product
adjusts only the torus coordinate, preserving the order of its other factors. -/
theorem centralAdjustedTorusPoint_factorization
    (hc : IsCentral (CommGroupScheme.groupHom f ≫ i))
    (a : AdelicGroupPoints F A.toGrp) (x : AdelicGroupPoints F U)
    (m : AdelicGroupPoints F L) (p : AdelicGroupPoints F G)
    (s : AdelicGroupPoints F T.toGrp)
    (hp : map F A.toGrp G (CommGroupScheme.groupHom f ≫ i) a * p =
      map F U G zU x * map F L G zL m * map F T.toGrp G i s) :
    p = map F U G zU x * map F L G zL m *
      map F T.toGrp G i (PositiveRealTorus.centralAdjustedTorusPoint F T A f a s) := by
  let bT := map F A.toGrp T.toGrp (CommGroupScheme.groupHom f) a
  let bG := map F T.toGrp G i bT
  have hcomp : map F A.toGrp G (CommGroupScheme.groupHom f ≫ i) a = bG := by
    change a ≫ (CommGroupScheme.groupHom f ≫ i).hom.hom =
      (a ≫ (CommGroupScheme.groupHom f).hom.hom) ≫ i.hom.hom
    simp only [Grp.comp_hom_hom, Category.assoc]
  have hcomm : Commute bG (map F U G zU x * map F L G zL m) := by
    rw [← hcomp]
    exact commute_of_mem_center (hc _ a) _
  apply mul_left_cancel (a := bG)
  rw [← hcomp, hp, hcomp]
  symm
  calc
    bG * (map F U G zU x * map F L G zL m *
        map F T.toGrp G i
          (PositiveRealTorus.centralAdjustedTorusPoint F T A f a s)) =
        (map F U G zU x * map F L G zL m) *
          (bG * map F T.toGrp G i
            (PositiveRealTorus.centralAdjustedTorusPoint F T A f a s)) := by
      rw [← mul_assoc, hcomm.eq, mul_assoc]
    _ = map F U G zU x * map F L G zL m * map F T.toGrp G i s := by
      simp only [PositiveRealTorus.centralAdjustedTorusPoint, map_mul, map_inv, bG, bT]
      group

/-- Intrinsic norm-one normalization of the full product forces intrinsic
norm-one membership of the adjusted torus image after the unipotent and
norm-one Levi factors are removed. The same removal preserves its height. -/
theorem centralAdjustedTorusPoint_mem_normOne_and_height
    (hc : IsCentral (CommGroupScheme.groupHom f ≫ i)) (hU : IsUnipotent U)
    {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hUline : (ρ.restrict zU).PreservesCoordinateLine j)
    (hLline : (ρ.restrict zL).PreservesCoordinateLine j)
    (hTline : (ρ.restrict i).PreservesCoordinateLine j)
    (a : AdelicGroupPoints F A.toGrp) (x : AdelicGroupPoints F U)
    (m : normOneSubgroup F L) (p : normOneSubgroup F G)
    (s : AdelicGroupPoints F T.toGrp)
    (hp : map F A.toGrp G (CommGroupScheme.groupHom f ≫ i) a * p =
      map F U G zU x * map F L G zL m * map F T.toGrp G i s) :
    map F T.toGrp G i (PositiveRealTorus.centralAdjustedTorusPoint F T A f a s) ∈
        normOneSubgroup F G ∧
      orbitHeight F G ρ (Pi.single j 1)
        (map F T.toGrp G i (PositiveRealTorus.centralAdjustedTorusPoint F T A f a s)) =
          orbitHeight F G ρ (Pi.single j 1) p := by
  have hfact := centralAdjustedTorusPoint_factorization F T A f G i U L zU zL
    hc a x (m : AdelicGroupPoints F L) (p : AdelicGroupPoints F G) s hp
  constructor
  · have hx : map F U G zU x ∈ normOneSubgroup F G :=
      range_le_normOne_of_charactersTrivialAlong F U G zU
        (charactersTrivialAlong_of_isUnipotent F U G zU hU) ⟨x, rfl⟩
    have hm : map F L G zL m ∈ normOneSubgroup F G :=
      map_normOneSubgroup_le F L G zL ⟨m, m.property, rfl⟩
    have he :
        map F T.toGrp G i (PositiveRealTorus.centralAdjustedTorusPoint F T A f a s) =
          (map F U G zU x * map F L G zL m)⁻¹ * p := by
      rw [hfact]
      group
    rw [he]
    exact (normOneSubgroup F G).mul_mem
      ((normOneSubgroup F G).inv_mem ((normOneSubgroup F G).mul_mem hx hm)) p.property
  · rw [hfact]
    exact (orbitHeight_unipotent_mul_normOne_mul_torus F G U L zU zL hU
      T i ρ j hUline hLline hTline x m
      (PositiveRealTorus.centralAdjustedTorusPoint F T A f a s)).symm

/-- Bounded heights of root-preserving intrinsic norm-one torus adjustments
control the original torus family, uniformly before its points are chosen. -/
theorem hasUniformRootBound_of_normOne_torus_adjustments
    {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hTline : (ρ.restrict i).PreservesCoordinateLine j)
    (α : characterLattice T)
    (hrel : HasPositiveIntegralRootCharacterRelation i α
      (ρ.torusCoordinateLineCharacter i j hTline))
    (S : Set (AdelicGroupPoints F T.toGrp))
    (C : ℝ) (hC : 0 < C)
    (hS : ∀ s ∈ S, ∃ s' : AdelicGroupPoints F T.toGrp,
      map F T.toGrp G i s' ∈ normOneSubgroup F G ∧
        PositiveRealTorus.normCharacter F T α s' =
          PositiveRealTorus.normCharacter F T α s ∧
        orbitHeight F G ρ (Pi.single j 1) (map F T.toGrp G i s') ≤ C) :
    PositiveRealTorus.HasUniformCharacterBound F T α S := by
  let S' : Set (AdelicGroupPoints F T.toGrp) :=
    {s' | map F T.toGrp G i s' ∈ normOneSubgroup F G ∧
      orbitHeight F G ρ (Pi.single j 1) (map F T.toGrp G i s') ≤ C}
  have hh : HasUniformTorusLineHeightBound F G T ρ j i S' :=
    ⟨C, hC, fun _ hs => hs.2⟩
  obtain ⟨B, hB⟩ :=
    PositiveRealTorus.hasUniformCharacterBound_of_positiveIntegralRootRelation F G T i
      hrel S' (fun _ hs => hs.1)
      (hasUniformCharacterBound_of_torusLineHeightBound F G T ρ j i hTline S' hh)
  refine ⟨B, ?_⟩
  intro s hs
  obtain ⟨s', hn, he, hb⟩ := hS s hs
  rw [← he]
  exact hB s' ⟨hn, hb⟩

end RepresentationGrowth
end Langlands.Global
