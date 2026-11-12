import Langlands.Global.AdelicRankOneOrbitHeightBound
import Langlands.Global.AdelicOrbitHeightCompactBounds
import Langlands.Global.AdelicMinimalParabolicNormCoordinates
import Langlands.Global.AdelicEmptyRootChamberReduction
import Langlands.Global.AdelicSiegelNormOne
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Actual rank-one chamber reduction from an arithmetic height bound -/

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
  (G : GroupScheme (Spec (CommRingCat.of F))) {d : ℕ}

/-- The ordered inverse of a unipotent, intrinsic norm-one and torus product
has the same selected-vector height as the inverse torus point. -/
theorem orbitHeight_inv_unipotent_mul_normOne_mul_torus
    (U L : GroupScheme (Spec (CommRingCat.of F)))
    (zU : U ⟶ G) (zL : L ⟶ G) (hU : IsUnipotent U)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ρ : MatrixRepresentation G (Fin d)) (b : Fin d)
    (hUline : (ρ.restrict zU).PreservesCoordinateLine b)
    (hLline : (ρ.restrict zL).PreservesCoordinateLine b)
    (x : AdelicGroupPoints F U) (m : normOneSubgroup F L)
    (s : AdelicGroupPoints F T.toGrp) :
    orbitHeight F G ρ (Pi.single b 1)
        (map F U G zU x * map F L G zL m * map F T.toGrp G i s)⁻¹ =
      orbitHeight F G ρ (Pi.single b 1) (map F T.toGrp G i s)⁻¹ := by
  have hfix := isOrbitVectorFixedBy_range_of_isUnipotent F G U zU ρ b hUline hU
  have hx := orbitHeight_mul_eq_of_fixed F G ρ (Pi.single b 1)
    (map F U G zU).toMonoidHom.range hfix
    (map F T.toGrp G i s⁻¹ * map F L G zL (m⁻¹ : normOneSubgroup F L))
    (map F U G zU x⁻¹) ⟨x⁻¹, rfl⟩
  simpa only [map_inv, Subgroup.coe_inv, mul_inv_rev, mul_assoc] using
    hx.trans (orbitHeight_mul_map_normOne F G L zL ρ b hLline
      (map F T.toGrp G i s⁻¹) m⁻¹)

/-- One positive constant bounds every inverse torus height in such a product
whose inverse full height is bounded, uniformly over a specified compact subgroup. -/
theorem exists_bound_on_inverse_torus_factors
    (U L : GroupScheme (Spec (CommRingCat.of F)))
    (zU : U ⟶ G) (zL : L ⟶ G) (hU : IsUnipotent U)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ρ : MatrixRepresentation G (Fin d)) (b : Fin d)
    (hUline : (ρ.restrict zU).PreservesCoordinateLine b)
    (hLline : (ρ.restrict zL).PreservesCoordinateLine b)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsCompact (K : Set (AdelicGroupPoints F G)))
    (C : ℝ) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (x : AdelicGroupPoints F U) (m : normOneSubgroup F L)
      (s : AdelicGroupPoints F T.toGrp) (k : AdelicGroupPoints F G), k ∈ K →
        orbitHeight F G ρ (Pi.single b 1)
            (map F U G zU x * map F L G zL m * map F T.toGrp G i s * k)⁻¹ ≤ C →
          orbitHeight F G ρ (Pi.single b 1) (map F T.toGrp G i s)⁻¹ ≤ D := by
  have hv : (Pi.single b (1 : F) : Fin d → F) ≠ 0 := by
    intro h
    have he := congrFun h b
    simp at he
  obtain ⟨B, hB, hdist⟩ := exists_pos_orbitHeight_bounds_of_isCompact F G ρ
    (Nat.zero_lt_of_lt b.isLt) hK
  refine ⟨B * C, mul_pos hB hC, ?_⟩
  intro x m s k hk hsmall
  have h := (hdist k⁻¹ (K.inv_mem hk)
    (map F U G zU x * map F L G zL m * map F T.toGrp G i s)⁻¹
    (Pi.single b 1) hv).2
  rw [← mul_inv_rev] at h
  rw [orbitHeight_inv_unipotent_mul_normOne_mul_torus F G U L zU zL hU
    T i ρ b hUline hLline] at h
  exact h.trans (mul_le_mul_of_nonneg_left hsmall hB.le)

end Langlands.Global.RepresentationGrowth

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)

/-- At least one actual exact minimal-parabolic eigenline has the uniform
rational-orbit arithmetic height bound. This is an input, not an existence theorem. -/
def HasBoundedMinimalParabolicEigenline : Prop :=
  ∃ (d : ℕ) (ρ : MatrixRepresentation G (Fin d)) (b : Fin d),
    ρ.HasExactCoordinateLineStabilizer (standardParabolic i ν ∅) b ∧
      HasUniformNormOneRationalOrbitHeightBound F G ρ (Pi.single b 1)

/-- The universal arithmetic rank-one assertion supplies the weaker existential
input, using the published actual Chevalley eigenline construction. -/
theorem hasBoundedMinimalParabolicEigenline_of_rankOne_heightStatement
    [LocallyOfFiniteType G.X.hom]
    (harith : RankOneParabolicRationalOrbitHeightBoundStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (α : characterLattice T)
    (hα : simpleRelativeRoots i ν = {α}) :
    HasBoundedMinimalParabolicEigenline F G T i ν := by
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  let : Fintype (relativeWeylGroup i) :=
    relativeWeylGroupFintype i (relativeRootSystem F G hG T i hi)
  obtain ⟨d, b, ρ, hline, hstab, hrel⟩ :=
    MatrixRepresentation.exists_exact_emptyStandardParabolic_stabilizer_positiveRootRelation
      i hG hi ν hν α hα
  exact ⟨d + 1, ρ, b, hstab, harith F G hG T i hi ν hν α hα (d + 1) ρ b hstab⟩

variable (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)

/-- In actual relative rank one, an arithmetic bound and positive norm coordinates
imply the complete weak chamber factorization for every prescribed Iwasawa compact. -/
theorem hasWeakChamberReduction_of_rankOne_height_and_coordinates
    (hG : IsConnectedReductive G)
    (hS : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (α : characterLattice T) (hα : simpleRelativeRoots i ν = {α})
    (hheight : HasBoundedMinimalParabolicEigenline F G T i ν)
    (hcoords : HasMinimalParabolicNormCoordinates F G T i ν T₀ j)
    (K : Subgroup (AdelicGroupPoints F G))
    (hK : IsParabolicIwasawaCompact F G
      (Standard.parabolicScheme i ν ∅) (Standard.parabolicHom i ν ∅) K) :
    HasWeakChamberReduction F G T i ν T₀ j K := by
  let : Mono i.hom.hom.left := hS.1.isSplitSubtorus.mono
  let : Fintype (relativeWeylGroup i) :=
    relativeWeylGroupFintype i (relativeRootSystem F G hG T i hS.1)
  obtain ⟨d, ρ, b, hstab, C, hC, hbound⟩ := hheight
  obtain ⟨hTline, hrel⟩ :=
    MatrixRepresentation.positiveRootRelation_of_exact_emptyStandardParabolic_stabilizer
      i hG hS.1 ν hS.2.1 α hα ρ b hstab
  have hUline : (ρ.restrict (Standard.unipotentHom i ν ∅)).PreservesCoordinateLine b := by
    intro Z x
    have hx : x ≫ (Standard.unipotentHom i ν ∅).hom.hom ∈
        (standardUnipotent i ν ∅).carrier Z := by
      rw [← (Standard.isRepresentedBy_unipotentHom i ν ∅).2]
      exact ⟨x, rfl⟩
    simpa only [MatrixRepresentation.pointMatrix_restrict] using
      (hstab Z (x ≫ (Standard.unipotentHom i ν ∅).hom.hom)).mp
        (standardUnipotent_le_standardParabolic i ν ∅ Z hx)
  have hLline : (ρ.restrict (Standard.leviHom i ν ∅)).PreservesCoordinateLine b := by
    intro Z x
    have hx : x ≫ (Standard.leviHom i ν ∅).hom.hom ∈
        (standardLevi i ν ∅).carrier Z := by
      rw [← (Standard.isRepresentedBy_leviHom i ν ∅).2]
      exact ⟨x, rfl⟩
    simpa only [MatrixRepresentation.pointMatrix_restrict] using
      (hstab Z (x ≫ (Standard.leviHom i ν ∅).hom.hom)).mp
        (standardLevi_le_standardParabolic i ν ∅ Z hx)
  obtain ⟨D, hD, hfactor⟩ := exists_bound_on_inverse_torus_factors F G
    (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅)
    (Standard.unipotentHom i ν ∅) (Standard.leviHom i ν ∅)
    (hS.isUnipotent_standard F G T i ν T₀ j) T i ρ b hUline hLline K hK.1.1 C hC
  let s : PositiveRealTorus.intrinsicSubgroup F T₀ → AdelicGroupPoints F T.toGrp :=
    fun a => map F T₀.toGrp T.toGrp (CommGroupScheme.groupHom j) a
  have hs (a : PositiveRealTorus.intrinsicSubgroup F T₀) :
      map F T.toGrp G i (s a) = positiveMap F G T i T₀ j a := by
    change (a.val ≫ (CommGroupScheme.groupHom j).hom.hom) ≫ i.hom.hom =
      a.val ≫ (CommGroupScheme.groupHom j ≫ i).hom.hom
    rw [Grp.comp_hom_hom, Category.assoc]
  let S : Set (AdelicGroupPoints F T.toGrp) := {z | ∃ a, z = (s a)⁻¹ ∧
    ∃ (x : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅))
      (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
      (k : AdelicGroupPoints F G), k ∈ K ∧
        orbitHeight F G ρ (Pi.single b 1)
          (map F _ G (Standard.unipotentHom i ν ∅) x *
            map F _ G (Standard.leviHom i ν ∅) m *
              positiveMap F G T i T₀ j a * k)⁻¹ ≤ C}
  have hSone : ∀ z ∈ S, map F T.toGrp G i z ∈ normOneSubgroup F G := by
    rintro z ⟨a, rfl, _⟩
    rw [map_inv, hs]
    exact (normOneSubgroup F G).inv_mem (hS.positiveMap_mem_normOne F G T i ν T₀ j a)
  have hShe : HasUniformTorusLineHeightBound F G T ρ b i S := by
    refine ⟨D, hD, ?_⟩
    rintro z ⟨a, rfl, x, m, k, hk, hsmall⟩
    rw [map_inv]
    apply hfactor x m (s a) k hk
    simpa only [hs] using hsmall
  obtain ⟨t, ht⟩ := exists_lower_rootNorm_inv_of_torusLineHeightBound
    F G T ρ b i hTline α hrel S hSone hShe
  refine ⟨t, fun g => ?_⟩
  obtain ⟨q, hq⟩ := hbound g⁻¹
  let y : normOneSubgroup F G := rationalNormOne F G q⁻¹ * g
  obtain ⟨x, m, a, k, hk, heq⟩ := hcoords.exists_iwasawa_factors F G T i ν T₀ j K hK y
  have hsmall : orbitHeight F G ρ (Pi.single b 1)
      (map F _ G (Standard.unipotentHom i ν ∅) x *
        map F _ G (Standard.leviHom i ν ∅) m *
          positiveMap F G T i T₀ j a * k)⁻¹ ≤ C := by
    rw [heq]
    simpa only [y, Subgroup.coe_mul, Subgroup.coe_inv, rationalNormOne_val,
      mul_inv_rev, map_inv, inv_inv] using hq
  have ha : a ∈ PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t := by
    intro β hβ
    have hb : β = α := by simpa only [hα, Set.mem_singleton_iff] using hβ
    subst β
    have h := ht (s a)⁻¹ ⟨a, rfl, x, m, k, hk, hsmall⟩
    rw [inv_inv] at h
    exact (PositiveRealTorus.normCharacter_pullback F T₀ T j α a).symm ▸ h
  refine ⟨q⁻¹, x, m, a, ha, k, hk, ?_⟩
  simpa only [y, Subgroup.coe_mul, rationalNormOne_val] using heq

end Langlands.Global.AdelicSiegelFactors
