import Langlands.Global.AdelicSubgroupQuotient
import Langlands.Global.AdelicGroupQuotient
import Langlands.Global.SplitUnipotentRationalQuotientCompact
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof

/-! # Rational quotients of represented adelic subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicSubgroupPoints

open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  {H G : GroupScheme (Spec (CommRingCat.of F))} (j : H ⟶ G)

/-- Rational points map onto the rational evaluation of the all-test image. -/
def rationalRangeMap :
    RationalGroupPoints F H →* rationalPoints F G (SubgroupFunctor.range j) where
  toFun x := ⟨H.affinePointsTarget j _ x, ⟨x, rfl⟩⟩
  map_one' := Subtype.ext (map_one (H.affinePointsTarget j _))
  map_mul' x y := Subtype.ext (map_mul (H.affinePointsTarget j _) x y)

/-- Adelic points map onto the actual adelic subgroup with its subspace topology. -/
def adelicRangeMap :
    AdelicGroupPoints F H →* adelicPoints F G (SubgroupFunctor.range j) where
  toFun x := ⟨H.affinePointsTarget j _ x, ⟨x, rfl⟩⟩
  map_one' := Subtype.ext (map_one (H.affinePointsTarget j _))
  map_mul' x y := Subtype.ext (map_mul (H.affinePointsTarget j _) x y)

theorem adelicRangeMap_surjective : Function.Surjective (adelicRangeMap F j) := by
  rintro ⟨x, y, hy⟩
  exact ⟨y, Subtype.ext hy⟩

theorem continuous_adelicRangeMap : Continuous (adelicRangeMap F j) :=
  (H.continuous_affinePointsTarget _ j).subtype_mk _

/-- Restriction to the range commutes with the actual principal maps. -/
theorem adelicRangeMap_rational (q : RationalGroupPoints F H) :
    adelicRangeMap F j (AdelicGroupPoints.rational F H q) =
      rational F G (SubgroupFunctor.range j) (rationalRangeMap F j q) := by
  apply Subtype.ext
  exact (congrArg (fun f : RationalGroupPoints F H →* AdelicGroupPoints F G => f q)
    (AdelicGroupPoints.rational_naturality F H j)).symm

/-- The represented source quotient maps to the actual subgroup-functor quotient. -/
def representedQuotientMap :
    AdelicGroupPoints.RationalQuotient F H →
      RationalQuotient F G (SubgroupFunctor.range j) :=
  Quotient.map' (adelicRangeMap F j) fun x y h => by
    apply QuotientGroup.rightRel_apply.mpr
    rcases QuotientGroup.rightRel_apply.mp h with ⟨q, hq⟩
    refine ⟨rationalRangeMap F j q, ?_⟩
    rw [← adelicRangeMap_rational, hq, map_mul, map_inv]

@[simp]
theorem representedQuotientMap_mk (x : AdelicGroupPoints F H) :
    representedQuotientMap F j (LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F H) x) =
      LeftCosetSpace.mk (rationalSubgroup F G (SubgroupFunctor.range j))
        (adelicRangeMap F j x) := rfl

theorem representedQuotientMap_surjective :
    Function.Surjective (representedQuotientMap F j) := by
  intro q
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective _ q
  obtain ⟨y, rfl⟩ := adelicRangeMap_surjective F j x
  exact ⟨LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F H) y, rfl⟩

theorem continuous_representedQuotientMap : Continuous (representedQuotientMap F j) := by
  apply (LeftCosetSpace.continuous_iff (AdelicGroupPoints.rationalSubgroup F H)).mpr
  exact (LeftCosetSpace.continuous_mk _).comp (continuous_adelicRangeMap F j)

/-- The quotient map preserves positive right translation. -/
theorem representedQuotientMap_rightTranslate (h : AdelicGroupPoints F H)
    (q : AdelicGroupPoints.RationalQuotient F H) :
    representedQuotientMap F j
      (LeftCosetSpace.rightTranslate (AdelicGroupPoints.rationalSubgroup F H) h q) =
        LeftCosetSpace.rightTranslate (rationalSubgroup F G (SubgroupFunctor.range j))
          (adelicRangeMap F j h) (representedQuotientMap F j q) := by
  induction q using Quotient.inductionOn with
  | _ x => exact congrArg (LeftCosetSpace.mk _) (map_mul (adelicRangeMap F j) x h)

/-- Compactness transfers along the continuous surjection, without an inverse map. -/
theorem compactSpace_rationalQuotient_range
    [CompactSpace (AdelicGroupPoints.RationalQuotient F H)] :
    CompactSpace (RationalQuotient F G (SubgroupFunctor.range j)) := by
  apply isCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr (representedQuotientMap_surjective F j)]
  exact isCompact_range (continuous_representedQuotientMap F j)

/-- The actual subgroup quotient of a represented smooth connected unipotent group
over a number field is compact. All splitness and affine-torsor inputs are public proofs. -/
theorem compactSpace_rationalQuotient_range_unipotent [IsAffine H.X.left]
    (hs : Smooth H.X.hom) (hc : ConnectedSpace H.X.left) (hu : IsUnipotent H) :
    CompactSpace (RationalQuotient F G (SubgroupFunctor.range j)) := by
  let : CompactSpace (AdelicGroupPoints.RationalQuotient F H) :=
    AdelicGroupPoints.compactSpace_rationalQuotient_of_hasCompactRationalCover
      (AdelicGroupPoints.exists_isCompact_rational_mul_mem_of_split
        perfectFieldUnipotentSplit splitUnipotentAffineTorsorStatement F H hs hc hu)
  exact compactSpace_rationalQuotient_range F j

end Langlands.Global.AdelicSubgroupPoints
