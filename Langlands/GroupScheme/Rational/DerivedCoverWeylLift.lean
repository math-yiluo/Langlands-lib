import Langlands.GroupScheme.Rational.DerivedCoverReflectionLift
import Langlands.GroupScheme.Rational.RootGeneratedWeylRepresentatives
import Langlands.GroupScheme.Rational.RootSubgroupPositive
import Langlands.GroupScheme.Rational.WeightVectorUniqueness

/-! # Actual simply connected cover points representing relative Weyl classes -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G D C : GroupScheme (Spec (CommRingCat.of k))}
  {d : D ⟶ G} {π : C ⟶ D}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

namespace RelativeRoot

/-- Every actual relative-root rational subgroup lies in the actual simply
connected image, using integral reflection data and a positive cocharacter. -/
theorem subgroupPoints_le_derivedCoverImage_of_reflectionData
    (hcover : IsSimplyConnectedDerivedCover d π) (hi : IsMaximalSplitTorus i)
    (R : RelativeRootReflectionData i) {a : characterLattice T}
    (ha : a ∈ relativeRoots i) :
    (subgroup i a).carrier (Over.mk (𝟙 _)) ≤
      (rationalPoints.map (π ≫ d)).range := by
  obtain ⟨m, hm, ν, hν⟩ := hi.isSplitSubtorus.1.exists_pairing_eq_pos ha.1
  have hpos : 0 < latticePairing T a ν := by
    rw [hν]
    exact_mod_cast hm
  exact (subgroup_le_dynamicUnipotent i ν hpos (Over.mk (𝟙 _))).trans
    (Dynamic.unipotentPoints_le_derivedCoverImage_of_reflectionData i hcover hi R ν)

end RelativeRoot

/-- Opposite-root factor pairs and an actual-root-system realization make the
actual simply connected image supply every rational relative-Weyl class. -/
theorem subgroupRelativeWeylMap_derivedCover_surjective
    (hcover : IsSimplyConnectedDerivedCover d π) (hi : IsMaximalSplitTorus i)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hroot : HasRelativeRootSystem i) :
    Function.Surjective
      (subgroupRelativeWeylMap i (rationalPoints.map (π ≫ d)).range) := by
  let : Smooth G.X.hom := hcover.isConnectedReductive.smooth
  let R := RelativeRootReflectionData.ofOppositeFactorPairs i hi.isSplitSubtorus.1 hE
  exact RelativeRoot.subgroupRelativeWeylMap_surjective_of_oppositeFactorPairs
    i hi.isSplitSubtorus.1 hE hroot _
    (fun _ ha => RelativeRoot.subgroupPoints_le_derivedCoverImage_of_reflectionData
      i hcover hi R ha)

/-- A trivial positive-root stabilizer can replace the root-system realization
when proving that the actual simply connected image supplies every Weyl class. -/
theorem subgroupRelativeWeylMap_derivedCover_surjective_of_positive_stabilizer
    (hcover : IsSimplyConnectedDerivedCover d π) (hi : IsMaximalSplitTorus i)
    (hE : RelativeRoot.HasOppositeFactorPairs i) {ν : cocharacterLattice T}
    (hν : IsGenericCocharacter i ν) (hstab : HasTrivialPositiveRootStabilizer i ν) :
    Function.Surjective
      (subgroupRelativeWeylMap i (rationalPoints.map (π ≫ d)).range) := by
  let : Smooth G.X.hom := hcover.isConnectedReductive.smooth
  let R := RelativeRootReflectionData.ofOppositeFactorPairs i hi.isSplitSubtorus.1 hE
  exact RelativeRoot.subgroupRelativeWeylMap_surjective_of_positive_stabilizer
    i hi.isSplitSubtorus.1 hE (hi.isSplitSubtorus.1.finite_relativeRoots i) hν hstab _
    (fun _ ha => RelativeRoot.subgroupPoints_le_derivedCoverImage_of_reflectionData
      i hcover hi R ha)

/-- Each relative-Weyl class has a representative which is the actual image of
a point of the supplied simply connected cover. -/
theorem exists_derivedCoverWeylRepresentative
    (hcover : IsSimplyConnectedDerivedCover d π) (hi : IsMaximalSplitTorus i)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hroot : HasRelativeRootSystem i)
    (w : relativeWeylGroup i) :
    ∃ c : (normalizerPoints i).comap (rationalPoints.map (π ≫ d)),
      (QuotientGroup.mk
        (⟨rationalPoints.map (π ≫ d) c.val, c.property⟩ : normalizerPoints i) :
        relativeWeylGroup i) = w := by
  obtain ⟨n, hn⟩ := subgroupRelativeWeylMap_derivedCover_surjective i hcover hi hE hroot w
  obtain ⟨c, hc⟩ := n.property
  have hcn : rationalPoints.map (π ≫ d) c ∈ normalizerPoints i := by
    rw [hc]
    exact n.val.property
  refine ⟨⟨c, hcn⟩, ?_⟩
  change (QuotientGroup.mk n.val : relativeWeylGroup i) = w at hn
  have hn' : (⟨rationalPoints.map (π ≫ d) c, hcn⟩ : normalizerPoints i) = n.val :=
    Subtype.ext hc
  simpa only [hn'] using hn

/-- Choose an actual cover point over every relative-Weyl class, retaining
normalizer membership of its image. This choice need not be multiplicative. -/
def derivedCoverWeylRepresentative
    (hcover : IsSimplyConnectedDerivedCover d π) (hi : IsMaximalSplitTorus i)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hroot : HasRelativeRootSystem i)
    (w : relativeWeylGroup i) :
    (normalizerPoints i).comap (rationalPoints.map (π ≫ d)) :=
  (exists_derivedCoverWeylRepresentative i hcover hi hE hroot w).choose

/-- The image of the selected cover point normalizes the original split torus. -/
theorem derivedCoverWeylRepresentative_mem_normalizer
    (hcover : IsSimplyConnectedDerivedCover d π) (hi : IsMaximalSplitTorus i)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hroot : HasRelativeRootSystem i)
    (w : relativeWeylGroup i) :
    rationalPoints.map (π ≫ d)
      (derivedCoverWeylRepresentative i hcover hi hE hroot w).val ∈ normalizerPoints i :=
  (derivedCoverWeylRepresentative i hcover hi hE hroot w).property

/-- The image of the selected actual cover point has exactly the requested
class in the actual normalizer quotient. -/
theorem derivedCoverWeylRepresentative_class
    (hcover : IsSimplyConnectedDerivedCover d π) (hi : IsMaximalSplitTorus i)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hroot : HasRelativeRootSystem i)
    (w : relativeWeylGroup i) :
    (QuotientGroup.mk
      (⟨rationalPoints.map (π ≫ d)
          (derivedCoverWeylRepresentative i hcover hi hE hroot w).val,
        derivedCoverWeylRepresentative_mem_normalizer i hcover hi hE hroot w⟩ :
        normalizerPoints i) : relativeWeylGroup i) = w :=
  (exists_derivedCoverWeylRepresentative i hcover hi hE hroot w).choose_spec

/-- Every normalizer point is the image of the selected cover representative
of its own Weyl class times an actual whole-torus-centralizer point. -/
theorem derivedCoverWeylRepresentative_normalizer_factorization
    (hcover : IsSimplyConnectedDerivedCover d π) (hi : IsMaximalSplitTorus i)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hroot : HasRelativeRootSystem i)
    (n : normalizerPoints i) :
    ∃ z ∈ centralizerPoints i,
      n.val = rationalPoints.map (π ≫ d)
        (derivedCoverWeylRepresentative i hcover hi hE hroot (QuotientGroup.mk n)).val * z := by
  let c := derivedCoverWeylRepresentative i hcover hi hE hroot (QuotientGroup.mk n)
  let m : normalizerPoints i := ⟨rationalPoints.map (π ≫ d) c.val, c.property⟩
  have hm : (QuotientGroup.mk m : relativeWeylGroup i) = QuotientGroup.mk n :=
    derivedCoverWeylRepresentative_class i hcover hi hE hroot (QuotientGroup.mk n)
  have hz : (m⁻¹ * n : normalizerPoints i) ∈
      (centralizerPoints i).subgroupOf (normalizerPoints i) := QuotientGroup.eq.mp hm
  exact ⟨m.val⁻¹ * n.val, hz, by simp [m, c]⟩

/-- Conditional product assembly with no separate unipotent-containment,
Weyl-surjectivity or generic-centralizer premise. Opposite-pair existence,
the actual-root-system realization and rational Bruhat covering remain explicit. -/
theorem exists_derivedCover_mul_centralizer_of_oppositeFactorPairs
    {Z : GroupScheme (Spec (CommRingCat.of k))} (j : Z ⟶ G)
    (hcover : IsSimplyConnectedDerivedCover d π) (hi : IsMaximalSplitTorus i)
    (hj : (torusCentralizer i).IsRepresentedBy j)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hroot : HasRelativeRootSystem i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (hBr : HasRationalBruhatDecomposition i ν) (g : rationalPoints G) :
    ∃ c : rationalPoints C, ∃ z : rationalPoints Z,
      g = rationalPoints.map (π ≫ d) c * rationalPoints.map j z := by
  let : Smooth G.X.hom := hcover.isConnectedReductive.smooth
  let R := RelativeRootReflectionData.ofOppositeFactorPairs i hi.isSplitSubtorus.1 hE
  exact exists_cover_mul_centralizer_of_bruhat i ν j d π hj
    (genericCentralizer k G hcover.isConnectedReductive T i hi ν hν) hBr
    (Dynamic.unipotentPoints_le_derivedCoverImage_of_reflectionData i hcover hi R ν)
    (subgroupRelativeWeylMap_derivedCover_surjective i hcover hi hE hroot) g

/-- The same product follows using a trivial positive-root stabilizer in place
of the actual-root-system realization. -/
theorem exists_derivedCover_mul_centralizer_of_positive_stabilizer
    {Z : GroupScheme (Spec (CommRingCat.of k))} (j : Z ⟶ G)
    (hcover : IsSimplyConnectedDerivedCover d π) (hi : IsMaximalSplitTorus i)
    (hj : (torusCentralizer i).IsRepresentedBy j)
    (hE : RelativeRoot.HasOppositeFactorPairs i)
    (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (hstab : HasTrivialPositiveRootStabilizer i ν)
    (hBr : HasRationalBruhatDecomposition i ν) (g : rationalPoints G) :
    ∃ c : rationalPoints C, ∃ z : rationalPoints Z,
      g = rationalPoints.map (π ≫ d) c * rationalPoints.map j z := by
  let : Smooth G.X.hom := hcover.isConnectedReductive.smooth
  let R := RelativeRootReflectionData.ofOppositeFactorPairs i hi.isSplitSubtorus.1 hE
  exact exists_cover_mul_centralizer_of_bruhat i ν j d π hj
    (genericCentralizer k G hcover.isConnectedReductive T i hi ν hν) hBr
    (Dynamic.unipotentPoints_le_derivedCoverImage_of_reflectionData i hcover hi R ν)
    (subgroupRelativeWeylMap_derivedCover_surjective_of_positive_stabilizer
      i hcover hi hE hν hstab) g

end Langlands.GroupScheme
