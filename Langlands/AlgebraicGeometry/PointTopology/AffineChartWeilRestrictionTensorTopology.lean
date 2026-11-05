import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionTensorBaseChange
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionLocalTopology
import Langlands.AlgebraicGeometry.PointTopology.SchemeBaseChangeTopologyProofs

/-! # The topology of actual tensor-base-change Weil comparisons -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

/-- The actual pullback-adjunction point equivalence as a homeomorphism for
independently defined scheme-point topologies over a local value ring. -/
def schemePointBaseChangeHomeomorph
    (A B S : Type u) [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra A S] [Algebra B S] [IsScalarTower A B S]
    [TopologicalSpace S] [IsTopologicalRing S] [IsLocalRing S] [IsOpenUnits S]
    (X : Over (Spec (CommRingCat.of A))) :
    letI : TopologicalSpace (RingPoint A X S) := schemePointTopology A X S
    letI : TopologicalSpace (RingPoint B (ringBaseChange A B X) S) :=
      schemePointTopology B (ringBaseChange A B X) S
    RingPoint A X S ≃ₜ RingPoint B (ringBaseChange A B X) S := by
  let : TopologicalSpace (RingPoint A X S) := schemePointTopology A X S
  let : TopologicalSpace (RingPoint B (ringBaseChange A B X) S) :=
    schemePointTopology B (ringBaseChange A B X) S
  exact IsHomeomorph.homeomorph (ringPointBaseChangeEquiv A B S X)
    (schemeBaseChangeTopology_proof A B S X)

@[simp]
theorem schemePointBaseChangeHomeomorph_apply
    (A B S : Type u) [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra A S] [Algebra B S] [IsScalarTower A B S]
    [TopologicalSpace S] [IsTopologicalRing S] [IsLocalRing S] [IsOpenUnits S]
    (X : Over (Spec (CommRingCat.of A))) (p : RingPoint A X S) :
    schemePointBaseChangeHomeomorph A B S X p = ringPointBaseChangeEquiv A B S X p := rfl

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Module.Finite A B] [Module.Projective A B]
variable (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance : LocallyOfFiniteType (ringBaseChange B (C ⊗[A] B) Y).hom :=
  inferInstanceAs
    (LocallyOfFiniteType (pullback.snd Y.hom (Spec.algebraMap B (C ⊗[A] B))))

variable [IsSeparated Y.hom]

local instance : IsSeparated (ringBaseChange B (C ⊗[A] B) Y).hom :=
  inferInstanceAs (IsSeparated (pullback.snd Y.hom (Spec.algebraMap B (C ⊗[A] B))))

variable [TopologicalSpace C] [IsTopologicalRing C] [IsLocalRing C] [IsOpenUnits C]

/-- On points over a local topological ring, actual tensor base change
preserves the independent topologies on the two Weil schemes.
The tensor algebra need not be local and needs no topology for this step. -/
def affineChartWeilRestrictionTensorPointHomeomorph
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    letI : TopologicalSpace (RingPoint A (affineChartWeilRestriction A B Y) C) :=
      schemePointTopology A (affineChartWeilRestriction A B Y) C
    letI : TopologicalSpace (RingPoint C
        (affineChartWeilRestriction C (C ⊗[A] B) (ringBaseChange B (C ⊗[A] B) Y)) C) :=
      schemePointTopology C
        (affineChartWeilRestriction C (C ⊗[A] B) (ringBaseChange B (C ⊗[A] B) Y)) C
    RingPoint A (affineChartWeilRestriction A B Y) C ≃ₜ
      RingPoint C
        (affineChartWeilRestriction C (C ⊗[A] B) (ringBaseChange B (C ⊗[A] B) Y)) C := by
  let : TopologicalSpace (RingPoint A (affineChartWeilRestriction A B Y) C) :=
    schemePointTopology A (affineChartWeilRestriction A B Y) C
  let : TopologicalSpace (RingPoint C
      (ringBaseChange A C (affineChartWeilRestriction A B Y)) C) :=
    schemePointTopology C (ringBaseChange A C (affineChartWeilRestriction A B Y)) C
  let : TopologicalSpace (RingPoint C
      (affineChartWeilRestriction C (C ⊗[A] B) (ringBaseChange B (C ⊗[A] B) Y)) C) :=
    schemePointTopology C
      (affineChartWeilRestriction C (C ⊗[A] B) (ringBaseChange B (C ⊗[A] B) Y)) C
  exact (schemePointBaseChangeHomeomorph A C C (affineChartWeilRestriction A B Y)).trans
    (schemePointIsoHomeomorph C C (affineChartWeilRestrictionTensorBaseChangeIso A B C Y hY))

/-- The point homeomorphism is actual base change of a point followed by
the canonical tensor-base-change scheme isomorphism. -/
@[simp]
theorem affineChartWeilRestrictionTensorPointHomeomorph_apply
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (p : RingPoint A (affineChartWeilRestriction A B Y) C) :
    affineChartWeilRestrictionTensorPointHomeomorph A B C Y hY p =
      ringPointBaseChangeEquiv A C C (affineChartWeilRestriction A B Y) p ≫
        (affineChartWeilRestrictionTensorBaseChangeIso A B C Y hY).hom := rfl

/-- Under the second Weil scheme's actual counit, the topological
comparison has exactly the previously constructed canonical tensor map. -/
@[simp]
theorem affineChartWeilRestrictionTensorPointHomeomorph_comparison
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (p : RingPoint A (affineChartWeilRestriction A B Y) C) :
    affineChartWeilRestrictionComparison C (C ⊗[A] B)
        (ringBaseChange B (C ⊗[A] B) Y) (ringTest C C)
        (affineChartWeilRestrictionTensorPointHomeomorph A B C Y hY p) =
      affineChartWeilRestrictionTensorBaseChangeComparison A B C Y (ringTest C C)
        (ringPointBaseChangeEquiv A C C (affineChartWeilRestriction A B Y) p) := by
  rw [affineChartWeilRestrictionTensorPointHomeomorph_apply]
  exact affineChartWeilRestrictionTensorBaseChangeIso_comparison A B C Y hY _ _

omit [IsSeparated Y.hom] in
/-- An actual relative projective immersion supplies the geometry for
the tensor-base-change homeomorphism over any local topological value ring. -/
def projectiveImmersionWeilRestrictionTensorPointHomeomorph
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom) :
    letI : TopologicalSpace (RingPoint A (affineChartWeilRestriction A B Y) C) :=
      schemePointTopology A (affineChartWeilRestriction A B Y) C
    letI : TopologicalSpace (RingPoint C
        (affineChartWeilRestriction C (C ⊗[A] B) (ringBaseChange B (C ⊗[A] B) Y)) C) :=
      schemePointTopology C
        (affineChartWeilRestriction C (C ⊗[A] B) (ringBaseChange B (C ⊗[A] B) Y)) C
    RingPoint A (affineChartWeilRestriction A B Y) C ≃ₜ
      RingPoint C
        (affineChartWeilRestriction C (C ⊗[A] B) (ringBaseChange B (C ⊗[A] B) Y)) C := by
  letI := isSeparated_of_projectiveImmersion B Y n i hi
  exact affineChartWeilRestrictionTensorPointHomeomorph A B C Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B n i)

omit [IsSeparated Y.hom] in
/-- The specialized homeomorphism retains the actual canonical scheme map. -/
@[simp]
theorem projectiveImmersionWeilRestrictionTensorPointHomeomorph_apply
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom)
    (p : RingPoint A (affineChartWeilRestriction A B Y) C) :
    projectiveImmersionWeilRestrictionTensorPointHomeomorph A B C Y n i hi p =
      ringPointBaseChangeEquiv A C C (affineChartWeilRestriction A B Y) p ≫
        (projectiveImmersionWeilRestrictionTensorBaseChangeIso A B C Y n i hi).hom := rfl

omit [IsSeparated Y.hom] in
/-- The projective-immersion specialization retains the exact counit formula. -/
@[simp]
theorem projectiveImmersionWeilRestrictionTensorPointHomeomorph_comparison
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom)
    (p : RingPoint A (affineChartWeilRestriction A B Y) C) :
    affineChartWeilRestrictionComparison C (C ⊗[A] B)
        (ringBaseChange B (C ⊗[A] B) Y) (ringTest C C)
        (projectiveImmersionWeilRestrictionTensorPointHomeomorph A B C Y n i hi p) =
      affineChartWeilRestrictionTensorBaseChangeComparison A B C Y (ringTest C C)
        (ringPointBaseChangeEquiv A C C (affineChartWeilRestriction A B Y) p) := by
  let := isSeparated_of_projectiveImmersion B Y n i hi
  exact affineChartWeilRestrictionTensorPointHomeomorph_comparison A B C Y _ p

end Langlands.AlgebraicGeometry.PointTopology
