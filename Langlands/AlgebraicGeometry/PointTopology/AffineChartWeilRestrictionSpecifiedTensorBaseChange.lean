import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionTensorBaseChange
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionCoefficientIso
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionTargetIso

/-! # Actual Weil base change along a specified original tensor coefficient equivalence -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (A B C D : Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra C D] [Algebra B D]
  (e : C ⊗[A] B ≃ₐ[C] D)
  (he : ∀ b : B, e (1 ⊗ₜ[A] b) = algebraMap B D b)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

include he in
/-- The coefficient spectrum map retains the original upper base map. -/
@[reassoc (attr := simp)]
theorem specifiedTensorCoefficientSpec_comp :
    (weilCoefficientSpecIso C (C ⊗[A] B) D e).hom ≫
      Spec.algebraMap B (C ⊗[A] B) = Spec.algebraMap B D := by
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap B (C ⊗[A] B))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext he

/-- Coefficient transport of the tensor-base-changed target is its ordinary original-base pullback. -/
def specifiedTensorCoefficientTargetIso (Y : Over (Spec (CommRingCat.of B))) :
    weilCoefficientTarget C (C ⊗[A] B) D e (ringBaseChange B (C ⊗[A] B) Y) ≅
      ringBaseChange B D Y :=
  Over.isoMk
    ((pullbackLeftPullbackSndIso Y.hom (Spec.algebraMap B (C ⊗[A] B))
      (weilCoefficientSpecIso C (C ⊗[A] B) D e).hom).trans
        (pullback.congrHom rfl (specifiedTensorCoefficientSpec_comp A B C D e he)))
    (by simp [weilCoefficientTarget, ringBaseChange, pullback.congrHom])

/-- The target isomorphism has precisely the original projection back to the model. -/
@[reassoc (attr := simp)]
theorem specifiedTensorCoefficientTargetIso_hom_fst
    (Y : Over (Spec (CommRingCat.of B))) :
    (specifiedTensorCoefficientTargetIso A B C D e he Y).hom.left ≫
      pullback.fst Y.hom (Spec.algebraMap B D) =
    pullback.fst (ringBaseChange B (C ⊗[A] B) Y).hom
        (weilCoefficientSpecIso C (C ⊗[A] B) D e).hom ≫
      pullback.fst Y.hom (Spec.algebraMap B (C ⊗[A] B)) := by
  simp [specifiedTensorCoefficientTargetIso, ringBaseChange, pullback.congrHom,
    Category.assoc]

variable [Module.Finite A B] [Module.Projective A B]
  (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

local instance tensorTargetLocallyOfFiniteType :
    LocallyOfFiniteType (ringBaseChange B (C ⊗[A] B) Y).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd Y.hom (Spec.algebraMap B (C ⊗[A] B))))

local instance transportedTargetLocallyOfFiniteType :
    LocallyOfFiniteType
      (weilCoefficientTarget C (C ⊗[A] B) D e (ringBaseChange B (C ⊗[A] B) Y)).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd
    (ringBaseChange B (C ⊗[A] B) Y).hom (weilCoefficientSpecIso C (C ⊗[A] B) D e).hom))

local instance originalTargetLocallyOfFiniteType : LocallyOfFiniteType (ringBaseChange B D Y).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd Y.hom (Spec.algebraMap B D)))

/-- The independently constructed Weil scheme over the specified coefficient algebra. -/
abbrev affineChartWeilRestrictionSpecifiedTensorBaseChange :
    Over (Spec (CommRingCat.of C)) := by
  letI := weilCoefficientFinite C (C ⊗[A] B) D e
  letI := weilCoefficientProjective C (C ⊗[A] B) D e
  exact affineChartWeilRestriction C D (ringBaseChange B D Y)

/-- The canonical original-counit comparison after tensor and coefficient base change. -/
def affineChartWeilRestrictionSpecifiedTensorComparison
    (T : Over (Spec (CommRingCat.of C)))
    (p : T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    ringBaseChange C D T ⟶ ringBaseChange B D Y :=
  (Over.mapPullbackAdj (weilCoefficientSpecIso C (C ⊗[A] B) D e).hom).homEquiv
      _ (ringBaseChange B (C ⊗[A] B) Y)
      ((weilCoefficientTestIso C (C ⊗[A] B) D e T).hom ≫
        affineChartWeilRestrictionTensorBaseChangeComparison A B C Y T p) ≫
    (specifiedTensorCoefficientTargetIso A B C D e he Y).hom

variable [IsSeparated Y.hom]

local instance tensorTargetIsSeparated : IsSeparated (ringBaseChange B (C ⊗[A] B) Y).hom :=
  inferInstanceAs (IsSeparated (pullback.snd Y.hom (Spec.algebraMap B (C ⊗[A] B))))

local instance transportedTargetIsSeparated :
    IsSeparated
      (weilCoefficientTarget C (C ⊗[A] B) D e (ringBaseChange B (C ⊗[A] B) Y)).hom :=
  inferInstanceAs (IsSeparated (pullback.snd
    (ringBaseChange B (C ⊗[A] B) Y).hom (weilCoefficientSpecIso C (C ⊗[A] B) D e).hom))

local instance originalTargetIsSeparated : IsSeparated (ringBaseChange B D Y).hom :=
  inferInstanceAs (IsSeparated (pullback.snd Y.hom (Spec.algebraMap B D)))

/-- The actual scalar base change of the Weil model is the independently glued Weil scheme
for the original target pullback and specified coefficient extension. -/
def affineChartWeilRestrictionSpecifiedTensorBaseChangeIso
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    ringBaseChange A C (affineChartWeilRestriction A B Y) ≅
      affineChartWeilRestrictionSpecifiedTensorBaseChange A B C D e Y := by
  letI := weilCoefficientFinite C (C ⊗[A] B) D e
  letI := weilCoefficientProjective C (C ⊗[A] B) D e
  let Z := ringBaseChange B (C ⊗[A] B) Y
  have hZ := hasFiniteAffineNeighborhoods_ringBaseChange B (C ⊗[A] B) Y hY
  have hW := hasFiniteAffineNeighborhoods_weilCoefficientTarget C (C ⊗[A] B) D e Z hZ
  have hV := hasFiniteAffineNeighborhoods_ringBaseChange B D Y hY
  exact (affineChartWeilRestrictionTensorBaseChangeIso A B C Y hY).trans
    ((affineChartWeilRestrictionCoefficientIso C (C ⊗[A] B) D e Z hZ).trans
      (affineChartWeilRestrictionTargetIso C D hW hV
        (specifiedTensorCoefficientTargetIso A B C D e he Y)))

/-- On every original test, the actual scheme isomorphism induces the specified original-counit map. -/
theorem affineChartWeilRestrictionSpecifiedTensorBaseChangeIso_comparison
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of C)))
    (p : T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    letI := weilCoefficientFinite C (C ⊗[A] B) D e
    letI := weilCoefficientProjective C (C ⊗[A] B) D e
    affineChartWeilRestrictionComparison C D (ringBaseChange B D Y) T
        (p ≫ (affineChartWeilRestrictionSpecifiedTensorBaseChangeIso A B C D e he Y hY).hom) =
      affineChartWeilRestrictionSpecifiedTensorComparison A B C D e he Y T p := by
  let := weilCoefficientFinite C (C ⊗[A] B) D e
  let := weilCoefficientProjective C (C ⊗[A] B) D e
  dsimp only [affineChartWeilRestrictionSpecifiedTensorBaseChangeIso, Iso.trans_hom]
  rw [← Category.assoc, ← Category.assoc,
    affineChartWeilRestrictionTargetIso_comparison,
    affineChartWeilRestrictionCoefficientIso_comparison]
  simp only [affineChartWeilRestrictionCoefficientComparison,
    affineChartWeilRestrictionTensorBaseChangeIso_comparison]
  rfl

omit [IsSeparated Y.hom] in
/-- A specified relative projective immersion derives all geometry for the original tensor-base-change iso. -/
def projectiveImmersionWeilRestrictionSpecifiedTensorBaseChangeIso
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace B n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec B n = Y.hom) :
    ringBaseChange A C (affineChartWeilRestriction A B Y) ≅
      affineChartWeilRestrictionSpecifiedTensorBaseChange A B C D e Y := by
  let := isSeparated_of_projectiveImmersion B Y n j hj
  exact affineChartWeilRestrictionSpecifiedTensorBaseChangeIso A B C D e he Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B n j)

omit [IsSeparated Y.hom] in
/-- The projective-immersion iso retains the original comparison on every actual test. -/
theorem projectiveImmersionWeilRestrictionSpecifiedTensorBaseChangeIso_comparison
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace B n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec B n = Y.hom)
    (T : Over (Spec (CommRingCat.of C)))
    (p : T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    letI := weilCoefficientFinite C (C ⊗[A] B) D e
    letI := weilCoefficientProjective C (C ⊗[A] B) D e
    affineChartWeilRestrictionComparison C D (ringBaseChange B D Y) T
        (p ≫ (projectiveImmersionWeilRestrictionSpecifiedTensorBaseChangeIso
          A B C D e he Y n j hj).hom) =
      affineChartWeilRestrictionSpecifiedTensorComparison A B C D e he Y T p := by
  let := isSeparated_of_projectiveImmersion B Y n j hj
  exact affineChartWeilRestrictionSpecifiedTensorBaseChangeIso_comparison A B C D e he Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B n j) T p

end Langlands.AlgebraicGeometry.PointTopology
