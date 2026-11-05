import Langlands.AlgebraicGeometry.PointTopology.QuasiProjectiveWeilRestriction

/-! # Scalar base change of the actual affine-chart Weil restriction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]

/-- The actual base-changed extension is the spectrum of the actual
tensor-product algebra, with its original new-base structure map. -/
def weilRestrictionScalarBaseChangeExtensionIso :
    Over.mk (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B)) ≅
      ringTest C (C ⊗[A] B) :=
  Over.isoMk (pullbackSpecIso A C B) (pullbackSpecIso_hom_fst' A C B)

/-- Pasting the actual extension pullback with a test-scheme pullback,
as an isomorphism over the original extension spectrum. -/
def weilRestrictionScalarBaseChangeTestIso
    (T : Over (Spec (CommRingCat.of C))) :
    (Over.map (pullback.snd (Spec.algebraMap A C) (Spec.algebraMap A B))).obj
        ((Over.pullback
          (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B))).obj T) ≅
      ringBaseChange A B ((Over.map (Spec.algebraMap A C)).obj T) :=
  Over.isoMk
    (pullbackRightPullbackFstIso (Spec.algebraMap A C) (Spec.algebraMap A B) T.hom)
    (pullbackRightPullbackFstIso_hom_snd _ _ _)

/-- The test-pasting isomorphism is natural in every actual test scheme. -/
theorem weilRestrictionScalarBaseChangeTestIso_natural
    {T S : Over (Spec (CommRingCat.of C))} (f : T ⟶ S) :
    (Over.map (pullback.snd (Spec.algebraMap A C) (Spec.algebraMap A B))).map
        ((Over.pullback
          (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B))).map f) ≫
        (weilRestrictionScalarBaseChangeTestIso A B C S).hom =
      (weilRestrictionScalarBaseChangeTestIso A B C T).hom ≫
        (Over.pullback (Spec.algebraMap A B)).map
          ((Over.map (Spec.algebraMap A C)).map f) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp [weilRestrictionScalarBaseChangeTestIso, Over.pullback_map_left,
      Category.assoc]
  · simp [weilRestrictionScalarBaseChangeTestIso, Over.pullback_map_left,
      Category.assoc]

variable [Module.Finite A B] [Module.Projective A B]
variable (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

/-- The canonical base-changed comparison: forget the new base on the
input, apply the original counit comparison, paste the actual source
pullbacks, then lift to the actual base-changed target. -/
def affineChartWeilRestrictionScalarBaseChangeComparison
    (T : Over (Spec (CommRingCat.of C)))
    (p : T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    (Over.pullback
      (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B))).obj T ⟶
      (Over.pullback
        (pullback.snd (Spec.algebraMap A C) (Spec.algebraMap A B))).obj Y :=
  (Over.mapPullbackAdj
    (pullback.snd (Spec.algebraMap A C) (Spec.algebraMap A B))).homEquiv _ Y
      ((weilRestrictionScalarBaseChangeTestIso A B C T).hom ≫
        affineChartWeilRestrictionComparison A B Y _
          (((Over.mapPullbackAdj (Spec.algebraMap A C)).homEquiv T _).symm p))

/-- The original target projection of the comparison is the original
counit comparison after the canonical source-pasting isomorphism. -/
@[simp]
theorem affineChartWeilRestrictionScalarBaseChangeComparison_fst
    (T : Over (Spec (CommRingCat.of C)))
    (p : T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    (affineChartWeilRestrictionScalarBaseChangeComparison A B C Y T p).left ≫
        pullback.fst Y.hom
          (pullback.snd (Spec.algebraMap A C) (Spec.algebraMap A B)) =
      (weilRestrictionScalarBaseChangeTestIso A B C T).hom.left ≫
        (affineChartWeilRestrictionComparison A B Y _
          (((Over.mapPullbackAdj (Spec.algebraMap A C)).homEquiv T _).symm p)).left := by
  simp [affineChartWeilRestrictionScalarBaseChangeComparison, Over.mapPullbackAdj]

/-- The canonical base-changed comparison is natural on all test schemes. -/
theorem affineChartWeilRestrictionScalarBaseChangeComparison_natural
    {T S : Over (Spec (CommRingCat.of C))} (f : T ⟶ S)
    (p : S ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    affineChartWeilRestrictionScalarBaseChangeComparison A B C Y T (f ≫ p) =
      (Over.pullback
        (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B))).map f ≫
        affineChartWeilRestrictionScalarBaseChangeComparison A B C Y S p := by
  unfold affineChartWeilRestrictionScalarBaseChangeComparison
  rw [(Over.mapPullbackAdj (Spec.algebraMap A C)).homEquiv_naturality_left_symm,
    affineChartWeilRestrictionComparison_natural, ← Category.assoc,
    ← weilRestrictionScalarBaseChangeTestIso_natural A B C f,
    Category.assoc]
  exact (Over.mapPullbackAdj
    (pullback.snd (Spec.algebraMap A C) (Spec.algebraMap A B))).homEquiv_naturality_left
      _ _

variable [IsSeparated Y.hom]

/-- Base change of the original representing scheme represents the actual
base-changed Weil functor, on every test scheme over the new base.
No geometric premise on the pulled-back target is needed. -/
def affineChartWeilRestrictionScalarBaseChangeTestEquiv
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of C))) :
    (T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) ≃
      ((Over.pullback
        (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B))).obj T ⟶
        (Over.pullback
          (pullback.snd (Spec.algebraMap A C) (Spec.algebraMap A B))).obj Y) :=
  (((Over.mapPullbackAdj (Spec.algebraMap A C)).homEquiv T _).symm.trans
    (affineChartWeilRestrictionTestEquiv A B Y hY
      ((Over.map (Spec.algebraMap A C)).obj T))).trans
    ((Iso.homCongr (weilRestrictionScalarBaseChangeTestIso A B C T).symm
      (Iso.refl Y)).trans
      ((Over.mapPullbackAdj
        (pullback.snd (Spec.algebraMap A C) (Spec.algebraMap A B))).homEquiv _ Y))

/-- The equivalence uses exactly the canonical base-changed counit map. -/
@[simp]
theorem affineChartWeilRestrictionScalarBaseChangeTestEquiv_apply
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of C)))
    (p : T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    affineChartWeilRestrictionScalarBaseChangeTestEquiv A B C Y hY T p =
      affineChartWeilRestrictionScalarBaseChangeComparison A B C Y T p := by
  change (Over.mapPullbackAdj _).homEquiv _ Y (_ ≫ _ ≫ 𝟙 Y) = _
  rw [Category.comp_id]
  rfl

/-- Naturality of the representing equivalence, with actual pullback maps. -/
theorem affineChartWeilRestrictionScalarBaseChangeTestEquiv_natural
    (hY : HasFiniteAffineNeighborhoods Y.left)
    {T S : Over (Spec (CommRingCat.of C))} (f : T ⟶ S)
    (p : S ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    affineChartWeilRestrictionScalarBaseChangeTestEquiv A B C Y hY T (f ≫ p) =
      (Over.pullback
        (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B))).map f ≫
        affineChartWeilRestrictionScalarBaseChangeTestEquiv A B C Y hY S p := by
  simp only [affineChartWeilRestrictionScalarBaseChangeTestEquiv_apply]
  exact affineChartWeilRestrictionScalarBaseChangeComparison_natural A B C Y f p

/-- Naturality of the inverse of the actual base-changed equivalence. -/
theorem affineChartWeilRestrictionScalarBaseChangeTestEquiv_symm_natural
    (hY : HasFiniteAffineNeighborhoods Y.left)
    {T S : Over (Spec (CommRingCat.of C))} (f : T ⟶ S)
    (q : (Over.pullback
        (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B))).obj S ⟶
        (Over.pullback
          (pullback.snd (Spec.algebraMap A C) (Spec.algebraMap A B))).obj Y) :
    (affineChartWeilRestrictionScalarBaseChangeTestEquiv A B C Y hY T).symm
        ((Over.pullback
          (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B))).map f ≫ q) =
      f ≫ (affineChartWeilRestrictionScalarBaseChangeTestEquiv A B C Y hY S).symm q := by
  apply (affineChartWeilRestrictionScalarBaseChangeTestEquiv A B C Y hY T).injective
  rw [Equiv.apply_symm_apply,
    affineChartWeilRestrictionScalarBaseChangeTestEquiv_natural,
    Equiv.apply_symm_apply]

omit [IsSeparated Y.hom] in
/-- The actual relative projective immersion discharges the original
target's separation and finite-affine-neighborhood premises. -/
def projectiveImmersionWeilRestrictionScalarBaseChangeTestEquiv
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom)
    (T : Over (Spec (CommRingCat.of C))) :
    (T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) ≃
      ((Over.pullback
        (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B))).obj T ⟶
        (Over.pullback
          (pullback.snd (Spec.algebraMap A C) (Spec.algebraMap A B))).obj Y) := by
  letI := isSeparated_of_projectiveImmersion B Y n i hi
  exact affineChartWeilRestrictionScalarBaseChangeTestEquiv A B C Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B n i) T

omit [IsSeparated Y.hom] in
/-- The projective-immersion specialization retains the canonical map. -/
@[simp]
theorem projectiveImmersionWeilRestrictionScalarBaseChangeTestEquiv_apply
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom)
    (T : Over (Spec (CommRingCat.of C)))
    (p : T ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    projectiveImmersionWeilRestrictionScalarBaseChangeTestEquiv A B C Y n i hi T p =
      affineChartWeilRestrictionScalarBaseChangeComparison A B C Y T p := by
  let := isSeparated_of_projectiveImmersion B Y n i hi
  exact affineChartWeilRestrictionScalarBaseChangeTestEquiv_apply A B C Y _ T p

omit [IsSeparated Y.hom] in
/-- Naturality for actual projective-immersion inputs. -/
theorem projectiveImmersionWeilRestrictionScalarBaseChangeTestEquiv_natural
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom)
    {T S : Over (Spec (CommRingCat.of C))} (f : T ⟶ S)
    (p : S ⟶ ringBaseChange A C (affineChartWeilRestriction A B Y)) :
    projectiveImmersionWeilRestrictionScalarBaseChangeTestEquiv A B C Y n i hi T
        (f ≫ p) =
      (Over.pullback
        (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B))).map f ≫
        projectiveImmersionWeilRestrictionScalarBaseChangeTestEquiv A B C Y n i hi S p := by
  simp only [projectiveImmersionWeilRestrictionScalarBaseChangeTestEquiv_apply]
  exact affineChartWeilRestrictionScalarBaseChangeComparison_natural A B C Y f p

omit [IsSeparated Y.hom] in
/-- Inverse naturality for actual projective-immersion inputs. -/
theorem projectiveImmersionWeilRestrictionScalarBaseChangeTestEquiv_symm_natural
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom)
    {T S : Over (Spec (CommRingCat.of C))} (f : T ⟶ S)
    (q : (Over.pullback
        (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B))).obj S ⟶
        (Over.pullback
          (pullback.snd (Spec.algebraMap A C) (Spec.algebraMap A B))).obj Y) :
    (projectiveImmersionWeilRestrictionScalarBaseChangeTestEquiv A B C Y n i hi T).symm
        ((Over.pullback
          (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B))).map f ≫ q) =
      f ≫
        (projectiveImmersionWeilRestrictionScalarBaseChangeTestEquiv A B C Y n i hi S).symm
          q := by
  let := isSeparated_of_projectiveImmersion B Y n i hi
  exact affineChartWeilRestrictionScalarBaseChangeTestEquiv_symm_natural
    A B C Y _ f q

end Langlands.AlgebraicGeometry.PointTopology
