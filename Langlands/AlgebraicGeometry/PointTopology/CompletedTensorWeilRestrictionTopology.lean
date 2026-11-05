import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionTargets
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionTensorTopology
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionProductTopology

/-! # Completed-tensor decomposition of actual Weil point topologies -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

section FactorTest

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
variable {ι : Type u} (D : ι → Type u) [∀ i, CommRing (D i)]
  [∀ i, Algebra C (D i)] [∀ i, Algebra B (D i)]
  (e : C ⊗[A] B ≃ₐ[C] (∀ i, D i))
  (he : ∀ (b : B) (i : ι), e (1 ⊗ₜ[A] b) i = algebraMap B (D i) b)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The actual upper-factor spectrum maps to the original Weil test pullback
by the given tensor decomposition, with its original `B`-structure. -/
def completedTensorWeilRestrictionFactorTestMap (i : ι) :
    ringTest B (D i) ⟶ ringBaseChange A B (ringTest A C) :=
  Over.homMk
    (finiteProductSpecProjection D i ≫
      (weilCoefficientSpecIso C (C ⊗[A] B) (∀ j, D j) e).hom ≫
      (pullbackSpecIso A C B).inv) (by
        change _ ≫ pullback.snd (Spec.algebraMap A C) (Spec.algebraMap A B) = _
        simp only [Category.assoc, pullbackSpecIso_inv_snd]
        exact tensorCoefficientSpecFactor_comp A B C D e he i)

private theorem completedTensorTestIso_inv_fst
    (T : Over (Spec (CommRingCat.of C))) :
    (weilRestrictionTensorBaseChangeTestIso A B C T).inv.left ≫
        pullback.fst T.hom (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B)) =
      pullback.fst T.hom (Spec.algebraMap C (C ⊗[A] B)) := by
  apply (cancel_epi (weilRestrictionTensorBaseChangeTestIso A B C T).hom.left).1
  simp [weilRestrictionTensorBaseChangeTestIso]

private theorem completedTensorTestIso_inv_snd
    (T : Over (Spec (CommRingCat.of C))) :
    (weilRestrictionTensorBaseChangeTestIso A B C T).inv.left ≫
        pullback.snd T.hom (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B)) =
      pullback.snd T.hom (Spec.algebraMap C (C ⊗[A] B)) ≫
        (pullbackSpecIso A C B).inv := by
  apply (cancel_mono (pullbackSpecIso A C B).hom).1
  have h := Over.w (weilRestrictionTensorBaseChangeTestIso A B C T).inv
  change (weilRestrictionTensorBaseChangeTestIso A B C T).inv.left ≫
      (pullback.snd T.hom
        (pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B)) ≫
          (pullbackSpecIso A C B).hom) =
    pullback.snd T.hom (Spec.algebraMap C (C ⊗[A] B)) at h
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    h

private theorem completedProductTestIso_inv_fst_fst
    (T : Over (Spec (CommRingCat.of C))) (i : ι) :
    (finiteProductBaseChangeTestIso D C T i).inv.left ≫
        pullback.fst (ringBaseChange C (∀ j, D j) T).hom (finiteProductSpecProjection D i) ≫
        pullback.fst T.hom (Spec.algebraMap C (∀ j, D j)) =
      pullback.fst T.hom (Spec.algebraMap C (D i)) := by
  apply (cancel_epi (finiteProductBaseChangeTestIso D C T i).hom.left).1
  simp [finiteProductBaseChangeTestIso, ringBaseChange, pullback.congrHom, Category.assoc]

private theorem completedProductTestIso_inv_fst_snd
    (T : Over (Spec (CommRingCat.of C))) (i : ι) :
    (finiteProductBaseChangeTestIso D C T i).inv.left ≫
        pullback.fst (ringBaseChange C (∀ j, D j) T).hom (finiteProductSpecProjection D i) ≫
        pullback.snd T.hom (Spec.algebraMap C (∀ j, D j)) =
      pullback.snd T.hom (Spec.algebraMap C (D i)) ≫ finiteProductSpecProjection D i := by
  change (finiteProductBaseChangeTestIso D C T i).inv.left ≫
      pullback.fst (ringBaseChange C (∀ j, D j) T).hom (finiteProductSpecProjection D i) ≫
      (ringBaseChange C (∀ j, D j) T).hom = _
  rw [pullback.condition]
  have h := Over.w (finiteProductBaseChangeTestIso D C T i).inv
  change (finiteProductBaseChangeTestIso D C T i).inv.left ≫
      pullback.snd (ringBaseChange C (∀ j, D j) T).hom (finiteProductSpecProjection D i) =
    pullback.snd T.hom (Spec.algebraMap C (D i)) at h
  simpa only [← Category.assoc] using
    congrArg (fun f => f ≫ finiteProductSpecProjection D i) h

private theorem completedBaseTestIso_hom_fst (i : ι) :
    (weilRestrictionBaseTestIso C (D i)).hom.left ≫
        pullback.fst (ringTest C C).hom (Spec.algebraMap C (D i)) =
      Spec.algebraMap C (D i) := by
  have hC : (ringTest C C).hom = 𝟙 _ := by
    simp [ringTest, Spec.algebraMap]
  calc
    _ = (weilRestrictionBaseTestIso C (D i)).hom.left ≫
        pullback.fst (ringTest C C).hom (Spec.algebraMap C (D i)) ≫
        (ringTest C C).hom := by
          conv_rhs => arg 2; arg 2; rw [hC]
          rw [Category.comp_id]
    _ = (weilRestrictionBaseTestIso C (D i)).hom.left ≫
        pullback.snd (ringTest C C).hom (Spec.algebraMap C (D i)) ≫
        Spec.algebraMap C (D i) := by rw [pullback.condition]
    _ = _ := by
      rw [← Category.assoc]
      change ((weilRestrictionBaseTestIso C (D i)).hom.left ≫
        (ringBaseChange C (D i) (ringTest C C)).hom) ≫ _ = _
      rw [Over.w]
      simp [ringTest, Spec.algebraMap]

end FactorTest

section General

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Module.Finite A B] [Module.Projective A B]
variable {ι : Type u} (D : ι → Type u) [Finite ι] [∀ i, CommRing (D i)]
  [∀ i, Algebra C (D i)] [∀ i, Algebra B (D i)]
  [∀ i, Module.Finite C (D i)] [∀ i, Module.Projective C (D i)]
  (e : C ⊗[A] B ≃ₐ[C] (∀ i, D i))
  (he : ∀ (b : B) (i : ι), e (1 ⊗ₜ[A] b) i = algebraMap B (D i) b)
variable (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance completedTensorTargetLocallyOfFiniteType :
    LocallyOfFiniteType (ringBaseChange B (C ⊗[A] B) Y).hom :=
  inferInstanceAs (LocallyOfFiniteType
    (pullback.snd Y.hom (Spec.algebraMap B (C ⊗[A] B))))

local instance completedCoefficientTargetLocallyOfFiniteType :
    LocallyOfFiniteType
      (weilCoefficientTarget C (C ⊗[A] B) (∀ j, D j) e
        (ringBaseChange B (C ⊗[A] B) Y)).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd
    (ringBaseChange B (C ⊗[A] B) Y).hom
    (weilCoefficientSpecIso C (C ⊗[A] B) (∀ j, D j) e).hom))

local instance completedFactorTargetLocallyOfFiniteType (i : ι) :
    LocallyOfFiniteType (tensorCoefficientFactorTarget A B C D e Y i).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd
    (weilCoefficientTarget C (C ⊗[A] B) (∀ j, D j) e
      (ringBaseChange B (C ⊗[A] B) Y)).hom (finiteProductSpecProjection D i)))

variable [IsSeparated Y.hom]

local instance completedTensorTargetIsSeparated :
    IsSeparated (ringBaseChange B (C ⊗[A] B) Y).hom :=
  inferInstanceAs (IsSeparated (pullback.snd Y.hom (Spec.algebraMap B (C ⊗[A] B))))

local instance completedCoefficientTargetIsSeparated :
    IsSeparated
      (weilCoefficientTarget C (C ⊗[A] B) (∀ j, D j) e
        (ringBaseChange B (C ⊗[A] B) Y)).hom :=
  inferInstanceAs (IsSeparated (pullback.snd
    (ringBaseChange B (C ⊗[A] B) Y).hom
    (weilCoefficientSpecIso C (C ⊗[A] B) (∀ j, D j) e).hom))

local instance completedFactorTargetIsSeparated (i : ι) :
    IsSeparated (tensorCoefficientFactorTarget A B C D e Y i).hom :=
  inferInstanceAs (IsSeparated (pullback.snd
    (weilCoefficientTarget C (C ⊗[A] B) (∀ j, D j) e
      (ringBaseChange B (C ⊗[A] B) Y)).hom (finiteProductSpecProjection D i)))

variable [TopologicalSpace C] [IsTopologicalRing C] [IsLocalRing C] [IsOpenUnits C]
  [∀ i, TopologicalSpace (D i)] [∀ i, IsTopologicalRing (D i)]
  [∀ i, IsLocalRing (D i)] [∀ i, IsOpenUnits (D i)] [∀ i, IsModuleTopology C (D i)]

/-- Actual tensor base change, coefficient transport, finite-product decomposition
and local Weil comparison give the product of the original target's factor points.
All geometric premises for intermediate targets are derived from `Y`. -/
def completedTensorWeilRestrictionPointHomeomorph
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    letI : TopologicalSpace (RingPoint A (affineChartWeilRestriction A B Y) C) :=
      schemePointTopology A (affineChartWeilRestriction A B Y) C
    letI : ∀ i, TopologicalSpace (RingPoint B Y (D i)) :=
      fun i => schemePointTopology B Y (D i)
    RingPoint A (affineChartWeilRestriction A B Y) C ≃ₜ (∀ i, RingPoint B Y (D i)) := by
  let Z := ringBaseChange B (C ⊗[A] B) Y
  let W := weilCoefficientTarget C (C ⊗[A] B) (∀ j, D j) e Z
  have hZ : HasFiniteAffineNeighborhoods Z.left :=
    hasFiniteAffineNeighborhoods_ringBaseChange B (C ⊗[A] B) Y hY
  have hW : HasFiniteAffineNeighborhoods W.left :=
    hasFiniteAffineNeighborhoods_weilCoefficientTarget C (C ⊗[A] B) (∀ j, D j) e Z hZ
  letI : TopologicalSpace (RingPoint A (affineChartWeilRestriction A B Y) C) :=
    schemePointTopology A (affineChartWeilRestriction A B Y) C
  letI : TopologicalSpace (RingPoint C (affineChartWeilRestriction C (C ⊗[A] B) Z) C) :=
    schemePointTopology C (affineChartWeilRestriction C (C ⊗[A] B) Z) C
  letI : TopologicalSpace (RingPoint C (affineChartWeilRestriction C (∀ j, D j) W) C) :=
    schemePointTopology C (affineChartWeilRestriction C (∀ j, D j) W) C
  letI : ∀ i, TopologicalSpace (RingPoint C
      (affineChartWeilRestriction C (D i) (tensorCoefficientFactorTarget A B C D e Y i)) C) :=
    fun i => schemePointTopology C
      (affineChartWeilRestriction C (D i) (tensorCoefficientFactorTarget A B C D e Y i)) C
  letI : ∀ i, TopologicalSpace
      (RingPoint (D i) (tensorCoefficientFactorTarget A B C D e Y i) (D i)) :=
    fun i => schemePointTopology (D i) (tensorCoefficientFactorTarget A B C D e Y i) (D i)
  letI : ∀ i, TopologicalSpace (RingPoint (D i) (ringBaseChange B (D i) Y) (D i)) :=
    fun i => schemePointTopology (D i) (ringBaseChange B (D i) Y) (D i)
  letI : ∀ i, TopologicalSpace (RingPoint B Y (D i)) :=
    fun i => schemePointTopology B Y (D i)
  exact (affineChartWeilRestrictionTensorPointHomeomorph A B C Y hY).trans
    ((affineChartWeilRestrictionCoefficientPointHomeomorph C (C ⊗[A] B)
      (∀ j, D j) e Z C hZ).trans
      ((affineChartWeilRestrictionProductPointHomeomorph D C C W hW).trans
        (Homeomorph.piCongrRight (fun i =>
          (affineChartWeilRestrictionPointHomeomorph C (D i)
            (tensorCoefficientFactorTarget A B C D e Y i)
            (hasFiniteAffineNeighborhoods_finiteProductFactor D W hW i)).trans
            ((schemePointIsoHomeomorph (D i) (D i)
              (tensorCoefficientFactorTargetIso A B C D e he Y i)).trans
              (schemePointBaseChangeHomeomorph B (D i) (D i) Y).symm)))))

/-- The exact component map is the original local factor comparison after
coefficient transport and the canonical product projection. -/
theorem completedTensorWeilRestrictionPointHomeomorph_apply
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (p : RingPoint A (affineChartWeilRestriction A B Y) C) (i : ι) :
    let Z := ringBaseChange B (C ⊗[A] B) Y
    let W := weilCoefficientTarget C (C ⊗[A] B) (∀ j, D j) e Z
    let hZ := hasFiniteAffineNeighborhoods_ringBaseChange B (C ⊗[A] B) Y hY
    let hW := hasFiniteAffineNeighborhoods_weilCoefficientTarget
      C (C ⊗[A] B) (∀ j, D j) e Z hZ
    completedTensorWeilRestrictionPointHomeomorph A B C D e he Y hY p i =
      (ringPointBaseChangeEquiv B (D i) (D i) Y).symm
        (affineChartWeilRestrictionBasePointComparison C (D i)
          (tensorCoefficientFactorTarget A B C D e Y i)
          (affineChartWeilRestrictionCoefficientPointHomeomorph
              C (C ⊗[A] B) (∀ j, D j) e Z C hZ
              (affineChartWeilRestrictionTensorPointHomeomorph A B C Y hY p) ≫
            affineChartWeilRestrictionProductProjection D C W hW i) ≫
          (tensorCoefficientFactorTargetIso A B C D e he Y i).hom) := by
  dsimp only
  simp only [completedTensorWeilRestrictionPointHomeomorph, Homeomorph.trans_apply,
    Homeomorph.piCongrRight_apply, affineChartWeilRestrictionProductPointHomeomorph_apply]
  let : TopologicalSpace (RingPoint B Y (D i)) := schemePointTopology B Y (D i)
  let : TopologicalSpace (RingPoint (D i) (ringBaseChange B (D i) Y) (D i)) :=
    schemePointTopology (D i) (ringBaseChange B (D i) Y) (D i)
  apply (schemePointBaseChangeHomeomorph B (D i) (D i) Y).injective
  rw [Homeomorph.apply_symm_apply, schemePointBaseChangeHomeomorph_apply,
    Equiv.apply_symm_apply]
  rfl

/-- Each component agrees with the original Weil counit on the actual
factor test spectrum. In particular, no intermediate counit is redefined. -/
theorem completedTensorWeilRestrictionPointHomeomorph_counit
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (p : RingPoint A (affineChartWeilRestriction A B Y) C) (i : ι) :
    completedTensorWeilRestrictionPointHomeomorph A B C D e he Y hY p i =
      completedTensorWeilRestrictionFactorTestMap A B C D e he i ≫
        affineChartWeilRestrictionComparison A B Y (ringTest A C) p := by
  have hforget :
      ((Over.mapPullbackAdj (Spec.algebraMap A C)).homEquiv (ringTest C C)
          (affineChartWeilRestriction A B Y)).symm
        (ringPointBaseChangeEquiv A C C (affineChartWeilRestriction A B Y) p) =
      (ringTestRestrictScalarsIso A C C).hom ≫ p := by
    simp only [ringPointBaseChangeEquiv, Equiv.trans_apply]
    exact ((Over.mapPullbackAdj (Spec.algebraMap A C)).homEquiv (ringTest C C)
      (affineChartWeilRestriction A B Y)).symm_apply_apply _
  rw [completedTensorWeilRestrictionPointHomeomorph_apply]
  apply Over.OverMorphism.ext
  simp only [ringPointBaseChangeEquiv_symm_left, Over.comp_left, Category.assoc,
    tensorCoefficientFactorTargetIso_hom_fst]
  simp only [affineChartWeilRestrictionBasePointComparison, Over.comp_left,
    Category.assoc]
  rw [affineChartWeilRestrictionProductProjection_comparison]
  simp only [affineChartWeilRestrictionProductComparison, Over.comp_left,
    Over.pullback_map_left, Category.assoc]
  rw [affineChartWeilRestrictionCoefficientPointHomeomorph_comparison]
  simp only [pullback.lift_fst_assoc, Category.assoc]
  rw [reassoc_of% affineChartWeilRestrictionCoefficientComparison_fst]
  rw [affineChartWeilRestrictionTensorPointHomeomorph_comparison]
  simp [affineChartWeilRestrictionTensorBaseChangeComparison,
    weilRestrictionTensorBaseChangeTargetIso, Over.comp_left,
    Over.map_map_left, Category.assoc, hforget,
    affineChartWeilRestrictionComparison_natural]
  simp only [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp [completedTensorWeilRestrictionFactorTestMap, weilRestrictionScalarBaseChangeTestIso,
      completedTensorTestIso_inv_fst, weilCoefficientTestIso,
      completedProductTestIso_inv_fst_fst, completedBaseTestIso_hom_fst, Category.assoc]
    change Spec.algebraMap C (D i) = finiteProductSpecProjection D i ≫
      (weilCoefficientSpecIso C (C ⊗[A] B) (∀ j, D j) e).hom ≫
        (pullbackSpecIso A C B).inv ≫
          pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B)
    rw [pullbackSpecIso_inv_fst']
    change Spec.algebraMap C (D i) = finiteProductSpecProjection D i ≫
      (weilCoefficientSpecIso C (C ⊗[A] B) (∀ j, D j) e).hom ≫
        Spec.algebraMap C (C ⊗[A] B)
    simp
  · simp [completedTensorWeilRestrictionFactorTestMap, weilRestrictionScalarBaseChangeTestIso,
      weilCoefficientTestIso, Category.assoc]
    rw [reassoc_of% completedTensorTestIso_inv_snd]
    simp only [pullback.map, pullback.lift_snd_assoc]
    simp only [Category.assoc]
    rw [reassoc_of% completedProductTestIso_inv_fst_snd]
    change (weilRestrictionBaseTestIso C (D i)).hom.left ≫
      (ringBaseChange C (D i) (ringTest C C)).hom ≫ _ = _
    rw [Over.w_assoc]
    simp [ringTest, Spec.algebraMap]

omit [IsSeparated Y.hom] in
/-- An actual relative projective immersion supplies all the geometric
premises of the completed-tensor product homeomorphism. -/
def projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace B n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec B n = Y.hom) :
    letI : TopologicalSpace (RingPoint A (affineChartWeilRestriction A B Y) C) :=
      schemePointTopology A (affineChartWeilRestriction A B Y) C
    letI : ∀ i, TopologicalSpace (RingPoint B Y (D i)) :=
      fun i => schemePointTopology B Y (D i)
    RingPoint A (affineChartWeilRestriction A B Y) C ≃ₜ (∀ i, RingPoint B Y (D i)) := by
  letI := isSeparated_of_projectiveImmersion B Y n j hj
  exact completedTensorWeilRestrictionPointHomeomorph A B C D e he Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B n j)

omit [IsSeparated Y.hom] in
/-- The projective-immersion specialization retains the original counit
on every actual factor test spectrum. -/
theorem projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph_counit
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace B n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec B n = Y.hom)
    (p : RingPoint A (affineChartWeilRestriction A B Y) C) (i : ι) :
    projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
        A B C D e he Y n j hj p i =
      completedTensorWeilRestrictionFactorTestMap A B C D e he i ≫
        affineChartWeilRestrictionComparison A B Y (ringTest A C) p := by
  let := isSeparated_of_projectiveImmersion B Y n j hj
  exact completedTensorWeilRestrictionPointHomeomorph_counit A B C D e he Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B n j) p i

end General

end Langlands.AlgebraicGeometry.PointTopology
