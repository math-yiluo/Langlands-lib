import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionTopology

/-! # Coefficient naturality of the original completed-tensor Weil point map -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

section Factor

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
variable {ι : Type u} (D : ι → Type u) [∀ i, CommRing (D i)]
  [∀ i, Algebra C (D i)] [∀ i, Algebra B (D i)]
  (e : C ⊗[A] B ≃ₐ[C] (∀ i, D i))
  (he : ∀ (b : B) (i : ι), e (1 ⊗ₜ[A] b) i = algebraMap B (D i) b)

/-- The actual factor test map retains the original lower coefficient map. -/
@[reassoc (attr := simp)]
theorem completedTensorWeilRestrictionFactorTestMap_fst (i : ι) :
    (completedTensorWeilRestrictionFactorTestMap A B C D e he i).left ≫
      pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B) =
        Spec.algebraMap C (D i) := by
  change finiteProductSpecProjection D i ≫
    (weilCoefficientSpecIso C (C ⊗[A] B) (∀ j, D j) e).hom ≫
      (pullbackSpecIso A C B).inv ≫ pullback.fst _ _ = _
  rw [pullbackSpecIso_inv_fst']
  change Spec.map (CommRingCat.ofHom (Pi.evalRingHom D i)) ≫
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[A] B))) = _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext fun c => congrFun (e.commutes c) i

variable [Module.Finite A B] [Module.Projective A B]
  (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

/-- The original counit on each actual factor test spectrum, before any topology is used. -/
def completedTensorWeilRestrictionPointMap
    (p : RingPoint A (affineChartWeilRestriction A B Y) C) :
    ∀ i, RingPoint B Y (D i) :=
  fun i => completedTensorWeilRestrictionFactorTestMap A B C D e he i ≫
    affineChartWeilRestrictionComparison A B Y (ringTest A C) p

end Factor

section Naturality

variable (A B C C' : Type u) [CommRing A] [CommRing B] [CommRing C] [CommRing C']
  [Algebra A B] [Algebra A C] [Algebra A C']
variable {ι : Type u} (D D' : ι → Type u) [∀ i, CommRing (D i)] [∀ i, CommRing (D' i)]
  [∀ i, Algebra C (D i)] [∀ i, Algebra B (D i)]
  [∀ i, Algebra C' (D' i)] [∀ i, Algebra B (D' i)]
  (e : C ⊗[A] B ≃ₐ[C] (∀ i, D i))
  (he : ∀ (b : B) (i : ι), e (1 ⊗ₜ[A] b) i = algebraMap B (D i) b)
  (e' : C' ⊗[A] B ≃ₐ[C'] (∀ i, D' i))
  (he' : ∀ (b : B) (i : ι), e' (1 ⊗ₜ[A] b) i = algebraMap B (D' i) b)
  (f : C →ₐ[A] C') (g : ∀ i, D i →ₐ[B] D' i)
  (hfg : ∀ (c : C) (i : ι), g i (algebraMap C (D i) c) =
    algebraMap C' (D' i) (f c))

include hfg in
/-- The original factor test squares commute for compatible coefficient embeddings. -/
theorem completedTensorWeilRestrictionFactorTestMap_natural (i : ι) :
    ringTestMap B (g i) ≫ completedTensorWeilRestrictionFactorTestMap A B C D e he i =
      completedTensorWeilRestrictionFactorTestMap A B C' D' e' he' i ≫
        (Over.pullback (Spec.algebraMap A B)).map (ringTestMap A f) := by
  have hf : ((Over.pullback (Spec.algebraMap A B)).map (ringTestMap A f)).left ≫
      pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B) =
    pullback.fst (Spec.algebraMap A C') (Spec.algebraMap A B) ≫
      (ringTestMap A f).left := by
    change pullback.lift _ _ _ ≫ _ = _
    exact pullback.lift_fst _ _ _
  have hs : (ringTestMap B (g i)).left ≫ Spec.algebraMap C (D i) =
      Spec.algebraMap C' (D' i) ≫ (ringTestMap A f).left := by
    change Spec.map (CommRingCat.ofHom (g i).toRingHom) ≫ Spec.algebraMap C (D i) =
      Spec.algebraMap C' (D' i) ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext fun c => hfg c i
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change ((ringTestMap B (g i)).left ≫
        (completedTensorWeilRestrictionFactorTestMap A B C D e he i).left) ≫
          pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B) =
      ((completedTensorWeilRestrictionFactorTestMap A B C' D' e' he' i).left ≫
        ((Over.pullback (Spec.algebraMap A B)).map (ringTestMap A f)).left) ≫
          pullback.fst (Spec.algebraMap A C) (Spec.algebraMap A B)
    simp only [Category.assoc, hf, completedTensorWeilRestrictionFactorTestMap_fst,
      completedTensorWeilRestrictionFactorTestMap_fst_assoc]
    exact hs
  · exact (Over.w (ringTestMap B (g i) ≫
        completedTensorWeilRestrictionFactorTestMap A B C D e he i)).trans
      (Over.w (completedTensorWeilRestrictionFactorTestMap A B C' D' e' he' i ≫
        (Over.pullback (Spec.algebraMap A B)).map (ringTestMap A f))).symm

variable [Module.Finite A B] [Module.Projective A B]
  (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

include hfg in
/-- Changing the original lower coefficient ring commutes with every original upper component. -/
theorem completedTensorWeilRestrictionPointMap_natural
    (p : RingPoint A (affineChartWeilRestriction A B Y) C) (i : ι) :
    completedTensorWeilRestrictionPointMap A B C' D' e' he' Y (p.changeRing f) i =
      (completedTensorWeilRestrictionPointMap A B C D e he Y p i).changeRing (g i) := by
  change _ ≫ affineChartWeilRestrictionComparison A B Y (ringTest A C')
      (ringTestMap A f ≫ p) = ringTestMap B (g i) ≫ _ ≫ _
  rw [affineChartWeilRestrictionComparison_natural, ← Category.assoc,
    ← completedTensorWeilRestrictionFactorTestMap_natural A B C C' D D' e he e' he' f g hfg i,
    Category.assoc]

variable [Finite ι]
  [∀ i, Module.Finite C (D i)] [∀ i, Module.Projective C (D i)]
  [∀ i, Module.Finite C' (D' i)] [∀ i, Module.Projective C' (D' i)]
  [TopologicalSpace C] [IsTopologicalRing C] [IsLocalRing C] [IsOpenUnits C]
  [TopologicalSpace C'] [IsTopologicalRing C'] [IsLocalRing C'] [IsOpenUnits C']
  [∀ i, TopologicalSpace (D i)] [∀ i, IsTopologicalRing (D i)]
  [∀ i, IsLocalRing (D i)] [∀ i, IsOpenUnits (D i)] [∀ i, IsModuleTopology C (D i)]
  [∀ i, TopologicalSpace (D' i)] [∀ i, IsTopologicalRing (D' i)]
  [∀ i, IsLocalRing (D' i)] [∀ i, IsOpenUnits (D' i)] [∀ i, IsModuleTopology C' (D' i)]

include hfg in
/-- The independently topologized Weil homeomorphisms retain the original coefficient square. -/
theorem completedTensorWeilRestrictionPointHomeomorph_natural [IsSeparated Y.hom]
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (p : RingPoint A (affineChartWeilRestriction A B Y) C) (i : ι) :
    completedTensorWeilRestrictionPointHomeomorph A B C' D' e' he' Y hY
        (p.changeRing f) i =
      (completedTensorWeilRestrictionPointHomeomorph A B C D e he Y hY p i).changeRing
        (g i) := by
  rw [completedTensorWeilRestrictionPointHomeomorph_counit,
    completedTensorWeilRestrictionPointHomeomorph_counit]
  exact completedTensorWeilRestrictionPointMap_natural A B C C' D D' e he e' he'
    f g hfg Y p i

include hfg in
/-- The same coefficient square holds for actual projectively immersed targets. -/
theorem projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph_natural
    (n : ℕ) (j : Y.left ⟶ ProjectiveSpace B n) [IsImmersion j]
    (hj : j ≫ projectiveSpaceToSpec B n = Y.hom)
    (p : RingPoint A (affineChartWeilRestriction A B Y) C) (i : ι) :
    projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph A B C' D' e' he' Y n j hj
        (p.changeRing f) i =
      (projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph
        A B C D e he Y n j hj p i).changeRing (g i) := by
  rw [projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph_counit,
    projectiveImmersionCompletedTensorWeilRestrictionPointHomeomorph_counit]
  exact completedTensorWeilRestrictionPointMap_natural A B C C' D D' e he e' he'
    f g hfg Y p i

end Naturality

end Langlands.AlgebraicGeometry.PointTopology
