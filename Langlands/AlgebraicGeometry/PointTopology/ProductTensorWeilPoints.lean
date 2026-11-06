import Langlands.Global.FiniteProjectivePiTensor
import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionNaturality
import Langlands.AlgebraicGeometry.PointTopology.ProductRingPointComparisonProof
import Langlands.Global.AdelicLevelModelPoints

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  {ι : Type u} (C : ι → Type u) [∀ i, CommRing (C i)] [∀ i, Algebra A (C i)]
  (J : ι → Type u) (D : ∀ i, J i → Type u)
  [∀ i j, CommRing (D i j)] [∀ i j, Algebra (C i) (D i j)] [∀ i j, Algebra B (D i j)]
  (e : ∀ i, C i ⊗[A] B ≃ₐ[C i] (∀ j, D i j))
  (he : ∀ i (b : B) (j : J i), e i (1 ⊗ₜ[A] b) j = algebraMap B (D i j) b)

/-- Each original local tensor equivalence also retains the original upper coefficient algebra. -/
def productTensorWeilFactorEquiv (i : ι) :
    B ⊗[A] C i ≃ₐ[B] (∀ j, D i j) :=
  { toRingEquiv := (Algebra.TensorProduct.comm A B (C i)).toRingEquiv.trans (e i).toRingEquiv
    commutes' b := by
      change e i (1 ⊗ₜ[A] b) = algebraMap B (∀ j, D i j) b
      funext j
      exact he i b j }

/-- The original product of local tensors identifies the global coefficient tensor with all factors. -/
def productTensorWeilCoefficientEquiv :
    B ⊗[A] (∀ i, C i) ≃ₐ[B] (∀ z : Σ i, J i, D z.1 z.2) :=
  ((Langlands.Global.finiteProjectivePiTensorEquiv A B C).trans
    (AlgEquiv.piCongrRight (productTensorWeilFactorEquiv A B C J D e he))).trans
      { toFun := fun x z => x z.1 z.2
        invFun := fun x i j => x ⟨i, j⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl
        commutes' := fun _ => rfl }

@[simp]
theorem productTensorWeilCoefficientEquiv_tmul (b : B) (c : ∀ i, C i) (i : ι) (j : J i) :
    productTensorWeilCoefficientEquiv A B C J D e he (b ⊗ₜ[A] c) ⟨i, j⟩ =
      e i (c i ⊗ₜ[A] b) j := rfl

/-- The actual factor test spectrum maps to the original global Weil test pullback. -/
def productTensorWeilFactorTestMap (i : ι) (j : J i) :
    ringTest B (D i j) ⟶ ringBaseChange A B (ringTest A (∀ i, C i)) :=
  ringTestMap B
      ((Pi.evalAlgHom B (fun z : Σ i, J i => D z.1 z.2) ⟨i, j⟩).comp
        (productTensorWeilCoefficientEquiv A B C J D e he).toAlgHom) ≫
    (ringBaseChangeSpectrumIso A B (∀ i, C i)).inv

/-- This factor spectrum is precisely the original local factor test after coordinate restriction. -/
theorem productTensorWeilFactorTestMap_local (i : ι) (j : J i) :
    productTensorWeilFactorTestMap A B C J D e he i j =
      completedTensorWeilRestrictionFactorTestMap A B (C i) (D i) (e i) (he i) j ≫
        (Over.pullback (Spec.algebraMap A B)).map
          (ringTestMap A (Pi.evalAlgHom A C i)) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [productTensorWeilFactorTestMap, Over.comp_left, Category.assoc,
      Over.pullback_map_left, pullback.lift_fst, ringTestMap_left]
    change Spec.map (CommRingCat.ofHom
        ((Pi.evalAlgHom B (fun z : Σ i, J i => D z.1 z.2) ⟨i, j⟩).comp
          (productTensorWeilCoefficientEquiv A B C J D e he).toAlgHom).toRingHom) ≫
        (ringBaseChangeSpectrumIso A B (∀ i, C i)).inv.left ≫
          pullback.fst (Spec.algebraMap A (∀ i, C i)) (Spec.algebraMap A B) =
      (completedTensorWeilRestrictionFactorTestMap A B (C i) (D i) (e i) (he i) j).left ≫
        pullback.fst (Spec.algebraMap A (C i)) (Spec.algebraMap A B) ≫
          Spec.map (CommRingCat.ofHom (Pi.evalAlgHom A C i).toRingHom)
    rw [ringBaseChangeSpectrumIso_inv_fst,
      completedTensorWeilRestrictionFactorTestMap_fst_assoc]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    change e i (c i ⊗ₜ[A] (1 : B)) j = algebraMap (C i) (D i j) (c i)
    exact congrFun ((e i).commutes (c i)) j
  · exact (Over.w (productTensorWeilFactorTestMap A B C J D e he i j)).trans
      (Over.w (completedTensorWeilRestrictionFactorTestMap A B (C i) (D i) (e i) (he i) j ≫
        (Over.pullback (Spec.algebraMap A B)).map
          (ringTestMap A (Pi.evalAlgHom A C i)))).symm

variable (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]
  [IsSeparated Y.hom] [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]
  [∀ i j, IsLocalRing (D i j)]

/-- Original Weil representability and the actual upper product-point bijection give global points. -/
def productTensorWeilPointEquiv (hY : HasFiniteAffineNeighborhoods Y.left) :
    RingPoint A (affineChartWeilRestriction A B Y) (∀ i, C i) ≃
      (∀ z : Σ i, J i, RingPoint B Y (D z.1 z.2)) :=
  (((affineChartWeilRestrictionTestEquiv A B Y hY (ringTest A (∀ i, C i))).trans
      (ringBaseChangeSpectrumIso A B (∀ i, C i)).homFromEquiv).trans
    (ringPointChangeRingEquiv B Y (productTensorWeilCoefficientEquiv A B C J D e he))).trans
      (Equiv.ofBijective (productPointMap B (fun z : Σ i, J i => D z.1 z.2) Y)
        ⟨productPointMap_injective B _ Y, productPointMap_surjective B _ Y⟩)

/-- Every original global component is the original global relative Weil counit on its factor test. -/
theorem productTensorWeilPointEquiv_counit (hY : HasFiniteAffineNeighborhoods Y.left)
    (p : RingPoint A (affineChartWeilRestriction A B Y) (∀ i, C i)) (i : ι) (j : J i) :
    productTensorWeilPointEquiv A B C J D e he Y hY p ⟨i, j⟩ =
      productTensorWeilFactorTestMap A B C J D e he i j ≫
        affineChartWeilRestrictionComparison A B Y (ringTest A (∀ i, C i)) p := by
  change ringTestMap B (Pi.evalAlgHom B (fun z : Σ i, J i => D z.1 z.2) ⟨i, j⟩) ≫
    (ringTestMap B (productTensorWeilCoefficientEquiv A B C J D e he).toAlgHom ≫
      ((ringBaseChangeSpectrumIso A B (∀ i, C i)).inv ≫ _)) = _
  simp only [productTensorWeilFactorTestMap, ringTestMap_comp, Category.assoc,
    affineChartWeilRestrictionTestEquiv_apply]

/-- Restricting a global Weil point to one lower coordinate and then taking its local component
is the same actual upper point. -/
theorem productTensorWeilPointEquiv_local (hY : HasFiniteAffineNeighborhoods Y.left)
    (p : RingPoint A (affineChartWeilRestriction A B Y) (∀ i, C i)) (i : ι) (j : J i) :
    productTensorWeilPointEquiv A B C J D e he Y hY p ⟨i, j⟩ =
      completedTensorWeilRestrictionPointMap A B (C i) (D i) (e i) (he i) Y
        (p.changeRing (Pi.evalAlgHom A C i)) j := by
  rw [productTensorWeilPointEquiv_counit, productTensorWeilFactorTestMap_local]
  change (_ ≫ _) ≫ _ = _ ≫
    affineChartWeilRestrictionComparison A B Y (ringTest A (C i))
      (ringTestMap A (Pi.evalAlgHom A C i) ≫ p)
  rw [affineChartWeilRestrictionComparison_natural, Category.assoc]

end Langlands.AlgebraicGeometry.PointTopology
