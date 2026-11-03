import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionCounit
import Langlands.AlgebraicGeometry.PointTopology.AffineProductRingTopologyProof

/-! # Affine-test agreement of the universal Weil-restriction comparison -/

noncomputable section

universe u

open CategoryTheory TensorProduct
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

open Langlands.Algebra

variable (A : Type u) [CommRing A]

/-- Every actual relative spectrum point is the spectrum of its algebra map. -/
theorem ringTestMap_affineRingPointEquiv
    {C T : Type u} [CommRing C] [CommRing T] [Algebra A C] [Algebra A T]
    (p : RingPoint A (ringTest A C) T) :
    ringTestMap A (affineRingPointEquiv A C T p) = p := by
  apply Over.OverMorphism.ext
  exact Spec.map_preimage p.left

variable (B : Type u) [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
variable (X : Over (Spec (CommRingCat.of B))) [IsAffine X.left]
  [LocallyOfFiniteType X.hom]

/-- The canonical comparison on an affine test is exactly the previously
constructed tensor-valued point equivalence, through the actual pullback
presentation. -/
theorem affineWeilRestrictionComparison_affine
    (T : Type u) [CommRing T] [Algebra A T]
    (p : RingPoint A (affineWeilRestriction A B X) T) :
    affineWeilRestrictionComparison A B X (ringTest A T) p =
      (ringBaseChangeSpectrumIso A B T).hom ≫
        affineWeilRestrictionPointEquiv A B X T p := by
  dsimp only [RingPoint, affineWeilRestriction] at p
  let W := WeilRestrictionFiniteType A B (AffineCoordinateRing B X)
  let φ : W →ₐ[A] T := affineRingPointEquiv A W T p
  have hp : ringTestMap A φ = p := ringTestMap_affineRingPointEquiv A p
  let q : ringTest B (B ⊗[A] W) ⟶ X :=
    (affineSchemePointEquiv B X (B ⊗[A] W)).symm
      (AlgPoint.ofAlgHom
        (WeilRestrictionFiniteType.universalPoint A B (AffineCoordinateRing B X)))
  have hn :
      (Over.pullback (Spec.algebraMap A B)).map p ≫
          (ringBaseChangeSpectrumIso A B W).hom =
        (ringBaseChangeSpectrumIso A B T).hom ≫
          ringTestMap B (Algebra.TensorProduct.lTensor (S := B) B φ) := by
    have h := ringBaseChangeSpectrumIso_natural A B φ
    rw [hp] at h
    exact h
  have hq :
      ringTestMap B (Algebra.TensorProduct.lTensor (S := B) B φ) ≫ q =
        affineWeilRestrictionPointEquiv A B X T p := by
    apply (affineSchemePointEquiv B X (B ⊗[A] T)).injective
    erw [affineSchemePointEquiv_changeRing]
    dsimp only [q]
    rw [Equiv.apply_symm_apply]
    erw [affineWeilRestrictionPointEquiv_coordinates A B T p]
    rfl
  change (Over.pullback (Spec.algebraMap A B)).map p ≫
      ((ringBaseChangeSpectrumIso A B W).hom ≫ q) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ q) hn).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun k => (ringBaseChangeSpectrumIso A B T).hom ≫ k) hq)))

/-- The representing equivalence on an actual relative spectrum, with
the actual scheme pullback as its target test object. -/
def affineWeilRestrictionAffineTestEquiv
    (T : Type u) [CommRing T] [Algebra A T] :
    (ringTest A T ⟶ affineWeilRestriction A B X) ≃
      (ringBaseChange A B (ringTest A T) ⟶ X) :=
  (affineWeilRestrictionPointEquiv A B X T).trans
    (ringBaseChangeSpectrumIso A B T).symm.homFromEquiv

/-- The affine-test equivalence has the canonical comparison as its forward map. -/
theorem affineWeilRestrictionAffineTestEquiv_apply
    (T : Type u) [CommRing T] [Algebra A T]
    (p : RingPoint A (affineWeilRestriction A B X) T) :
    affineWeilRestrictionAffineTestEquiv A B X T p =
      affineWeilRestrictionComparison A B X (ringTest A T) p :=
  (affineWeilRestrictionComparison_affine A B X T p).symm

end Langlands.AlgebraicGeometry.PointTopology
