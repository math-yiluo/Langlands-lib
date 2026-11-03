import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionMaps
import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeCoordinates

/-! # The actual universal morphism for affine finite-type Weil restriction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TensorProduct
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

open Langlands.Algebra

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

@[reassoc (attr := simp)]
theorem ringBaseChangeSpectrumIso_inv_fst
    (T : Type u) [CommRing T] [Algebra A T] :
    (ringBaseChangeSpectrumIso A B T).inv.left ≫
        pullback.fst (Spec.algebraMap A T) (Spec.algebraMap A B) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T).toRingHom) := by
  change ((pullbackSpecIso A B T).inv ≫
      (pullbackSymmetry (Spec.algebraMap A T) (Spec.algebraMap A B)).inv) ≫ _ = _
  simp [Category.assoc]

@[reassoc (attr := simp)]
theorem ringBaseChangeSpectrumIso_inv_snd
    (T : Type u) [CommRing T] [Algebra A T] :
    (ringBaseChangeSpectrumIso A B T).inv.left ≫
        pullback.snd (Spec.algebraMap A T) (Spec.algebraMap A B) =
      Spec.algebraMap B (B ⊗[A] T) := by
  exact Over.w (ringBaseChangeSpectrumIso A B T).inv

/-- The tensor presentation of actual affine base change is natural in
the test algebra. -/
theorem ringBaseChangeSpectrumIso_natural
    {T U : Type u} [CommRing T] [CommRing U] [Algebra A T] [Algebra A U]
    (φ : T →ₐ[A] U) :
    (Over.pullback (Spec.algebraMap A B)).map (ringTestMap A φ) ≫
        (ringBaseChangeSpectrumIso A B T).hom =
      (ringBaseChangeSpectrumIso A B U).hom ≫
        ringTestMap B (Algebra.TensorProduct.lTensor (S := B) B φ) := by
  apply Over.OverMorphism.ext
  let eT := pullbackSymmetry (Spec.algebraMap A T) (Spec.algebraMap A B) ≪≫
    pullbackSpecIso A B T
  let eU := pullbackSymmetry (Spec.algebraMap A U) (Spec.algebraMap A B) ≪≫
    pullbackSpecIso A B U
  have hφ : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.algebraMap A T =
      Spec.algebraMap A U := Over.w (ringTestMap A φ)
  let k := pullback.lift
    (pullback.fst (Spec.algebraMap A U) (Spec.algebraMap A B) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom))
    (pullback.snd (Spec.algebraMap A U) (Spec.algebraMap A B))
    (by rw [Category.assoc, hφ]; exact pullback.condition)
  change k ≫ eT.hom = eU.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.lTensor (S := B) B φ).toRingHom)
  apply (Iso.eq_comp_inv eT).mp
  apply pullback.hom_ext
  · dsimp only [k]
    rw [pullback.lift_fst]
    apply (cancel_epi eU.inv).mp
    dsimp only [eT, eU, Iso.trans_inv, Iso.trans_hom]
    simp only [Category.assoc, pullbackSymmetry_inv_comp_fst,
      pullbackSpecIso_inv_snd]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    simp only [Category.assoc, pullbackSymmetry_inv_comp_fst,
      pullbackSpecIso_inv_snd]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  · dsimp only [k]
    rw [pullback.lift_snd]
    apply (cancel_epi eU.inv).mp
    dsimp only [eT, eU, Iso.trans_inv, Iso.trans_hom]
    simp only [Category.assoc, pullbackSymmetry_inv_comp_snd,
      pullbackSpecIso_inv_fst]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [← Spec.map_comp]
    congr 1
    ext b
    change b ⊗ₜ[A] (1 : U) = b ⊗ₜ[A] φ 1
    rw [map_one]

variable [Module.Finite A B] [Module.Projective A B]
variable (X : Over (Spec (CommRingCat.of B))) [IsAffine X.left]
  [LocallyOfFiniteType X.hom]

/-- The actual universal morphism from the base change of the constructed
Weil-restriction scheme to the original scheme. -/
def affineWeilRestrictionCounit :
    ringBaseChange A B (affineWeilRestriction A B X) ⟶ X :=
  (ringBaseChangeSpectrumIso A B
    (WeilRestrictionFiniteType A B (AffineCoordinateRing B X))).hom ≫
      (affineSchemePointEquiv B X
        (B ⊗[A] WeilRestrictionFiniteType A B (AffineCoordinateRing B X))).symm
          (AlgPoint.ofAlgHom
            (WeilRestrictionFiniteType.universalPoint A B (AffineCoordinateRing B X)))

/-- The canonical comparison on an arbitrary actual test scheme over `Spec A`. -/
def affineWeilRestrictionComparison
    (T : Over (Spec (CommRingCat.of A)))
    (p : T ⟶ affineWeilRestriction A B X) :
    ringBaseChange A B T ⟶ X :=
  (Over.pullback (Spec.algebraMap A B)).map p ≫ affineWeilRestrictionCounit A B X

/-- The comparison commutes with every morphism of test schemes. -/
theorem affineWeilRestrictionComparison_natural
    {T U : Over (Spec (CommRingCat.of A))} (f : T ⟶ U)
    (p : U ⟶ affineWeilRestriction A B X) :
    affineWeilRestrictionComparison A B X T (f ≫ p) =
      (Over.pullback (Spec.algebraMap A B)).map f ≫
        affineWeilRestrictionComparison A B X U p := by
  dsimp only [affineWeilRestrictionComparison, ringBaseChange]
  rw [Functor.map_comp]
  exact Category.assoc _ _ _

end Langlands.AlgebraicGeometry.PointTopology
