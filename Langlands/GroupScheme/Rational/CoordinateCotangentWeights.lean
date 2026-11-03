import Langlands.GroupScheme.Rational.CoordinateWeightDecompositionStatement
import Mathlib.RingTheory.Ideal.CotangentBaseChange
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Cotangent base change and actual coordinate weights -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoordinateWeights

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The base augmentation is the tensor extension of the original augmentation. -/
theorem baseAugmentation_eq (A : Type u) [CommRing A] [Algebra k A] :
    (baseAugmentation G A).restrictScalars k =
      (Algebra.TensorProduct.rid k k A).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id k A) (Lie.coordinateOrigin G)) := by
  apply Algebra.TensorProduct.ext'
  intro a f
  change evaluate (1 : Lie.AffinePoints G A) (a ⊗ₜ[k] f) = _
  rw [evaluate_tmul, Lie.pointCoordinates_one]
  simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.rid_tmul,
    Algebra.smul_def, mul_comm]

/-- Tensor extension carries the identity augmentation ideal to the actual base ideal. -/
theorem baseAugmentationIdeal_eq (A : Type u) [CommRing A] [Algebra k A] :
    baseAugmentationIdeal G A =
      (augmentationIdeal G).map
        (Algebra.TensorProduct.includeRight.toRingHom :
          CharacterUnits.Coord G →+* A ⊗[k] CharacterUnits.Coord G) := by
  have hs : Function.Surjective (Lie.coordinateOrigin G) := by
    intro c
    exact ⟨algebraMap k (CharacterUnits.Coord G) c, (Lie.coordinateOrigin G).commutes c⟩
  change baseAugmentationIdeal G A =
    (RingHom.ker (Lie.coordinateOrigin G)).map
      (Algebra.TensorProduct.includeRight : CharacterUnits.Coord G →ₐ[k]
        A ⊗[k] CharacterUnits.Coord G)
  rw [← Algebra.TensorProduct.lTensor_ker (A := A) (Lie.coordinateOrigin G) hs]
  ext z
  change baseAugmentation G A z = 0 ↔ _
  rw [show baseAugmentation G A z =
    Algebra.TensorProduct.rid k k A
      (Algebra.TensorProduct.map (AlgHom.id k A) (Lie.coordinateOrigin G) z) from
        DFunLike.congr_fun (baseAugmentation_eq (G := G) A) z]
  exact (Algebra.TensorProduct.rid k k A).map_eq_zero_iff

/-- The actual cotangent after coefficient extension is the tensor base change. -/
def cotangentTensorEquiv (A : Type u) [CommRing A] [Algebra k A] :
    A ⊗[k] Cotangent G ≃ₗ[A] BaseCotangent G A :=
  ((augmentationIdeal G).tensorCotangentEquiv k A).trans
    ((Ideal.Cotangent.equivOfEq _ _ (baseAugmentationIdeal_eq (G := G) A).symm).restrictScalars A)

@[simp] theorem cotangentTensorEquiv_tmul (A : Type u) [CommRing A] [Algebra k A]
    (a : A) (q : Cotangent G) :
    cotangentTensorEquiv (G := G) A (a ⊗ₜ[k] q) = a • cotangentBaseChange q := by
  obtain ⟨f, rfl⟩ := (augmentationIdeal G).toCotangent_surjective q
  simp only [cotangentTensorEquiv, LinearEquiv.trans_apply, Ideal.tensorCotangentEquiv_tmul,
    LinearEquiv.restrictScalars_apply, map_smul, Ideal.Cotangent.equivOfEq_toCotangent]
  rfl

/-- Character evaluation is natural in the coefficient algebra. -/
theorem characterValue_affineMap {A B : Type u} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (f : A →ₐ[k] B)
    (χ : characterLattice S) (s : Lie.AffinePoints S.toGrp A) :
    Lie.characterValue χ (Lie.affineMap S.toGrp f s) =
      Units.map f.toRingHom.toMonoidHom (Lie.characterValue χ s) := by
  change Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k B)
    (Lie.affineMap S.toGrp f s ≫ χ.toMul.hom.hom) = _
  have h := Gm.affineUnitsEquiv_naturality (CommRingCat.of k)
    (CommAlgCat.ofHom f) (s ≫ χ.toMul.hom.hom)
  exact h

/-- An actual eigenfunction gives a pure tensor under every coordinate pullback. -/
theorem actionCoordinates_of_mem_weightSpace (b : AutomorphicAction S.toGrp G)
    (χ : characterLattice S) {f : CharacterUnits.Coord G} (hf : f ∈ weightSpace b χ)
    {A : Type u} [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A) :
    actionCoordinates b s f = (Lie.characterValue χ s : A) ⊗ₜ[k] f := by
  have h := hf (A ⊗[k] CharacterUnits.Coord G)
    (Lie.affineMap S.toGrp Algebra.TensorProduct.includeLeft s)
    ((Lie.pointCoordinates G).symm Algebra.TensorProduct.includeRight)
  change actionCoordinates b s f = _ at h
  rw [characterValue_affineMap, Equiv.apply_symm_apply] at h
  change actionCoordinates b s f =
    Algebra.TensorProduct.includeLeft (Lie.characterValue χ s : A) *
      Algebra.TensorProduct.includeRight f at h
  simpa only [Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul] using h

/-- The actual augmentation quotient preserves each character eigenspace. -/
theorem cotangentMk_mem_weightSpace (b : AutomorphicAction S.toGrp G)
    (χ : characterLattice S) {f : augmentation G}
    (hf : f ∈ augmentationWeightSpace b χ) :
    cotangentMk G f ∈ cotangentWeightSpace b χ := by
  intro A _ _ s
  change Ideal.mapCotangent _ _ _ _ (Ideal.mapCotangent _ _ _ _
    ((augmentationIdeal G).toCotangent f)) = _
  rw [Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent]
  change (baseAugmentationIdeal G A).toCotangent
    ⟨actionPullback b s (1 ⊗ₜ[k] f.val), _⟩ = _
  have he :
      (⟨actionPullback b s (1 ⊗ₜ[k] f.val),
        actionPullback_augmentation b s (includeRight_augmentation f.property)⟩ :
          baseAugmentationIdeal G A) =
      (Lie.characterValue χ s : A) •
        ⟨1 ⊗ₜ[k] f.val, includeRight_augmentation f.property⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_smul_of_tower, actionPullback_tmul, one_smul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact actionCoordinates_of_mem_weightSpace b χ (f := f.val) hf s
  rw [he]
  exact ((baseAugmentationIdeal G A).toCotangent.restrictScalars A).map_smul _ _

end Langlands.GroupScheme.CoordinateWeights
