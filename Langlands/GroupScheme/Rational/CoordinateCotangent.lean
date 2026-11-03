import Langlands.GroupScheme.Rational.CoordinateAction
import Mathlib.RingTheory.Ideal.Cotangent

/-! # Actual augmentation cotangents and all-algebra weights -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoordinateWeights

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The actual augmentation quotient I_G/I_G². -/
abbrev Cotangent (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] :=
  (augmentationIdeal G).Cotangent

/-- The quotient map on the actual augmentation, with base-field scalars. -/
def cotangentMk (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] :
    augmentation G →ₗ[k] Cotangent G :=
  ((augmentationIdeal G).toCotangent).restrictScalars k

section Coefficients

variable (G) (A : Type u) [CommRing A] [Algebra k A]

/-- The actual identity augmentation after tensor base change. -/
def baseAugmentation : A ⊗[k] CharacterUnits.Coord G →ₐ[A] A :=
  evaluate (1 : Lie.AffinePoints G A)

/-- The identity ideal in A ⊗ O(G). -/
def baseAugmentationIdeal : Ideal (A ⊗[k] CharacterUnits.Coord G) :=
  RingHom.ker (baseAugmentation G A).toRingHom

/-- The augmentation cotangent after arbitrary coefficient extension. -/
abbrev BaseCotangent := (baseAugmentationIdeal G A).Cotangent

variable {G A}

/-- Extending a function at the identity preserves the augmentation ideal. -/
theorem includeRight_augmentation : augmentationIdeal G ≤
    (baseAugmentationIdeal G A).comap Algebra.TensorProduct.includeRight := by
  intro z hz
  change evaluate (1 : Lie.AffinePoints G A) (1 ⊗ₜ[k] z) = 0
  rw [evaluate_tmul, one_mul, Lie.pointCoordinates_one, AlgHom.comp_apply]
  change (algebraMap k A) (Lie.coordinateOrigin G z) = 0
  rw [show Lie.coordinateOrigin G z = 0 from hz, map_zero]

/-- Scalar extension on actual cotangent classes. No base-change isomorphism is assumed. -/
def cotangentBaseChange : Cotangent G →ₗ[k] BaseCotangent G A :=
  Ideal.mapCotangent (augmentationIdeal G) (baseAugmentationIdeal G A)
    Algebra.TensorProduct.includeRight includeRight_augmentation

/-- The full tensor augmentation is fixed by every actual action pullback. -/
theorem baseAugmentation_action (b : AutomorphicAction S.toGrp G)
    (s : Lie.AffinePoints S.toGrp A) :
    (baseAugmentation G A).comp (actionPullback b s) = baseAugmentation G A := by
  apply Algebra.TensorProduct.ext'
  intro a z
  change evaluate (1 : Lie.AffinePoints G A) (actionPullback b s (a ⊗ₜ[k] z)) =
    evaluate (1 : Lie.AffinePoints G A) (a ⊗ₜ[k] z)
  rw [evaluate_actionPullback, b.act_one, evaluate_tmul]

/-- Stability of the entire augmentation ideal after every base change. -/
theorem actionPullback_augmentation (b : AutomorphicAction S.toGrp G)
    (s : Lie.AffinePoints S.toGrp A) :
    baseAugmentationIdeal G A ≤ (baseAugmentationIdeal G A).comap (actionPullback b s) := by
  intro z hz
  change baseAugmentation G A (actionPullback b s z) = 0
  rw [← AlgHom.comp_apply, baseAugmentation_action]
  exact hz

/-- The induced A-linear action on the actual quotient I_A/I_A². -/
def cotangentAction (b : AutomorphicAction S.toGrp G) (s : Lie.AffinePoints S.toGrp A) :
    BaseCotangent G A →ₗ[A] BaseCotangent G A :=
  Ideal.mapCotangent (baseAugmentationIdeal G A) (baseAugmentationIdeal G A)
    (actionPullback b s) (actionPullback_augmentation b s)

/-- Cotangent classes have the same character labels as CGP's coordinate action. -/
def IsCotangentEigenvector (b : AutomorphicAction S.toGrp G) (χ : characterLattice S)
    (q : Cotangent G) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra k A] (s : Lie.AffinePoints S.toGrp A),
    cotangentAction b s (cotangentBaseChange q) =
      (Lie.characterValue χ s : A) • cotangentBaseChange q

/-- Eigenspaces on I/I², tested after every coefficient extension and every S-point. -/
def cotangentWeightSpace (b : AutomorphicAction S.toGrp G) (χ : characterLattice S) :
    Submodule k (Cotangent G) where
  carrier := IsCotangentEigenvector b χ
  zero_mem' := by intro B _ _ s; simp
  add_mem' := by
    intro x y hx hy B _ _ s
    rw [map_add, map_add, hx B s, hy B s, smul_add]
  smul_mem' := by
    intro a x hx B _ _ s
    rw [map_smul, LinearMap.map_smul_of_tower, hx B s, smul_comm]

/-- The support of the actual augmentation cotangent, without discarding character zero. -/
def cotangentSupport (b : AutomorphicAction S.toGrp G) : Set (characterLattice S) :=
  {χ | ∃ q : Cotangent G, q ≠ 0 ∧ q ∈ cotangentWeightSpace b χ}

end Coefficients

end Langlands.GroupScheme.CoordinateWeights
