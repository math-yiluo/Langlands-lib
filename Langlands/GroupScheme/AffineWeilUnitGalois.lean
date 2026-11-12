import Langlands.GroupScheme.AffineWeilUnit
import Langlands.GroupScheme.TensorGaloisPoint

/-! # Galois fixed points of the actual scalar-extension Weil unit -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.AffineWeil

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (F L : Type u) [Field F] [Field L] [Algebra F L]
  [FiniteDimensional F L]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Forget the actual base change in tensor-valued points of the restricted group. -/
def unitGroundPointsEquiv (A : CommAlgCat.{u} (CommRingCat.of F)) :
    (groupScheme F L (unitBaseChange F L G)).affinePoints A ≃*
      G.affinePoints (CommAlgCat.of F (L ⊗[F] A)) :=
  (pointsEquiv F L (unitBaseChange F L G) A).trans
    (affinePointsBaseChangeMulEquiv F L (L ⊗[F] A) G).symm

/-- The coefficient conjugation on the point functor of the actual restricted base change. -/
def unitGaloisPointHom (σ : L ≃ₐ[F] L) (A : CommAlgCat.{u} (CommRingCat.of F)) :
    (pointFunctor F L (unitBaseChange F L G)).obj A →*
      (pointFunctor F L (unitBaseChange F L G)).obj A :=
  (affinePointsBaseChangeMulEquiv F L (L ⊗[F] A) G).toMonoidHom.comp
    ((TensorGaloisPoint.conjugate F L A G σ).comp
      (affinePointsBaseChangeMulEquiv F L (L ⊗[F] A) G).symm.toMonoidHom)

omit [FiniteDimensional F L] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- Base-change point transport intertwines coefficient conjugation and tensor maps. -/
theorem unitGaloisPointHom_naturality (σ : L ≃ₐ[F] L)
    {A B : CommAlgCat.{u} (CommRingCat.of F)} (a : A ⟶ B)
    (q : (pointFunctor F L (unitBaseChange F L G)).obj A) :
    (pointFunctor F L (unitBaseChange F L G)).map a (unitGaloisPointHom F L G σ A q) =
      unitGaloisPointHom F L G σ B
        ((pointFunctor F L (unitBaseChange F L G)).map a q) := by
  let t := Algebra.TensorProduct.lTensor (S := L) L a.hom
  let q' := (affinePointsBaseChangeMulEquiv F L (L ⊗[F] A) G).symm q
  have hnat (p : G.affinePoints (CommAlgCat.of F (L ⊗[F] A))) :=
    affinePointsBaseChangeMulEquiv_naturality F L (L ⊗[F] A) (L ⊗[F] B) G t p
  have hq : (pointFunctor F L (unitBaseChange F L G)).map a q =
      affinePointsBaseChangeMulEquiv F L (L ⊗[F] B) G
        (G.affinePointMap (CommAlgCat.ofHom (t.restrictScalars F)) q') := by
    change (unitBaseChange F L G).affinePointMap (CommAlgCat.ofHom t) q = _
    simpa only [q', MulEquiv.apply_symm_apply] using hnat q'
  change (unitBaseChange F L G).affinePointMap (CommAlgCat.ofHom t)
      (affinePointsBaseChangeMulEquiv F L (L ⊗[F] A) G
        (TensorGaloisPoint.conjugate F L A G σ q')) = _
  rw [hnat]
  change affinePointsBaseChangeMulEquiv F L (L ⊗[F] B) G _ =
    affinePointsBaseChangeMulEquiv F L (L ⊗[F] B) G
      (TensorGaloisPoint.conjugate F L B G σ
        ((affinePointsBaseChangeMulEquiv F L (L ⊗[F] B) G).symm
          ((pointFunctor F L (unitBaseChange F L G)).map a q)))
  rw [hq, MulEquiv.symm_apply_apply]
  apply congrArg (affinePointsBaseChangeMulEquiv F L (L ⊗[F] B) G)
  exact TensorGaloisPoint.conjugate_naturality F L G a.hom σ q'

/-- A natural endomorphism of the original tensor-valued point functor. -/
def unitGaloisTransformation (σ : L ≃ₐ[F] L) :
    pointFunctor F L (unitBaseChange F L G) ⟶ pointFunctor F L (unitBaseChange F L G) where
  app A := GrpCat.ofHom (unitGaloisPointHom F L G σ A)
  naturality A B a := by
    ext q
    exact (unitGaloisPointHom_naturality F L G σ a q).symm

/-- The actual ground-field group endomorphism conjugating the scalar-extension factor. -/
def unitGaloisAction (σ : L ≃ₐ[F] L) :
    groupScheme F L (unitBaseChange F L G) ⟶ groupScheme F L (unitBaseChange F L G) :=
  Corepresented.groupSchemeMap (corepresentableBy F L (unitBaseChange F L G))
    (corepresentableBy F L (unitBaseChange F L G)) (unitGaloisTransformation F L G σ)

/-- The actual morphism recovers coefficient conjugation on every affine test. -/
theorem unitGaloisAction_groundPoints (σ : L ≃ₐ[F] L)
    (A : CommAlgCat.{u} (CommRingCat.of F))
    (q : (groupScheme F L (unitBaseChange F L G)).affinePoints A) :
    unitGroundPointsEquiv F L G A
      ((groupScheme F L (unitBaseChange F L G)).affinePointsTarget
        (unitGaloisAction F L G σ) A q) =
      TensorGaloisPoint.conjugate F L A G σ (unitGroundPointsEquiv F L G A q) := by
  have h := Corepresented.groupSchemeMap_affinePoints
    (corepresentableBy F L (unitBaseChange F L G))
    (corepresentableBy F L (unitBaseChange F L G)) (unitGaloisTransformation F L G σ) q
  change pointsEquiv F L (unitBaseChange F L G) A
    ((groupScheme F L (unitBaseChange F L G)).affinePointsTarget
      (unitGaloisAction F L G σ) A q) = unitGaloisPointHom F L G σ A
        (pointsEquiv F L (unitBaseChange F L G) A q) at h
  change (affinePointsBaseChangeMulEquiv F L (L ⊗[F] A) G).symm
    (pointsEquiv F L (unitBaseChange F L G) A
      ((groupScheme F L (unitBaseChange F L G)).affinePointsTarget
        (unitGaloisAction F L G σ) A q)) = _
  rw [h]
  exact (affinePointsBaseChangeMulEquiv F L (L ⊗[F] A) G).symm_apply_apply _

/-- The original scalar-extension unit is exactly tensor coefficient extension. -/
theorem unitGroundPointsEquiv_unit
    (A : CommAlgCat.{u} (CommRingCat.of F)) (p : G.affinePoints A) :
    unitGroundPointsEquiv F L G A (G.affinePointsTarget (unit F L G) A p) =
      TensorGaloisPoint.extend F L A G p := by
  change (affinePointsBaseChangeMulEquiv F L (L ⊗[F] A) G).symm
    (pointsEquiv F L (unitBaseChange F L G) A
      (G.affinePointsTarget (unit F L G) A p)) = _
  rw [unit_affinePoints]
  exact (affinePointsBaseChangeMulEquiv F L (L ⊗[F] A) G).symm_apply_apply _

variable [IsGalois F L]

/-- On every affine test, the actual unit image is precisely the Galois fixed subgroup. -/
theorem mem_range_unit_iff_galois_fixed
    (A : CommAlgCat.{u} (CommRingCat.of F))
    (q : (groupScheme F L (unitBaseChange F L G)).affinePoints A) :
    q ∈ Set.range (G.affinePointsTarget (unit F L G) A) ↔
      ∀ σ : L ≃ₐ[F] L, (groupScheme F L (unitBaseChange F L G)).affinePointsTarget
        (unitGaloisAction F L G σ) A q = q := by
  have heq : q ∈ Set.range (G.affinePointsTarget (unit F L G) A) ↔
      unitGroundPointsEquiv F L G A q ∈ Set.range (TensorGaloisPoint.extend F L A G) := by
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p, (unitGroundPointsEquiv_unit F L G A p).symm⟩
    · rintro ⟨p, hp⟩
      refine ⟨p, (unitGroundPointsEquiv F L G A).injective ?_⟩
      rw [unitGroundPointsEquiv_unit]
      exact hp
  rw [heq, TensorGaloisPoint.mem_range_extend_iff]
  constructor
  · intro h σ
    apply (unitGroundPointsEquiv F L G A).injective
    rw [unitGaloisAction_groundPoints]
    exact h σ
  · intro h σ
    rw [← unitGaloisAction_groundPoints, h σ]

end Langlands.GroupScheme.AffineWeil
