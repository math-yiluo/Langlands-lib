import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.Jacquet.ReciprocityProof

/-!
# First adjointness for the actual general normalized functors

Evaluation at the identity and covariant orbit functions identify intertwiners
`A → i σ` with intertwiners `r A → σ`. The closed subgroup `U` is explicitly
assumed unimodular. The group and both carrier universes are independent.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.General.FirstAdjointness

universe uG uV uW

open SmoothRep
open Jacquet.Localization

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
variable {P M U : Subgroup G}
variable (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
variable (A : SmoothRep.{0, uG, uV} ℂ G) (σ : SmoothRep.{0, uG, uW} ℂ M)

/-- Evaluation at the identity before descent to the actual relation quotient. -/
def evaluation
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) : A →ₗ[ℂ] σ :=
  Jacquet.CharacterReciprocity.evaluation P A.representation
    (σ.representation.comp h.projection) (inductionCharacter U P hU h.le_normalizer) F

/-- Evaluation of a translated vector is the value of the induced function. -/
theorem evaluation_translate
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) (g : G) (v : A) :
    evaluation h hU A σ F (A.representation g v) =
      Induction.eval P (inducingRepresentation h hU σ) (F v) g :=
  Jacquet.CharacterReciprocity.evaluation_translate P A.representation
    (σ.representation.comp h.projection) (inductionCharacter U P hU h.le_normalizer) F g v

/-- The normalized covariance of evaluation. -/
theorem evaluation_covariance
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) (p : P) (v : A) :
    evaluation h hU A σ F (A.representation p v) =
      ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂˣ) : ℂ) •
        σ.representation (h.projection p) (evaluation h hU A σ F v) :=
  Jacquet.CharacterReciprocity.evaluation_covariance P A.representation
    (σ.representation.comp h.projection) (inductionCharacter U P hU h.le_normalizer) F p v

/-- Evaluation descends through the literal localization-at-one quotient. -/
def descendedEvaluation
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) :
    Coinvariants A.representation U 1 →ₗ[ℂ] σ :=
  lift A.representation U 1 (evaluation h hU A σ F) (by
    intro u v
    have he := evaluation_covariance h hU A σ F ⟨u, h.unipotent_le u.2⟩ v
    simpa only [closedHalfCharacter_unipotent h hU hδ,
      IsSemidirectDecomposition.projection_unipotent, map_one, Module.End.one_apply,
      Units.val_one, one_smul, MonoidHom.one_apply] using he)

/-- The descended evaluation intertwines the inverse-half-modulus Jacquet action. -/
def forward
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) :
    ((jacquetFunctor h hU).obj A).representation.IntertwiningMap σ.representation where
  toLinearMap := descendedEvaluation h hU hδ A σ F
  isIntertwining' m := by
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := mk_surjective A.representation U 1 q
    change descendedEvaluation h hU hδ A σ F
      (((HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer m :
        ℂˣ) : ℂ) • mk A.representation U 1 (A.representation m v)) = _
    rw [map_smul]
    change ((HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer m :
      ℂˣ) : ℂ) • evaluation h hU A σ F (A.representation m v) =
        σ.representation m (evaluation h hU A σ F v)
    rw [evaluation_covariance h hU A σ F ⟨m, h.levi_le m.2⟩ v,
      h.projection_levi, closedHalfCharacter_levi h hU m, smul_smul]
    have hcancel :
        ((HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer m :
          ℂˣ) : ℂ) *
        ((HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer m :
          ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul]
      simp [HaarModulus.closedHalfCharacter, HaarModulus.closedInverseHalfCharacter,
        Jacquet.inverseHalfCharacter]
    rw [hcancel, one_smul]

include hδ in
/-- A Jacquet intertwiner composed with the quotient map is covariant on `P`.
The published equality of inducing representations supplies the normalization
cancellation and the passage from `p` to its actual Levi projection. -/
theorem quotient_covariance
    (f : ((jacquetFunctor h hU).obj A).representation.IntertwiningMap σ.representation)
    (p : P) (v : A) :
    f (mk A.representation U 1 (A.representation p v)) =
      ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂˣ) : ℂ) •
        σ.representation (h.projection p) (f (mk A.representation U 1 v)) := by
  have he := congrArg
    (fun τ : Representation ℂ P (Coinvariants A.representation U 1) =>
      τ p (mk A.representation U 1 v))
    (inducingRepresentation_jacquet_eq h hU hδ A)
  change
    ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂˣ) : ℂ) •
      ((jacquetFunctor h hU).obj A).representation (h.projection p)
        (mk A.representation U 1 v) =
      mk A.representation U 1 (A.representation p v) at he
  rw [← he, map_smul, Representation.IntertwiningMap.isIntertwining]

/-- Covariant orbit functions attached to an actual Jacquet intertwiner. -/
def orbitMap
    (f : ((jacquetFunctor h hU).obj A).representation.IntertwiningMap σ.representation) :
    A.representation.IntertwiningMap
      (Induction.equivariantAction P (inducingRepresentation h hU σ)) where
  toLinearMap :=
    { toFun := fun v => ⟨fun g => f (mk A.representation U 1 (A.representation g v)), by
        intro p g
        change f (mk A.representation U 1 (A.representation ((p : G) * g) v)) =
          ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂˣ) : ℂ) •
            σ.representation (h.projection p)
              (f (mk A.representation U 1 (A.representation g v)))
        rw [map_mul, Module.End.mul_apply]
        exact quotient_covariance h hU hδ A σ f p (A.representation g v)⟩
      map_add' v w := by
        ext g
        exact (f.toLinearMap.comp ((mk A.representation U 1).comp
          (A.representation g))).map_add v w
      map_smul' c v := by
        ext g
        exact (f.toLinearMap.comp ((mk A.representation U 1).comp
          (A.representation g))).map_smul c v }
  isIntertwining' g := by
    ext v x
    change f (mk A.representation U 1 (A.representation x (A.representation g v))) =
      f (mk A.representation U 1 (A.representation (x * g) v))
    rw [map_mul, Module.End.mul_apply]

/-- Smoothness of `A` makes its covariant orbit functions smooth induced vectors. -/
def backward
    (f : ((jacquetFunctor h hU).obj A).representation.IntertwiningMap σ.representation) :
    A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation :=
  smoothLift A.isSmooth (orbitMap h hU hδ A σ f)

/-- First adjointness for the actual normalized induction and Jacquet functors,
with independent group, source-carrier and target-carrier universes. -/
def equiv :
    (A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) ≃ₗ[ℂ]
    (((jacquetFunctor h hU).obj A).representation.IntertwiningMap σ.representation) where
  toFun := forward h hU hδ A σ
  invFun := backward h hU hδ A σ
  left_inv F := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change evaluation h hU A σ F (A.representation g v) =
      Induction.eval P (inducingRepresentation h hU σ) (F v) g
    exact evaluation_translate h hU A σ F g v
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    apply Jacquet.Localization.hom_ext
    ext v
    change f (mk A.representation U 1 (A.representation 1 v)) =
      f (mk A.representation U 1 v)
    rw [map_one, Module.End.one_apply]
  map_add' F H := by
    apply Representation.IntertwiningMap.ext
    apply Jacquet.Localization.hom_ext
    ext v
    rfl
  map_smul' c F := by
    apply Representation.IntertwiningMap.ext
    apply Jacquet.Localization.hom_ext
    ext v
    rfl

@[simp]
theorem equiv_mk
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) (v : A) :
    equiv h hU hδ A σ F (mk A.representation U 1 v) =
      Induction.eval P (inducingRepresentation h hU σ) (F v) 1 := rfl

@[simp]
theorem equiv_symm_eval
    (f : ((jacquetFunctor h hU).obj A).representation.IntertwiningMap σ.representation)
    (v : A) (g : G) :
    Induction.eval P (inducingRepresentation h hU σ)
      ((equiv h hU hδ A σ).symm f v) g =
      f (mk A.representation U 1 (A.representation g v)) := rfl

end Langlands.Aubert.General.FirstAdjointness
