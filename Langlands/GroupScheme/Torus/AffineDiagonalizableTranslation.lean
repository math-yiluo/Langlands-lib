import Langlands.GroupScheme.Torus.AffineCharacterAction
import Langlands.GroupScheme.ImageGenerationSubgroup
import Langlands.CommutativeAlgebra.StronglyGradedGraph

/-! # Translation by an affine diagonalizable subgroup -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace Translation

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- The automorphism `(h,g) ↦ (g,hg)` of the square of a group scheme. -/
def graphIso (G : GroupScheme S) : G.X ⊗ G.X ≅ G.X ⊗ G.X where
  hom := lift (snd _ _) (fst _ _ * snd _ _)
  inv := lift (snd _ _ * (fst _ _)⁻¹) (fst _ _)
  hom_inv_id := by
    apply hom_ext
    · simp [MonObj.comp_mul, GrpObj.comp_inv]
    · simp
  inv_hom_id := by
    apply hom_ext
    · simp
    · simp [MonObj.comp_mul]

/-- The graph of subgroup translation, with the unmodified point first. -/
def graph (i : H ⟶ G) : H.X ⊗ G.X ⟶ G.X ⊗ G.X :=
  lift (snd _ _) ((fst _ _ ≫ i.hom.hom) * snd _ _)

/-- The graph factors as a product inclusion followed by a group automorphism. -/
theorem graph_eq (i : H ⟶ G) :
    graph i = (i.hom.hom ⊗ₘ 𝟙 G.X) ≫ (graphIso G).hom := by
  apply hom_ext
  · simp [graph, graphIso]
  · simp [graph, graphIso, MonObj.comp_mul]

/-- A closed subgroup has a closed translation graph over every base. -/
theorem isClosedImmersion_graph (i : H ⟶ G) (hi : IsClosedSubgroup i) :
    IsClosedImmersion (graph i).left := by
  let : IsClosedImmersion i.hom.hom.left := hi
  have : IsClosedImmersion (i.hom.hom ⊗ₘ 𝟙 G.X).left :=
    ImageGeneration.isClosedImmersion_tensorHom_left _ _
  rw [graph_eq, Over.comp_left]
  infer_instance

end Translation

namespace CharacterAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
variable {G : GroupScheme (Spec R)} [IsAffine G.X.left]

/-- Translation by a diagonalizable subgroup on actual affine coordinate points. -/
def ofTranslation (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G) :
    Action (M := M) (AffineCoordinates.algebra G) where
  act {C} t x := (AffineCoordinates.pointEquiv G C).symm
    ((characterPoint t ≫ i.hom.hom) * AffineCoordinates.pointEquiv G C x)
  one {C} x := by
    apply (AffineCoordinates.pointEquiv G C).injective
    simp only [Equiv.apply_symm_apply, characterPoint_one, MonObj.one_comp, one_mul]
  mul {C} t s x := by
    apply (AffineCoordinates.pointEquiv G C).injective
    simp only [Equiv.apply_symm_apply, characterPoint_mul, MonObj.mul_comp, mul_assoc]
  naturality {C D} f t x := by
    apply (AffineCoordinates.pointEquiv G D).injective
    simp only [Equiv.apply_symm_apply, AffineCoordinates.pointEquiv_comp,
      characterPoint_mapCharacter, MonObj.comp_mul, Category.assoc]

/-- Translation in coordinates agrees with translation on actual scheme points. -/
theorem pointEquiv_ofTranslation_act
    (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G)
    {C : CommAlgCat.{u} R} (t : Multiplicative M →* Cˣ)
    (x : AffineCoordinates.algebra G ⟶ C) :
    AffineCoordinates.pointEquiv G C ((ofTranslation i).act t x) =
      (characterPoint t ≫ i.hom.hom) * AffineCoordinates.pointEquiv G C x :=
  Equiv.apply_symm_apply _ _

/-- Evaluation at the trivial character sums all coefficients. -/
theorem evaluate_one_sum {B : CommAlgCat.{u} R} (q : AddMonoidAlgebra B M) :
    (evaluate (𝟙 B) (1 : Multiplicative M →* Bˣ)).hom q =
      q.coeff.sum (fun _ b => b) := by
  induction q using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    rw [map_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index'] <;> simp
  | single m b =>
    rw [evaluate_single, AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index] <;> simp

/-- Any natural character action supplies the coefficient grading identities. -/
theorem isGrading_coaction {B : CommAlgCat.{u} R} (a : Action (M := M) B) :
    Langlands.CommutativeAlgebra.StronglyGraded.IsGrading (coaction a).hom.toRingHom where
  sum_coeff b := by
    have h := congrArg (fun f : B ⟶ B => f.hom b) (coaction_counit a)
    change (evaluate (𝟙 B) (1 : Multiplicative M →* Bˣ)).hom ((coaction a).hom b) = b at h
    rw [evaluate_one_sum] at h
    exact h
  homogeneous_coeff := coaction_coefficient_homogeneous a

end CharacterAction

end Langlands.GroupScheme
