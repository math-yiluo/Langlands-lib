import Langlands.Automorphic.GroupSchemeAmbient
import Langlands.Global.AdelicGroupNormOneFunctorial

/-! # Morphism pullbacks on actual continuous rational-invariant functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]
  {G H K : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine H.X.left] [IsAffine K.X.left]

/-- Pull back the original continuous rational-invariant functions along the actual
adelic point map of a group-scheme homomorphism. -/
def continuousPullback (φ : G ⟶ H) :
    ContinuousRationalFunctions F H →ₗ[ℂ] ContinuousRationalFunctions F G where
  toFun f :=
    ⟨⟨fun x => f.val.val (AdelicGroupPoints.map F G H φ x), by
      intro q x
      change f.val.val (AdelicGroupPoints.map F G H φ
        (AdelicGroupPoints.rational F G q * x)) =
          f.val.val (AdelicGroupPoints.map F G H φ x)
      rw [map_mul]
      have hnat := DFunLike.congr_fun (AdelicGroupPoints.rational_naturality F G φ) q
      change AdelicGroupPoints.rational F H
          (G.affinePointsTarget φ (CommAlgCat.of F F) q) =
        AdelicGroupPoints.map F G H φ (AdelicGroupPoints.rational F G q) at hnat
      rw [← hnat]
      exact f.val.property (G.affinePointsTarget φ (CommAlgCat.of F F) q) _⟩,
      f.property.comp (AdelicGroupPoints.map F G H φ).continuous⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem continuousPullback_apply (φ : G ⟶ H)
    (f : ContinuousRationalFunctions F H) (x : AdelicGroupPoints F G) :
    (continuousPullback F φ f).val.val x =
      f.val.val (AdelicGroupPoints.map F G H φ x) := rfl

@[simp]
theorem continuousPullback_id (f : ContinuousRationalFunctions F G) :
    continuousPullback F (𝟙 G) f = f := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change f.val.val (G.affinePointsTarget (𝟙 G) _ x) = f.val.val x
  simp [Langlands.GroupScheme.affinePointsTarget_apply]

/-- Composition of actual group morphisms gives contravariant composition on functions. -/
theorem continuousPullback_comp (φ : G ⟶ H) (ψ : H ⟶ K)
    (f : ContinuousRationalFunctions F K) :
    continuousPullback F (φ ≫ ψ) f =
      continuousPullback F φ (continuousPullback F ψ f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change f.val.val (G.affinePointsTarget (φ ≫ ψ) _ x) =
    f.val.val (H.affinePointsTarget ψ _ (G.affinePointsTarget φ _ x))
  simp [Langlands.GroupScheme.affinePointsTarget_apply, Category.assoc]

/-- The original positive right action is intertwined after restricting the target
action along the same adelic point map. -/
theorem continuousPullback_rightAction (φ : G ⟶ H)
    (f : ContinuousRationalFunctions F H) (g : AdelicGroupPoints F G) :
    continuousPullback F φ
        (continuousRightAction F H (AdelicGroupPoints.map F G H φ g) f) =
      continuousRightAction F G g (continuousPullback F φ f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact congrArg f.val.val ((AdelicGroupPoints.map F G H φ).map_mul x g).symm

/-- The pullback is an intertwining linear map on the original function carriers. -/
def continuousPullbackIntertwiningMap (φ : G ⟶ H) :
    Representation.IntertwiningMap
      ((continuousRightAction F H).comp
        (AdelicGroupPoints.map F G H φ).toMonoidHom)
      (continuousRightAction F G) where
  toLinearMap := continuousPullback F φ
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    exact continuousPullback_rightAction F φ f g

/-- An actual group-scheme isomorphism gives a linear equivalence by pullback,
whose inverse pulls back along its inverse morphism. -/
def continuousPullbackEquiv (e : G ≅ H) :
    ContinuousRationalFunctions F H ≃ₗ[ℂ] ContinuousRationalFunctions F G where
  toLinearMap := continuousPullback F e.hom
  invFun := continuousPullback F e.inv
  left_inv f := by
    change continuousPullback F e.inv (continuousPullback F e.hom f) = f
    rw [← continuousPullback_comp, e.inv_hom_id, continuousPullback_id]
  right_inv f := by
    change continuousPullback F e.hom (continuousPullback F e.inv f) = f
    rw [← continuousPullback_comp, e.hom_inv_id, continuousPullback_id]

@[simp]
theorem continuousPullbackEquiv_apply (e : G ≅ H)
    (f : ContinuousRationalFunctions F H) (x : AdelicGroupPoints F G) :
    (continuousPullbackEquiv F e f).val.val x =
      f.val.val (AdelicGroupPoints.map F G H e.hom x) := rfl

@[simp]
theorem continuousPullbackEquiv_symm_apply (e : G ≅ H)
    (f : ContinuousRationalFunctions F G) (x : AdelicGroupPoints F H) :
    ((continuousPullbackEquiv F e).symm f).val.val x =
      f.val.val (AdelicGroupPoints.map F H G e.inv x) := rfl

end Langlands.Automorphic.GroupSchemeFunctions
