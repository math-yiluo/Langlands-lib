import Langlands.GroupScheme.HomogeneousQuotientSchemeAction
import Langlands.GroupScheme.Dynamic.AttractingOrbitClosed
import Langlands.GroupScheme.Absolute.CentralizerProductQuotient

/-! # Closed products from affine homogeneous quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace CentralizerProduct

variable {S : Scheme.{u}} (M B : GroupScheme S)

/-- Interchange the two actual factors and invert both group coordinates. -/
def reverseInvIso : M.X ⊗ B.X ≅ B.X ⊗ M.X where
  hom := lift (snd M.X B.X)⁻¹ (fst M.X B.X)⁻¹
  inv := lift (snd B.X M.X)⁻¹ (fst B.X M.X)⁻¹
  hom_inv_id := by
    apply hom_ext <;> simp [GrpObj.comp_inv]
  inv_hom_id := by
    apply hom_ext <;> simp [GrpObj.comp_inv]

variable {M B} {G : GroupScheme S} (j : M ⟶ G) (b : B ⟶ G)

/-- Reversing and inverting both factors inverts their product in the ambient group. -/
theorem reverseInvIso_comp_productHom :
    (reverseInvIso M B).hom ≫ productHom b j = productHom j b ≫ ι[G.X] := by
  rw [reverseInvIso, lift_productHom]
  simp only [GrpObj.inv_comp]
  change _ = (productHom j b)⁻¹
  simp only [productHom, SubgroupFunctor.cellMultiplication, mul_inv_rev]

/-- Inversion preserves closedness while reversing the order of the two subgroup images. -/
theorem isClosed_range_productHom_swap
    (hc : IsClosed (Set.range (productHom j b).left)) :
    IsClosed (Set.range (productHom b j).left) := by
  have hi : IsIso (ι[G.X]).left := (Over.forget S).map_isIso ι[G.X]
  have hs : Surjective (reverseInvIso M B).hom.left := by
    have : IsIso (reverseInvIso M B).hom.left :=
      (Over.forget S).map_isIso (reverseInvIso M B).hom
    infer_instance
  let := hs
  have he : Set.range (productHom b j).left =
      (ι[G.X]).left '' Set.range (productHom j b).left := by
    calc
      _ = Set.range ((reverseInvIso M B).hom ≫ productHom b j).left := by
        change _ = Set.range ((productHom b j).left ∘ (reverseInvIso M B).hom.left)
        rw [Set.range_comp, (reverseInvIso M B).hom.left.surjective.range_eq, Set.image_univ]
      _ = Set.range (productHom j b ≫ ι[G.X]).left := by
        rw [reverseInvIso_comp_productHom]
      _ = _ := by
        change Set.range ((ι[G.X]).left ∘ (productHom j b).left) = _
        exact Set.range_comp _ _
  rw [he]
  exact (ι[G.X]).left.homeomorph.isClosedMap _ hc

end CentralizerProduct

namespace HomogeneousQuotientFromEmbedding.HomogeneousQuotient

open Dynamic.Affine

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))} {i : H ⟶ G}
  [IsAffine G.X.left] [Smooth G.X.hom]
  (Q : HomogeneousQuotient i) [IsAffine Q.scheme.left]
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ H)

/-- The actual ambient dynamic parabolic mapped to the supplied identity coset quotient. -/
def parabolicIdentityOrbit : (parabolicScheme (χ ≫ i)).X ⟶ Q.scheme :=
  (parabolicHom (χ ≫ i)).hom.hom ≫ Q.projection

omit [IsAffine G.X.left] [Smooth G.X.hom] [IsAffine Q.scheme.left] in
/-- The original quotient action orbit of the identity coset is its supplied projection. -/
theorem action_orbitMap_identityCoset : Q.action.orbitMap Q.identityCoset = Q.projection := by
  rw [SchemeAction.orbitMap, identityCoset, ← Category.assoc, MonObj.comp_one,
    Q.action_act_lift, mul_one, Category.id_comp]

/-- The ambient dynamic parabolic has closed orbit through the supplied identity coset. -/
theorem isClosed_range_parabolicIdentityOrbit :
    IsClosed (Set.range (Q.parabolicIdentityOrbit χ).left) := by
  let := Q.smooth_structure
  have hx : (Q.action.cocharacterAction (χ ≫ i)).IsFixed Q.identityCoset := by
    intro T b t
    simpa only [SchemeAction.cocharacterAction, SchemeAction.toPointwiseSchemeAction_act,
      SchemeAction.restrict_act, Category.assoc, Grp.comp_hom_hom] using
      Q.identityCoset_isFixed T b (t ≫ χ.hom.hom)
  have hc := Q.action.isClosed_range_parabolic_orbitMap_of_isFixed (χ ≫ i)
    Q.smooth_action_relation Q.identityCoset hx
  simpa only [SchemeAction.cocharacterParabolicOrbitMap,
    Q.action_orbitMap_identityCoset, parabolicIdentityOrbit] using hc

include Q in
/-- Pulling back the closed parabolic orbit gives the closed parabolic-subgroup product. -/
theorem isClosed_range_parabolic_product [Mono i.hom.hom] :
    IsClosed (Set.range (CentralizerProduct.productHom (parabolicHom (χ ≫ i)) i).left) := by
  rw [CentralizerProduct.product_range_eq_preimage _ _ Q.projection Q.fibers]
  exact (Q.isClosed_range_parabolicIdentityOrbit χ).preimage Q.projection.left.continuous

include Q in
/-- Inversion gives the closed subgroup-parabolic product used by quotient comparisons. -/
theorem isClosed_range_product_parabolic [Mono i.hom.hom] :
    IsClosed (Set.range (CentralizerProduct.productHom i (parabolicHom (χ ≫ i))).left) :=
  CentralizerProduct.isClosed_range_productHom_swap _ _
    (Q.isClosed_range_parabolic_product χ)

end HomogeneousQuotientFromEmbedding.HomogeneousQuotient

end Langlands.GroupScheme
