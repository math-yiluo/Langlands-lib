import Langlands.GroupScheme.Rational.PointedCoordinateAction

/-! # Actual pointed product actions and tensor weights -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.PointedCoordinateWeights

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {V W : Over (Spec (CommRingCat.of k))}

namespace PointedAction

/-- The componentwise actual action with the pair of distinguished points. -/
def prod (a : PointedAction S V) (b : PointedAction S W) :
    PointedAction S (V ⊗ W) where
  hom := lift (a.act (fst _ _) (snd _ _ ≫ fst _ _))
    (b.act (fst _ _) (snd _ _ ≫ snd _ _))
  origin := lift a.origin b.origin
  one_left v := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [act, comp_lift, comp_lift_assoc, a.one_left, b.one_left]
  mul_left s t v := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [act, comp_lift, comp_lift_assoc, a.mul_left, b.mul_left]
  origin_fixed s := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [act, comp_lift, comp_lift_assoc, a.origin_fixed, b.origin_fixed]

@[simp] theorem prod_act_fst (a : PointedAction S V) (b : PointedAction S W)
    {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X) (v : T ⟶ V ⊗ W) :
    (a.prod b).act s v ≫ fst V W = a.act s (v ≫ fst V W) := by
  simp [act, prod, comp_lift, comp_lift_assoc]

@[simp] theorem prod_act_snd (a : PointedAction S V) (b : PointedAction S W)
    {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X) (v : T ⟶ V ⊗ W) :
    (a.prod b).act s v ≫ snd V W = b.act s (v ≫ snd V W) := by
  simp [act, prod, comp_lift, comp_lift_assoc]

end PointedAction

variable [IsAffineHom V.hom] [IsAffineHom W.hom]

instance prod_isAffineHom : IsAffineHom (V ⊗ W).hom := by
  change IsAffineHom (Limits.pullback.fst V.hom W.hom ≫ V.hom)
  let : IsAffineHom (Limits.pullback.fst V.hom W.hom) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  infer_instance

/-- The tensor of the actual input coordinates presents their actual product. -/
def tensorPresentation :
    (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k)
      (Coord V ⊗[k] Coord W))) ≅ V ⊗ W :=
  letI : Limits.PreservesLimits (algSpec (CommRingCat.of k)) :=
    AlgebraicGeometry.preservesLimitsOfSize_algSpec
  prodComparisonIso (algSpec (CommRingCat.of k)) (op (Coord V)) (op (Coord W)) ≪≫
    (coordinateIso V ⊗ᵢ coordinateIso W)

theorem universalPoint_eq_coordinateIso :
    universalPoint V = (coordinateIso V).hom := by
  simp [universalPoint, pointCoordinates]

theorem tensorPresentation_hom :
    (tensorPresentation (V := V) (W := W)).hom =
      lift (pointsMap Algebra.TensorProduct.includeLeft (universalPoint V))
        (pointsMap Algebra.TensorProduct.includeRight (universalPoint W)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [tensorPresentation, Iso.trans_hom, tensorIso_hom, lift_fst,
      pointsMap, universalPoint_eq_coordinateIso]
    rw [Category.assoc, tensorHom_fst, ← Category.assoc, prodComparisonIso_hom,
      prodComparison_fst]
    rfl
  · simp only [tensorPresentation, Iso.trans_hom, tensorIso_hom, lift_snd,
      pointsMap, universalPoint_eq_coordinateIso]
    rw [Category.assoc, tensorHom_snd, ← Category.assoc, prodComparisonIso_hom,
      prodComparison_snd]
    rfl

/-- Coordinates of the actual product identified with the tensor algebra. -/
def tensorCoordinates : Coord (V ⊗ W) ≃ₐ[k] Coord V ⊗[k] Coord W :=
  CommAlgCat.algEquivOfIso
    ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimageIso
      (tensorPresentation ≪≫ (coordinateIso (V ⊗ W)).symm)).unop

theorem tensorCoordinates_toAlgHom :
    (tensorCoordinates (V := V) (W := W)).toAlgHom =
      pointCoordinates (tensorPresentation (V := V) (W := W)).hom := rfl

@[simp] theorem tensorCoordinates_pullback_fst (z : Coord V) :
    (tensorCoordinates (V := V) (W := W)) (pullback (fst V W) z) = z ⊗ₜ[k] (1 : Coord W) := by
  change (tensorCoordinates (V := V) (W := W)).toAlgHom (pullback (fst V W) z) = _
  rw [tensorCoordinates_toAlgHom, ← AlgHom.comp_apply, ← coordinates_comp,
    tensorPresentation_hom, lift_fst, pointCoordinates_naturality,
    coordinates_universalPoint, AlgHom.comp_id]
  rfl

@[simp] theorem tensorCoordinates_pullback_snd (z : Coord W) :
    (tensorCoordinates (V := V) (W := W)) (pullback (snd V W) z) = (1 : Coord V) ⊗ₜ[k] z := by
  change (tensorCoordinates (V := V) (W := W)).toAlgHom (pullback (snd V W) z) = _
  rw [tensorCoordinates_toAlgHom, ← AlgHom.comp_apply, ← coordinates_comp,
    tensorPresentation_hom, lift_snd, pointCoordinates_naturality,
    coordinates_universalPoint, AlgHom.comp_id]
  rfl

theorem tensorCoordinates_symm_tmul (x : Coord V) (y : Coord W) :
    (tensorCoordinates (V := V) (W := W)).symm (x ⊗ₜ[k] y) =
      pullback (fst V W) x * pullback (snd V W) y := by
  apply (tensorCoordinates (V := V) (W := W)).injective
  simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- The actual product eigenspace in tensor coordinates. -/
def tensorWeightSpace (a : PointedAction S V) (b : PointedAction S W)
    (χ : characterLattice S) : Submodule k (Coord V ⊗[k] Coord W) :=
  (weightSpace (a.prod b) χ).map tensorCoordinates.toLinearMap

/-- Pure tensors add characters for the actual action on every test algebra. -/
theorem tmul_mem_tensorWeightSpace (a : PointedAction S V) (b : PointedAction S W)
    {α β : characterLattice S} {x : Coord V} {y : Coord W}
    (hx : x ∈ weightSpace a α) (hy : y ∈ weightSpace b β) :
    x ⊗ₜ[k] y ∈ tensorWeightSpace a b (α + β) := by
  refine ⟨pullback (fst V W) x * pullback (snd V W) y, ?_, ?_⟩
  · intro A _ _ s v
    have hα := hx A s (v ≫ fst V W)
    have hβ := hy A s (v ≫ snd V W)
    have hχ : (Lie.characterValue (α + β) s : A) =
        (Lie.characterValue α s : A) * (Lie.characterValue β s : A) := by
      simp only [Lie.characterValue, comp_groupHom_add, map_mul, Units.val_mul]
    simp only [map_mul]
    change (pointCoordinates ((a.prod b).act s v)).comp (pullback (fst V W)) x *
        (pointCoordinates ((a.prod b).act s v)).comp (pullback (snd V W)) y = _
    rw [← coordinates_comp, ← coordinates_comp,
      PointedAction.prod_act_fst, PointedAction.prod_act_snd, hα, hβ, hχ]
    simp only [← AlgHom.comp_apply, ← coordinates_comp]
    ring
  · change (tensorCoordinates (V := V) (W := W)) (_ * _) = _
    simp [Algebra.TensorProduct.tmul_mul_tmul]

end Langlands.GroupScheme.PointedCoordinateWeights
