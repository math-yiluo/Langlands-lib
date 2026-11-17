import Langlands.GroupScheme.Torus.AffineDiagonalizableQuotient
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Actual affine translation quotients -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.CharacterAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
variable {G : GroupScheme (Spec R)} [IsAffine G.X.left]
variable (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G)

/-- The actual left-translation map. -/
def translationAction : (Diagonalizable.groupScheme R M).X ⊗ G.X ⟶ G.X :=
  (fst _ _ ≫ i.hom.hom) * snd _ _

/-- The projection from the actual group to its degree-zero spectrum. -/
def translationProjection : G.X ⟶ quotientScheme (ofTranslation i) :=
  (AffineCoordinates.coordinateSchemeIso G).inv ≫ spectrumProjection (ofTranslation i)

/-- The actual translation relation is the fiber square of the invariant map. -/
theorem translationProjection_isPullback (hi : IsClosedSubgroup i) :
    IsPullback (snd _ _) (translationAction i)
      (translationProjection i) (translationProjection i) := by
  let e := AffineCoordinates.coordinateSchemeIso G
  refine (spectrumProjection_isPullback (ofTranslation i) (isStrong_ofTranslation i hi)).of_iso
    (translationProductIso (M := M) G) e e (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (translationProductIso_hom_snd (G := G)).symm
  · change AffineCoordinates.pointEquiv G _ (coaction (ofTranslation i)) = _
    change AffineCoordinates.pointEquiv G _
      ((ofTranslation i).act (universal _) (constant _)) = _
    rw [pointEquiv_ofTranslation_act]
    simp only [translationAction, MonObj.comp_mul, ← Category.assoc,
      translationProductIso_hom_fst, translationProductIso_hom_snd]
  · simp [translationProjection, e]
  · simp [translationProjection, e]

/-- Faithful flatness of the actual quotient projection. -/
theorem translationProjection_flat_surjective (hi : IsClosedSubgroup i) :
    Flat (translationProjection i).left ∧ Surjective (translationProjection i).left := by
  obtain ⟨hf, hs⟩ := spectrumProjection_flat_surjective
    (ofTranslation i) (isStrong_ofTranslation i hi)
  let := hf
  let := hs
  change Flat ((AffineCoordinates.coordinateSchemeIso G).inv.left ≫
    (spectrumProjection (ofTranslation i)).left) ∧
    Surjective ((AffineCoordinates.coordinateSchemeIso G).inv.left ≫
      (spectrumProjection (ofTranslation i)).left)
  exact ⟨inferInstance, inferInstance⟩

/-- Every scheme test sees exactly the left-translation cosets. -/
theorem translationProjection_left_fibers (hi : IsClosedSubgroup i)
    (T : Over (Spec R)) (g h : T ⟶ G.X) :
    g ≫ translationProjection i = h ≫ translationProjection i ↔
      h * g⁻¹ ∈ (SubgroupFunctor.range i).carrier T := by
  let hp := translationProjection_isPullback i hi
  constructor
  · intro he
    let t := hp.lift g h he
    have ht : (t ≫ fst _ _ ≫ i.hom.hom) * g = h := by
      have h₁ := hp.lift_fst g h he
      have h₂ := hp.lift_snd g h he
      change t ≫ snd _ _ = g at h₁
      change t ≫ translationAction i = h at h₂
      simpa only [translationAction, MonObj.comp_mul, Category.assoc, h₁] using h₂
    exact SubgroupFunctor.mem_range.mpr
      ⟨t ≫ fst _ _, (eq_mul_inv_iff_mul_eq.mpr ht)⟩
  · rintro ⟨x, hx⟩
    change x ≫ i.hom.hom = h * g⁻¹ at hx
    have he := congrArg (fun f => lift x g ≫ f) hp.w
    change (lift x g ≫ snd _ _) ≫ translationProjection i =
      (lift x g ≫ translationAction i) ≫ translationProjection i at he
    simpa only [lift_snd, translationAction, MonObj.comp_mul,
      lift_fst_assoc, hx, inv_mul_cancel_right] using he

/-- For a normal subgroup, the fibers have the usual right-coset criterion. -/
theorem translationProjection_fibers (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (T : Over (Spec R)) (g h : T ⟶ G.X) :
    g ≫ translationProjection i = h ≫ translationProjection i ↔
      g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T := by
  rw [translationProjection_left_fibers i hi]
  constructor
  · intro hx
    have hh := hn T g⁻¹ (h * g⁻¹) (Subgroup.mem_top _) hx
    simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hh
  · intro hx
    have hh := hn T g (g⁻¹ * h) (Subgroup.mem_top _) hx
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh

end Langlands.GroupScheme.CharacterAction
