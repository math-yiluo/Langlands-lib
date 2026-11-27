import Langlands.Algebra.LieEnvelopingEquiv
import Langlands.Algebra.RelativeEnvelopingCenter

/-! # Transitivity of normalized enveloping center projections -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Algebra.RelativeEnvelopingDecomposition

variable {k A B C : Type*} [CommRing k]
  [Ring A] [Algebra k A] [Ring B] [Algebra k B] [Ring C] [Algebra k C]
  {i : A →ₐ[k] B} {j : B →ₐ[k] C}

/-- Projecting through the intermediate algebra gives the direct projection when both
congruence remainders lie in the ideal of the direct decomposition. -/
theorem centerProjection_comp
    (inner : RelativeEnvelopingDecomposition i) (outer : RelativeEnvelopingDecomposition j)
    (direct : RelativeEnvelopingDecomposition (j.comp i))
    (hOuter : outer.ideal ≤ direct.ideal)
    (hInner : inner.ideal ≤ direct.ideal.comap j.toLinearMap) :
    direct.centerProjection = inner.centerProjection.comp outer.centerProjection := by
  ext z
  apply direct.centerProjection_val_eq
  change z.val - j (i (inner.centerProjection (outer.centerProjection z)).val) ∈ direct.ideal
  have hOuterRem := hOuter (outer.sub_centerProjection_mem z)
  have hInnerRem := hInner (inner.sub_centerProjection_mem (outer.centerProjection z))
  change j ((outer.centerProjection z).val -
    i (inner.centerProjection (outer.centerProjection z)).val) ∈ direct.ideal at hInnerRem
  rw [map_sub] at hInnerRem
  simpa only [sub_add_sub_cancel] using direct.ideal.add_mem hOuterRem hInnerRem

/-- A shift descends through the projection when it restricts to the given shift on
the Levi algebra and preserves the congruence ideal. -/
theorem centerProjection_shift (D : RelativeEnvelopingDecomposition i)
    (a : A ≃ₐ[k] A) (b : B ≃ₐ[k] B)
    (hi : ∀ x : A, b (i x) = i (a x))
    (hIdeal : ∀ x ∈ D.ideal, b x ∈ D.ideal) (z : Subalgebra.center k B) :
    D.centerProjection (LieEnvelopingEquiv.center b z) =
      LieEnvelopingEquiv.center a (D.centerProjection z) := by
  apply Subtype.ext
  apply D.centerProjection_val_eq
  simpa only [LieEnvelopingEquiv.center_apply, map_sub, hi] using
    hIdeal _ (D.sub_centerProjection_mem z)

/-- Normalization applies the shift on the target of a center projection. -/
def normalizedCenterProjection (D : RelativeEnvelopingDecomposition i) (a : A ≃ₐ[k] A) :
    Subalgebra.center k B →ₐ[k] Subalgebra.center k A :=
  (LieEnvelopingEquiv.center a).toAlgHom.comp D.centerProjection

/-- The projection congruence is recovered by undoing the normalization. -/
theorem sub_normalizedCenterProjection_mem (D : RelativeEnvelopingDecomposition i)
    (a : A ≃ₐ[k] A) (z : Subalgebra.center k B) :
    z.val - i (a.symm (D.normalizedCenterProjection a z).val) ∈ D.ideal := by
  change z.val - i (a.symm (a (D.centerProjection z).val)) ∈ D.ideal
  rw [a.symm_apply_apply]
  exact D.sub_centerProjection_mem z

variable (k A B C) in
/-- Normalized projection through an intermediate algebra agrees with direct normalized
projection. The intermediate shift preserves the inner congruence ideal and restricts
to a shift on the final algebra. The direct shift is this restriction followed by
the inner shift. -/
def NormalizedCenterProjectionTransitivityStatement : Prop :=
  ∀ (i : A →ₐ[k] B) (j : B →ₐ[k] C)
    (inner : RelativeEnvelopingDecomposition i) (outer : RelativeEnvelopingDecomposition j)
    (direct : RelativeEnvelopingDecomposition (j.comp i))
    (innerShift restrictedShift : A ≃ₐ[k] A) (outerShift : B ≃ₐ[k] B),
    outer.ideal ≤ direct.ideal →
    inner.ideal ≤ direct.ideal.comap j.toLinearMap →
    (∀ x : A, outerShift (i x) = i (restrictedShift x)) →
    (∀ x ∈ inner.ideal, outerShift x ∈ inner.ideal) →
    direct.normalizedCenterProjection (restrictedShift.trans innerShift) =
      (inner.normalizedCenterProjection innerShift).comp
        (outer.normalizedCenterProjection outerShift)

theorem normalizedCenterProjectionTransitivity :
    NormalizedCenterProjectionTransitivityStatement k A B C := by
  intro i j inner outer direct innerShift restrictedShift outerShift hOuter hInner hi hIdeal
  ext z
  have hShift := inner.centerProjection_shift restrictedShift outerShift hi hIdeal
    (outer.centerProjection z)
  change innerShift (restrictedShift (direct.centerProjection z).val) =
    innerShift (inner.centerProjection
      (LieEnvelopingEquiv.center outerShift (outer.centerProjection z))).val
  rw [centerProjection_comp inner outer direct hOuter hInner, hShift]
  rfl

end Langlands.Algebra.RelativeEnvelopingDecomposition
