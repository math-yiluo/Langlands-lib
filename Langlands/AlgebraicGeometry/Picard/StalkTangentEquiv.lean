import Langlands.AlgebraicGeometry.Picard.StalkTangent
import Mathlib.RingTheory.DualNumber

/-! # All rational tangent maps arise from the actual stalk -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- The augmentation sends the field's closed point to the dual numbers' closed point. -/
lemma dualNumberAugmentation_closedPoint :
    dualNumberAugmentation K (IsLocalRing.closedPoint K) =
      IsLocalRing.closedPoint (DualNumber K) := by
  let : IsLocalHom (TrivSqZeroExt.fstHom K K K).toRingHom :=
    ⟨fun _ h ↦ TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr h⟩
  exact Spec_closedPoint

/-- A tangent map sends the dual numbers' closed point to its specified base point. -/
lemma IsTangentVectorAt.closedPoint {p : X ⟶ Spec (CommRingCat.of K)}
    {x : Spec (CommRingCat.of K) ⟶ X}
    {t : Spec (CommRingCat.of (DualNumber K)) ⟶ X}
    (ht : IsTangentVectorAt p x t) :
    t (IsLocalRing.closedPoint (DualNumber K)) = x (IsLocalRing.closedPoint K) := by
  rw [← dualNumberAugmentation_closedPoint (K := K)]
  exact congrArg (fun f : Spec (CommRingCat.of K) ⟶ X ↦
    f (IsLocalRing.closedPoint K)) ht.2

/-- Every actual rational tangent map factors through its point's actual stalk. -/
lemma rationalStalkTangentMap_surjective (p : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : IsRationalPoint p x) :
    letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
    Function.Surjective (rationalStalkTangentMap p x hx) := by
  let := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  intro t
  obtain ⟨g, hg⟩ : ∃ g : Spec (CommRingCat.of (DualNumber K)) ⟶
      Spec (X.presheaf.stalk (x (IsLocalRing.closedPoint K))),
      g ≫ X.fromSpecStalk (x (IsLocalRing.closedPoint K)) = t.val := by
    rw [← t.property.closedPoint]
    exact ⟨Spec.map (Scheme.stalkClosedPointTo t.val),
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk t.val⟩
  have hgp : g ≫ Spec.algebraMap K
      (X.presheaf.stalk (x (IsLocalRing.closedPoint K))) = dualNumberProjection K := by
    rw [spec_algebraMap_stalkAlgebraOver, ← Category.assoc, hg, t.property.1]
  let f := Spec.homEquivAlgHom
    (R := K) (A := X.presheaf.stalk (x (IsLocalRing.closedPoint K)))
    (B := DualNumber K) ⟨g, hgp⟩
  have hf : Spec.map (CommRingCat.ofHom f.toRingHom) = g :=
    congrArg Subtype.val ((Spec.homEquivAlgHom
      (R := K) (A := X.presheaf.stalk (x (IsLocalRing.closedPoint K)))
      (B := DualNumber K)).symm_apply_apply ⟨g, hgp⟩)
  have hft : IsTangentVectorAt
      (Spec.algebraMap K (X.presheaf.stalk (x (IsLocalRing.closedPoint K))))
      (Spec.map (CommRingCat.ofHom (rationalStalkAugmentation p x hx).toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom)) := by
    constructor
    · rw [hf]
      exact hgp
    · apply (cancel_mono (X.fromSpecStalk (x (IsLocalRing.closedPoint K)))).mp
      rw [Category.assoc, hf, hg, t.property.2,
        rationalStalkAugmentation_spec_comp p x hx]
  refine ⟨⟨f, (isTangentVectorAt_spec_map_iff _ f).mp hft⟩, ?_⟩
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    X.fromSpecStalk (x (IsLocalRing.closedPoint K)) = t.val
  rw [hf, hg]

/-- Actual augmented stalk maps and actual rational tangent scheme maps are equivalent. -/
def rationalStalkTangentEquiv (p : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : IsRationalPoint p x) :
    letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
    {f : X.presheaf.stalk (x (IsLocalRing.closedPoint K)) →ₐ[K] DualNumber K //
      (TrivSqZeroExt.fstHom K K K).comp f = rationalStalkAugmentation p x hx} ≃
      {t : Spec (CommRingCat.of (DualNumber K)) ⟶ X // IsTangentVectorAt p x t} := by
  let := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  exact Equiv.ofBijective (rationalStalkTangentMap p x hx)
    ⟨rationalStalkTangentMap_injective p x hx,
      rationalStalkTangentMap_surjective p x hx⟩

@[simp]
lemma rationalStalkTangentEquiv_apply_val (p : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : IsRationalPoint p x) :
    letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
    ∀ f, (rationalStalkTangentEquiv p x hx f).val =
      Spec.map (CommRingCat.ofHom f.val.toRingHom) ≫
        X.fromSpecStalk (x (IsLocalRing.closedPoint K)) := by
  let := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  intro f
  rfl

end Langlands.AlgebraicGeometry.Picard
