import Langlands.AlgebraicGeometry.Picard.AffineTangent
import Mathlib.AlgebraicGeometry.Stalk

/-! # Rational tangent maps from actual scheme stalks -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

/-- The base algebra structure on an actual scheme stalk, obtained by applying
fully faithful `Spec` to its structural morphism over `K`. -/
@[instance_reducible]
def stalkAlgebraOver (p : X ⟶ Spec (CommRingCat.of K)) (z : X) :
    Algebra K (X.presheaf.stalk z) :=
  (Spec.preimage (X.fromSpecStalk z ≫ p)).hom.toAlgebra

lemma spec_algebraMap_stalkAlgebraOver (p : X ⟶ Spec (CommRingCat.of K)) (z : X) :
    letI := stalkAlgebraOver p z
    Spec.algebraMap K (X.presheaf.stalk z) = X.fromSpecStalk z ≫ p := by
  change Spec.map (Spec.preimage (X.fromSpecStalk z ≫ p)) = _
  exact Spec.map_preimage _

/-- A rational point induces an augmentation of its actual stalk over the base
field. Its underlying ring homomorphism is `Scheme.stalkClosedPointTo x`. -/
def rationalStalkAugmentation (p : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : IsRationalPoint p x) :
    letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
    X.presheaf.stalk (x (IsLocalRing.closedPoint K)) →ₐ[K] K := by
  letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  refine Spec.homEquivAlgHom ⟨Spec.map (Scheme.stalkClosedPointTo x), ?_⟩
  rw [spec_algebraMap_stalkAlgebraOver, ← Category.assoc,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hx]
  simp [Spec.algebraMap]

lemma rationalStalkAugmentation_toRingHom (p : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : IsRationalPoint p x) :
    letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
    (rationalStalkAugmentation p x hx).toRingHom = (Scheme.stalkClosedPointTo x).hom := by
  let := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  change (Spec.preimage (Spec.map (Scheme.stalkClosedPointTo x))).hom = _
  rw [Spec.preimage_map]

lemma rationalStalkAugmentation_spec_comp (p : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : IsRationalPoint p x) :
    letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
    Spec.map (CommRingCat.ofHom (rationalStalkAugmentation p x hx).toRingHom) ≫
      X.fromSpecStalk (x (IsLocalRing.closedPoint K)) = x := by
  let := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  rw [rationalStalkAugmentation_toRingHom p x hx]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk x

/-- Augmented dual-number algebra maps on the actual stalk give actual rational
tangent vectors on the scheme. -/
def rationalStalkTangentMap (p : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : IsRationalPoint p x) :
    letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
    {f : X.presheaf.stalk (x (IsLocalRing.closedPoint K)) →ₐ[K] DualNumber K //
      (TrivSqZeroExt.fstHom K K K).comp f = rationalStalkAugmentation p x hx} →
      {t : Spec (CommRingCat.of (DualNumber K)) ⟶ X // IsTangentVectorAt p x t} := by
  letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  intro f
  have ht := (isTangentVectorAt_spec_map_iff (rationalStalkAugmentation p x hx) f.val).mpr
    f.property
  refine ⟨Spec.map (CommRingCat.ofHom f.val.toRingHom) ≫
    X.fromSpecStalk (x (IsLocalRing.closedPoint K)), ?_, ?_⟩
  · rw [Category.assoc, ← spec_algebraMap_stalkAlgebraOver p, ht.1]
  · rw [← Category.assoc, ht.2, rationalStalkAugmentation_spec_comp p x hx]

@[simp]
lemma rationalStalkTangentMap_apply_val (p : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : IsRationalPoint p x) :
    letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
    ∀ f, (rationalStalkTangentMap p x hx f).val =
      Spec.map (CommRingCat.ofHom f.val.toRingHom) ≫
        X.fromSpecStalk (x (IsLocalRing.closedPoint K)) := by
  let := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  intro f
  rfl

/-- No distinct augmented stalk algebra maps are identified by the tangent map. -/
lemma rationalStalkTangentMap_injective (p : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : IsRationalPoint p x) :
    letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
    Function.Injective (rationalStalkTangentMap p x hx) := by
  let := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  intro f g h
  apply Subtype.ext
  apply AlgHom.coe_ringHom_injective
  have he := congrArg Subtype.val h
  simp only [rationalStalkTangentMap_apply_val] at he
  have he' := (cancel_mono (X.fromSpecStalk (x (IsLocalRing.closedPoint K)))).mp he
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective he')

/-- A tangent constructed from the stalk is constant precisely when its algebra
map is the constant lift of the point's augmentation. -/
lemma rationalStalkTangentMap_eq_constant_iff (p : X ⟶ Spec (CommRingCat.of K))
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : IsRationalPoint p x) :
    letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
    ∀ f, (rationalStalkTangentMap p x hx f).val = dualNumberProjection K ≫ x ↔
      f.val = (TrivSqZeroExt.inlAlgHom K K K).comp (rationalStalkAugmentation p x hx) := by
  let := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  intro f
  have hconst : dualNumberProjection K ≫ x =
      (dualNumberProjection K ≫
        Spec.map (CommRingCat.ofHom (rationalStalkAugmentation p x hx).toRingHom)) ≫
          X.fromSpecStalk (x (IsLocalRing.closedPoint K)) := by
    rw [Category.assoc, rationalStalkAugmentation_spec_comp p x hx]
  rw [rationalStalkTangentMap_apply_val, hconst, cancel_mono]
  exact spec_map_eq_constant_tangent_iff _ _

end Langlands.AlgebraicGeometry.Picard
