import Langlands.AlgebraicGeometry.Picard.StalkTangent

/-! # Naturality of the base algebra and augmentation on actual stalks -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

/-- The actual stalk map of a scheme morphism over the base field, as a
homomorphism of the canonical stalk algebras. -/
def stalkMapAlgHomOver (p : X ⟶ Spec (CommRingCat.of K))
    (q : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) (h : f ≫ q = p) (z : X) :
    letI := stalkAlgebraOver p z
    letI := stalkAlgebraOver q (f z)
    Y.presheaf.stalk (f z) →ₐ[K] X.presheaf.stalk z := by
  letI := stalkAlgebraOver p z
  letI := stalkAlgebraOver q (f z)
  refine Spec.homEquivAlgHom ⟨Spec.map (f.stalkMap z), ?_⟩
  rw [spec_algebraMap_stalkAlgebraOver, spec_algebraMap_stalkAlgebraOver,
    ← Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc, h]

lemma stalkMapAlgHomOver_toRingHom (p : X ⟶ Spec (CommRingCat.of K))
    (q : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) (h : f ≫ q = p) (z : X) :
    letI := stalkAlgebraOver p z
    letI := stalkAlgebraOver q (f z)
    (stalkMapAlgHomOver p q f h z).toRingHom = (f.stalkMap z).hom := by
  let := stalkAlgebraOver p z
  let := stalkAlgebraOver q (f z)
  change (Spec.preimage (Spec.map (f.stalkMap z))).hom = _
  rw [Spec.preimage_map]

/-- A morphism over the base field sends rational points to rational points. -/
lemma isRationalPoint_comp_over (p : X ⟶ Spec (CommRingCat.of K))
    (q : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) (h : f ≫ q = p)
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : IsRationalPoint p x) :
    IsRationalPoint q (x ≫ f) := by
  change (x ≫ f) ≫ q = 𝟙 _
  rw [Category.assoc, h, hx]

/-- The actual stalk map respects the augmentations at a rational point and
its image. -/
lemma rationalStalkAugmentation_comp_stalkMapAlgHomOver
    (p : X ⟶ Spec (CommRingCat.of K)) (q : Y ⟶ Spec (CommRingCat.of K))
    (f : X ⟶ Y) (h : f ≫ q = p)
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : IsRationalPoint p x) :
    letI := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
    letI := stalkAlgebraOver q (f (x (IsLocalRing.closedPoint K)))
    (rationalStalkAugmentation p x hx).comp
        (stalkMapAlgHomOver p q f h (x (IsLocalRing.closedPoint K))) =
      rationalStalkAugmentation q (x ≫ f) (isRationalPoint_comp_over p q f h x hx) := by
  let := stalkAlgebraOver p (x (IsLocalRing.closedPoint K))
  let := stalkAlgebraOver q (f (x (IsLocalRing.closedPoint K)))
  let := stalkAlgebraOver q ((x ≫ f) (IsLocalRing.closedPoint K))
  apply AlgHom.coe_ringHom_injective
  change (rationalStalkAugmentation p x hx).toRingHom.comp
      (stalkMapAlgHomOver p q f h (x (IsLocalRing.closedPoint K))).toRingHom =
    (rationalStalkAugmentation q (x ≫ f) (isRationalPoint_comp_over p q f h x hx)).toRingHom
  rw [rationalStalkAugmentation_toRingHom, stalkMapAlgHomOver_toRingHom,
    rationalStalkAugmentation_toRingHom]
  exact congrArg CommRingCat.Hom.hom (Scheme.stalkClosedPointTo_comp x f).symm

/-- Taking the spectrum of a precomposed stalk algebra map agrees with
postcomposing its actual scheme morphism. -/
lemma spec_stalkMapAlgHomOver_comp (p : X ⟶ Spec (CommRingCat.of K))
    (q : Y ⟶ Spec (CommRingCat.of K)) (f : X ⟶ Y) (h : f ≫ q = p) (z : X) :
    letI := stalkAlgebraOver p z
    letI := stalkAlgebraOver q (f z)
    ∀ g : X.presheaf.stalk z →ₐ[K] DualNumber K,
      Spec.map (CommRingCat.ofHom
          (g.comp (stalkMapAlgHomOver p q f h z)).toRingHom) ≫ Y.fromSpecStalk (f z) =
        (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ X.fromSpecStalk z) ≫ f := by
  let := stalkAlgebraOver p z
  let := stalkAlgebraOver q (f z)
  intro g
  change Spec.map (CommRingCat.ofHom (stalkMapAlgHomOver p q f h z).toRingHom ≫
      CommRingCat.ofHom g.toRingHom) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, stalkMapAlgHomOver_toRingHom, CommRingCat.ofHom_hom,
    Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc]

end Langlands.AlgebraicGeometry.Picard
