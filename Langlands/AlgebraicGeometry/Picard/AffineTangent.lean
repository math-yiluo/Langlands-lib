import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Affine rational tangent vectors and augmented dual-number algebra maps -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]

/-- An algebra map to the dual numbers gives a tangent at the specified affine point
exactly when its first projection is the point's augmentation. -/
lemma isTangentVectorAt_spec_map_iff (r : A →ₐ[K] K) (f : A →ₐ[K] DualNumber K) :
    IsTangentVectorAt (Spec.algebraMap K A)
      (Spec.map (CommRingCat.ofHom r.toRingHom))
      (Spec.map (CommRingCat.ofHom f.toRingHom)) ↔
      (TrivSqZeroExt.fstHom K K K).comp f = r := by
  constructor
  · intro h
    apply AlgHom.coe_ringHom_injective
    have he := h.2
    rw [dualNumberAugmentation, ← Spec.map_comp] at he
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)
  · intro h
    constructor
    · change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K A)) =
        Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K)))
      rw [← Spec.map_comp]
      congr 1
      exact congrArg CommRingCat.ofHom (RingHom.ext f.commutes)
    · change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) ≫
        Spec.map (CommRingCat.ofHom f.toRingHom) =
        Spec.map (CommRingCat.ofHom r.toRingHom)
      rw [← Spec.map_comp]
      exact congrArg (fun g : A →ₐ[K] K => Spec.map (CommRingCat.ofHom g.toRingHom)) h

/-- Affine tangent vectors are precisely augmented algebra homomorphisms to
`K[ε]`. The inverse uses Mathlib's fully faithful `Spec` equivalence over `K`. -/
def affineTangentEquiv (r : A →ₐ[K] K) :
    {f : A →ₐ[K] DualNumber K // (TrivSqZeroExt.fstHom K K K).comp f = r} ≃
      {t : Spec (CommRingCat.of (DualNumber K)) ⟶ Spec (CommRingCat.of A) //
        IsTangentVectorAt (Spec.algebraMap K A)
          (Spec.map (CommRingCat.ofHom r.toRingHom)) t} where
  toFun f := ⟨Spec.map (CommRingCat.ofHom f.val.toRingHom),
    (isTangentVectorAt_spec_map_iff r f.val).mpr f.property⟩
  invFun t := by
    let f := Spec.homEquivAlgHom (R := K) (A := A) (B := DualNumber K)
      ⟨t.val, t.property.1⟩
    have hf : Spec.map (CommRingCat.ofHom f.toRingHom) = t.val :=
      congrArg Subtype.val (Spec.homEquivAlgHom.symm_apply_apply ⟨t.val, t.property.1⟩)
    exact ⟨f, (isTangentVectorAt_spec_map_iff r f).mp (hf.symm ▸ t.property)⟩
  left_inv f := by
    apply Subtype.ext
    exact Spec.homEquivAlgHom.apply_symm_apply f.val
  right_inv t := by
    apply Subtype.ext
    change Spec.map (CommRingCat.ofHom
      (Spec.homEquivAlgHom (R := K) (A := A) (B := DualNumber K)
        ⟨t.val, t.property.1⟩).toRingHom) = t.val
    exact congrArg Subtype.val
      (Spec.homEquivAlgHom.symm_apply_apply ⟨t.val, t.property.1⟩)

@[simp]
lemma affineTangentEquiv_apply_val (r : A →ₐ[K] K)
    (f : {f : A →ₐ[K] DualNumber K // (TrivSqZeroExt.fstHom K K K).comp f = r}) :
    (affineTangentEquiv r f).val = Spec.map (CommRingCat.ofHom f.val.toRingHom) := rfl

/-- The constant algebra lift corresponds to the constant rational tangent vector. -/
lemma spec_map_eq_constant_tangent_iff (r : A →ₐ[K] K)
    (f : A →ₐ[K] DualNumber K) :
    Spec.map (CommRingCat.ofHom f.toRingHom) =
      dualNumberProjection K ≫ Spec.map (CommRingCat.ofHom r.toRingHom) ↔
      f = (TrivSqZeroExt.inlAlgHom K K K).comp r := by
  change Spec.map (CommRingCat.ofHom f.toRingHom) =
    Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) ≫
      Spec.map (CommRingCat.ofHom r.toRingHom) ↔ _
  rw [← Spec.map_comp, Spec.map_inj]
  constructor
  · intro h
    apply AlgHom.coe_ringHom_injective
    exact congrArg CommRingCat.Hom.hom h
  · intro h
    exact congrArg (fun g : A →ₐ[K] DualNumber K => CommRingCat.ofHom g.toRingHom) h

end Langlands.AlgebraicGeometry.Picard
