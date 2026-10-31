import Langlands.GroupScheme.GeneralLinearDualNumber
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Affine dual-number base change -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Picard.DualNumberBaseChange

open Langlands.GroupScheme.GeneralLinear.DualNumber

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]

/-- The tensor-product map to dual numbers over the coefficient algebra. -/
def tensorTo : R ⊗[k] DualNumber k →ₐ[R] DualNumber R :=
  Algebra.TensorProduct.lift (TrivSqZeroExt.inlAlgHom R R R)
    (coefficientAlgMap (R := CommRingCat.of k) (Algebra.ofId k R))
    (fun _ _ ↦ Commute.all _ _)

/-- The inverse sends epsilon to the epsilon in the second tensor factor. -/
def tensorFrom : DualNumber R →ₐ[R] R ⊗[k] DualNumber k :=
  DualNumber.lift ⟨(Algebra.ofId R _,
    (Algebra.TensorProduct.includeRight : DualNumber k →ₐ[k] R ⊗[k] DualNumber k)
      DualNumber.eps), by
    constructor
    · rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
    · intro a
      change (Algebra.TensorProduct.includeRight (DualNumber.eps : DualNumber k) :
        R ⊗[k] DualNumber k) * algebraMap R _ a =
          algebraMap R _ a * Algebra.TensorProduct.includeRight DualNumber.eps
      exact mul_comm (Algebra.TensorProduct.includeRight
        (DualNumber.eps : DualNumber k) : R ⊗[k] DualNumber k)
          (algebraMap R (R ⊗[k] DualNumber k) a)⟩

@[simp]
lemma tensorTo_includeLeft (a : R) :
    tensorTo k R ((Algebra.TensorProduct.includeLeft :
      R →ₐ[R] R ⊗[k] DualNumber k) a) = TrivSqZeroExt.inl a := by
  simp [tensorTo]

@[simp]
lemma tensorTo_includeRight (z : DualNumber k) :
    tensorTo k R (Algebra.TensorProduct.includeRight z) =
      coefficientMap (algebraMap k R) z := by
  simp [tensorTo, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.lift_tmul, coefficientAlgMap]

@[simp]
lemma tensorFrom_eps : tensorFrom k R DualNumber.eps =
    Algebra.TensorProduct.includeRight (DualNumber.eps : DualNumber k) := by
  simp [tensorFrom]

lemma tensorTo_comp_tensorFrom :
    (tensorTo k R).comp (tensorFrom k R) = AlgHom.id R (DualNumber R) := by
  apply DualNumber.algHom_ext
  change tensorTo k R (tensorFrom k R DualNumber.eps) = DualNumber.eps
  rw [tensorFrom_eps, tensorTo_includeRight, coefficientMap_eps]

lemma tensorFrom_comp_tensorTo :
    (tensorFrom k R).comp (tensorTo k R) = AlgHom.id R (R ⊗[k] DualNumber k) := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro a
    change tensorFrom k R (tensorTo k R
      ((Algebra.TensorProduct.includeLeft : R →ₐ[R] R ⊗[k] DualNumber k) a)) =
        Algebra.TensorProduct.includeLeft a
    rw [tensorTo_includeLeft]
    simp [tensorFrom, Algebra.TensorProduct.algebraMap_apply]
  · apply DualNumber.algHom_ext
    change tensorFrom k R (tensorTo k R
      (Algebra.TensorProduct.includeRight (DualNumber.eps : DualNumber k))) =
        Algebra.TensorProduct.includeRight (DualNumber.eps : DualNumber k)
    rw [tensorTo_includeRight, coefficientMap_eps, tensorFrom_eps]

/-- Affine base change along the dual numbers is the split dual-number algebra. -/
def tensorEquiv : R ⊗[k] DualNumber k ≃ₐ[R] DualNumber R :=
  AlgEquiv.ofAlgHom (tensorTo k R) (tensorFrom k R)
    (tensorTo_comp_tensorFrom k R) (tensorFrom_comp_tensorTo k R)

@[simp]
lemma tensorTo_tmul (a : R) (z : DualNumber k) :
    tensorTo k R (a ⊗ₜ[k] z) =
      TrivSqZeroExt.inl a * coefficientMap (algebraMap k R) z := by
  simp [tensorTo, Algebra.TensorProduct.lift_tmul, coefficientAlgMap]

/-- Evaluation at epsilon zero on the actual tensor algebra. -/
def tensorAugmentation : R ⊗[k] DualNumber k →ₐ[R] R :=
  Algebra.TensorProduct.lift (AlgHom.id R R)
    ((Algebra.ofId k R).comp (TrivSqZeroExt.fstHom k k k))
    (fun _ _ ↦ Commute.all _ _)

lemma augmentation_comp_tensorTo :
    (TrivSqZeroExt.fstHom R R R).comp (tensorTo k R) =
      tensorAugmentation k R := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro a
    simp [tensorTo, tensorAugmentation]
  · apply AlgHom.ext
    intro z
    change (tensorTo k R (1 ⊗ₜ[k] z)).fst = tensorAugmentation k R (1 ⊗ₜ[k] z)
    rw [tensorTo_tmul]
    simp [tensorAugmentation, Algebra.TensorProduct.lift_tmul]

lemma tensorTo_scale (r : k) :
    (tensorTo k R).comp
        (Algebra.TensorProduct.map (AlgHom.id R R) (epsilonScale r)) =
      (epsilonScale (algebraMap k R r)).comp (tensorTo k R) := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro a
    change tensorTo k R (a ⊗ₜ[k] epsilonScale r 1) =
      epsilonScale (algebraMap k R r) (tensorTo k R (a ⊗ₜ[k] 1))
    simp only [map_one, tensorTo_tmul, mul_one]
    apply TrivSqZeroExt.ext <;>
      simp [epsilonScale]
  · apply AlgHom.ext
    intro z
    change tensorTo k R (1 ⊗ₜ[k] epsilonScale r z) =
      epsilonScale (algebraMap k R r) (tensorTo k R (1 ⊗ₜ[k] z))
    simp only [tensorTo_tmul, TrivSqZeroExt.inl_one, one_mul]
    apply TrivSqZeroExt.ext <;>
      simp only [coefficientMap_fst, coefficientMap_snd,
        epsilonScale_fst, epsilonScale_snd, map_mul]

variable {R} {S : Type u} [CommRing S] [Algebra k S]

lemma tensorTo_natural (f : R →ₐ[k] S) :
    (coefficientAlgMap (R := CommRingCat.of k) f).comp
        ((tensorTo k R).restrictScalars k) =
      ((tensorTo k S).restrictScalars k).comp
        (Algebra.TensorProduct.map f (AlgHom.id k (DualNumber k))) := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro a
    change coefficientMap f.toRingHom (tensorTo k R (a ⊗ₜ[k] 1)) =
      tensorTo k S (f a ⊗ₜ[k] 1)
    simp only [tensorTo_tmul, map_one, mul_one]
    apply TrivSqZeroExt.ext <;>
      simp only [coefficientMap_fst, coefficientMap_snd,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, map_zero]
    rfl
  · apply AlgHom.ext
    intro z
    change coefficientMap f.toRingHom (tensorTo k R (1 ⊗ₜ[k] z)) =
      tensorTo k S (f 1 ⊗ₜ[k] z)
    simp only [map_one, tensorTo_tmul, TrivSqZeroExt.inl_one, one_mul]
    apply TrivSqZeroExt.ext
    · exact f.commutes z.fst
    · exact f.commutes z.snd

variable (R)

/-- The actual affine fibre product with the base dual-number scheme. -/
noncomputable abbrev affineThickening :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))
    (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))

/-- The actual affine base change is the spectrum of the split dual-number ring. -/
noncomputable def affineIso :
    affineThickening k R ≅ Spec (CommRingCat.of (DualNumber R)) :=
  pullbackSpecIso k R (DualNumber k) ≪≫
    Scheme.Spec.mapIso (tensorEquiv k R).toRingEquiv.symm.toCommRingCatIso.op

@[reassoc (attr := simp)]
lemma affineIso_inv_fst :
    (affineIso k R).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) := by
  change Spec.map (CommRingCat.ofHom (tensorTo k R).toRingHom) ≫
    (pullbackSpecIso k R (DualNumber k)).inv ≫ pullback.fst _ _ = _
  rw [pullbackSpecIso_inv_fst, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact tensorTo_includeLeft k R a

@[reassoc (attr := simp)]
lemma affineIso_inv_snd :
    (affineIso k R).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (coefficientMap (algebraMap k R))) := by
  change Spec.map (CommRingCat.ofHom (tensorTo k R).toRingHom) ≫
    (pullbackSpecIso k R (DualNumber k)).inv ≫ pullback.snd _ _ = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact tensorTo_includeRight k R z

/-- The actual zero section of the affine base change, constructed by its limit property. -/
noncomputable def affineClosedPoint :
    Spec (CommRingCat.of R) ⟶ affineThickening k R :=
  pullback.lift (𝟙 _)
    (Spec.map (CommRingCat.ofHom
      ((Algebra.ofId k R).comp (TrivSqZeroExt.fstHom k k k)).toRingHom)) (by
    rw [Category.id_comp, ← Spec.map_comp]
    congr 1)

lemma affineClosedPoint_eq :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
      (affineIso k R).inv = affineClosedPoint k R := by
  apply pullback.hom_ext
  · rw [Category.assoc, affineIso_inv_fst]
    change _ = pullback.lift _ _ _ ≫ pullback.fst _ _
    rw [pullback.lift_fst, ← Spec.map_comp, ← Spec.map_id]
    congr 1
  · rw [Category.assoc, affineIso_inv_snd]
    change _ = pullback.lift _ _ _ ≫ pullback.snd _ _
    rw [pullback.lift_snd, ← Spec.map_comp]
    congr 1

@[reassoc (attr := simp)]
lemma affineClosedPoint_comp_affineIso :
    affineClosedPoint k R ≫ (affineIso k R).hom =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  rw [← affineClosedPoint_eq, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Base change of the actual epsilon-scaling endomorphism of the test scheme. -/
noncomputable def affineScale (r : k) :
    affineThickening k R ⟶ affineThickening k R :=
  pullback.map _ _ _ _ (𝟙 _)
    (Spec.map (CommRingCat.ofHom (epsilonScale r).toRingHom)) (𝟙 _) (by simp) (by
      rw [Category.comp_id, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact ((epsilonScale r).commutes a).symm)

lemma affineIso_inv_scale (r : k) :
    (affineIso k R).inv ≫ affineScale k R r =
      Spec.map (CommRingCat.ofHom (epsilonScale (algebraMap k R r)).toRingHom) ≫
        (affineIso k R).inv := by
  apply pullback.hom_ext
  · simp only [Category.assoc, affineScale, pullback.lift_fst, Category.comp_id,
      affineIso_inv_fst]
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact ((epsilonScale (algebraMap k R r)).commutes a).symm
  · simp only [Category.assoc, affineScale, pullback.lift_snd,
      affineIso_inv_snd_assoc, affineIso_inv_snd]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change coefficientMap (algebraMap k R) (epsilonScale r z) =
      epsilonScale (algebraMap k R r) (coefficientMap (algebraMap k R) z)
    apply TrivSqZeroExt.ext <;>
      simp only [coefficientMap_fst, coefficientMap_snd, epsilonScale_fst,
        epsilonScale_snd, map_mul]

variable {R}

/-- The actual base-changed scheme morphism induced by a coefficient algebra map. -/
noncomputable def affineMap (f : R →ₐ[k] S) :
    affineThickening k S ⟶ affineThickening k R :=
  pullback.map _ _ _ _ (Spec.map (CommRingCat.ofHom f.toRingHom)) (𝟙 _) (𝟙 _)
    (by
      rw [Category.comp_id, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact (f.commutes a).symm) (by simp)

lemma affineIso_inv_natural (f : R →ₐ[k] S) :
    (affineIso k S).inv ≫ affineMap k f =
      Spec.map (CommRingCat.ofHom (coefficientMap f.toRingHom)) ≫
        (affineIso k R).inv := by
  apply pullback.hom_ext
  · simp only [Category.assoc, affineMap, pullback.lift_fst,
      affineIso_inv_fst_assoc, affineIso_inv_fst]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change TrivSqZeroExt.inl (f a) = coefficientMap f.toRingHom (TrivSqZeroExt.inl a)
    apply TrivSqZeroExt.ext
    · rfl
    · exact (map_zero f).symm
  · simp only [Category.assoc, affineMap, pullback.lift_snd, Category.comp_id,
      affineIso_inv_snd]
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change coefficientMap (algebraMap k S) z =
      coefficientMap f.toRingHom (coefficientMap (algebraMap k R) z)
    apply TrivSqZeroExt.ext
    · exact (f.commutes z.fst).symm
    · exact (f.commutes z.snd).symm

end Langlands.AlgebraicGeometry.Picard.DualNumberBaseChange
