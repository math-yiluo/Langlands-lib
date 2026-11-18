import Langlands.GroupScheme.AffinePointBaseChangeSmooth
import Langlands.GroupScheme.Lie.NonaffineKernel
import Langlands.GroupScheme.Lie.AffineCoordinates
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Base changes detected by the reduction of a generic point

Let `H` be a group scheme over `Spec R` presented by an affine algebra `D`, and let `I` be an
ideal of `R`. A morphism `s : H.X ⟶ G.X` over `Spec R` becomes the identity after base change to
`R ⧸ I` as soon as the reduction of the generic point `Spec D ⟶ H.X ⟶ G.X` modulo `I D` is the
identity point, because `Spec (D ⧸ I D)` is the base change of `Spec D` to `R ⧸ I`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomScheme

/-- The reduction modulo an extended ideal is the base change along `R → R ⧸ I`. -/
theorem quotient_isPushout {R : Type u} [CommRing R] (I : Ideal R) (D : Type u) [CommRing D]
    [Algebra R D] : Algebra.IsPushout R D (R ⧸ I) (D ⧸ I.map (algebraMap R D)) := by
  refine ⟨IsBaseChange.of_equiv
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot D I).symm.toLinearEquiv fun x => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot D I).symm
      ((1 : D) ⊗ₜ[R] Ideal.Quotient.mk I a) = algebraMap (R ⧸ I) _ (Ideal.Quotient.mk I a)
  rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
  change Submodule.Quotient.mk (a • (1 : D)) = _
  rw [Algebra.smul_def, mul_one]
  rfl

variable {R : CommRingCat.{u}} (I : Ideal R) {H G : GroupScheme (Spec R)}
  {D : CommAlgCat.{u} R} (e : (algSpec R).obj (op D) ≅ H.X)

/-- The spectrum of the reduction `D ⧸ I D` of an affine presentation is the base change of `H`
to `R ⧸ I`. -/
theorem isPullback_reduction :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap D (D ⧸ I.map (algebraMap R D)))) ≫ e.hom.left)
      (Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ I) (D ⧸ I.map (algebraMap R D)))))
      H.X.hom (Spec.algebraMap R (R ⧸ I)) := by
  have := quotient_isPushout I D
  have h := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R D (R ⧸ I) (D ⧸ I.map (algebraMap R D)))
  refine h.of_iso (Iso.refl _) ((Over.forget _).mapIso e) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Over.w e.hom).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **Base changes detected by a generic reduction.** If reducing the presenting point
`Spec D ≅ H.X ⟶ G.X` modulo `I D` gives the identity point, then `s` base-changes to the identity
morphism over `R ⧸ I`. No hypothesis on `G`, `I` or `s` is needed. -/
theorem baseChange_eq_one_of_reduction (s : H.X ⟶ G.X)
    (hs : Lie.NonaffineKernel.reduction G (I.map (algebraMap R D)) (e.hom ≫ s) = 1) :
    (Over.pullback (Spec.algebraMap R (R ⧸ I))).map s =
      (1 : (Over.pullback (Spec.algebraMap R (R ⧸ I))).obj H.X ⟶
        ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).obj G).X) := by
  have hP := isPullback_reduction I e
  let P₀ : (algSpec (CommRingCat.of (R ⧸ I))).obj
      (op (CommAlgCat.of (R ⧸ I) (D ⧸ I.map (algebraMap R D)))) ⟶
        (Over.pullback (Spec.algebraMap R (R ⧸ I))).obj H.X :=
    Over.homMk hP.isoPullback.hom hP.isoPullback_hom_snd
  have key1 : (P₀ ≫ (Over.pullback (Spec.algebraMap R (R ⧸ I))).map s :
      ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).obj G).affinePoints
        (CommAlgCat.of (R ⧸ I) (D ⧸ I.map (algebraMap R D)))) = 1 := by
    apply (affinePointsBaseChangeMulEquiv R (R ⧸ I) (D ⧸ I.map (algebraMap R D))
      G).symm.injective
    rw [map_one]
    apply Over.OverMorphism.ext
    rw [affinePointsBaseChangeMulEquiv_symm_left]
    have h1 : (P₀ ≫ (Over.pullback (Spec.algebraMap R (R ⧸ I))).map s).left ≫
        pullback.fst G.X.hom (Spec.algebraMap R (R ⧸ I)) =
          (Spec.map (CommRingCat.ofHom (algebraMap D (D ⧸ I.map (algebraMap R D)))) ≫
            e.hom.left) ≫ s.left := by
      change (hP.isoPullback.hom ≫ pullback.lift (pullback.fst _ _ ≫ s.left)
        (pullback.snd _ _) _) ≫ pullback.fst _ _ = _
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hP.isoPullback_hom_fst]
    exact h1.trans ((Category.assoc _ _ _).trans (congrArg Over.Hom.left hs))
  have key2 : P₀ ≫ (1 : (Over.pullback (Spec.algebraMap R (R ⧸ I))).obj H.X ⟶
      ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).obj G).X) = 1 :=
    MonObj.comp_one P₀
  apply Over.OverMorphism.ext
  rw [← cancel_epi hP.isoPullback.hom]
  exact congrArg Over.Hom.left (key1.trans key2.symm)

/-- The generic-point version for affine `H` with its chosen coordinates. -/
theorem baseChange_eq_one_of_generic_reduction [IsAffineHom H.X.hom] (s : H.X ⟶ G.X)
    (hs : Lie.NonaffineKernel.reduction G (I.map (algebraMap R (Lie.coordinateAlgebra H)))
      ((Lie.pointCoordinates H).symm (AlgHom.id R (Lie.coordinateAlgebra H)) ≫ s) = 1) :
    (Over.pullback (Spec.algebraMap R (R ⧸ I))).map s =
      (1 : (Over.pullback (Spec.algebraMap R (R ⧸ I))).obj H.X ⟶
        ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).obj G).X) := by
  have hg : (Lie.pointCoordinates H).symm (AlgHom.id R (Lie.coordinateAlgebra H)) =
      (Lie.coordinateIso H).hom := by
    change (algSpec R).map
      (CommAlgCat.ofHom (AlgHom.id R (Lie.coordinateAlgebra H))).op ≫ _ = _
    rw [show CommAlgCat.ofHom (AlgHom.id R (Lie.coordinateAlgebra H)) = 𝟙 _ from rfl, op_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hg] at hs
  exact baseChange_eq_one_of_reduction I (Lie.coordinateIso H) s hs

end Langlands.GroupScheme.HomScheme
