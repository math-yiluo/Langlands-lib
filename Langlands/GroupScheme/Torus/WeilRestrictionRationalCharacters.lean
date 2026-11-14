import Langlands.GroupScheme.Torus.WeilRestrictionSeparable
import Langlands.GroupScheme.Torus.WeilRestrictionGaloisPoints
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # Rational evaluation of embedding characters of Weil restriction -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open Langlands.Algebra.SeparableTensor
open Langlands.GroupScheme.GaloisPointComparison
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.WeilGm

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

variable (k K Ω : Type u) [Field k] [Field K] [Field Ω]
  [Algebra k K] [Algebra k Ω] [FiniteDimensional k K]
  (h : Function.Bijective (embeddingEvaluation k K Ω))

/-- The extended rational point with prescribed unit coordinate. -/
def extendedUnitPoint :
    Kˣ →* rationalPoints (baseChanged k Ω (groupScheme (CommRingCat.of k) K)) :=
  (rationalExtend k Ω (groupScheme (CommRingCat.of k) K)).comp
    (rationalUnitsEquiv k K).symm.toMonoidHom

@[simp] theorem extendedUnitPoint_apply (t : Kˣ) :
    extendedUnitPoint k K Ω t =
      rationalExtend k Ω (groupScheme (CommRingCat.of k) K)
        ((rationalUnitsEquiv k K).symm t) := rfl

/-- The identity-test and affine-test conventions have the same global tensor unit. -/
theorem pointsEquiv_rationalBaseChange
    (x : rationalPoints (baseChanged k Ω (groupScheme (CommRingCat.of k) K))) :
    pointsEquiv (CommRingCat.of k) K
        ((Over.map (algebraBaseMap k Ω)).obj
          (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))))
        (GroupScheme.baseChangePointsEquiv (algebraBaseMap k Ω)
          (groupScheme (CommRingCat.of k) K) _ x) =
      pointsEquiv (CommRingCat.of k) K
        ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k Ω)))
        (baseChangeCoeffEquiv k Ω (groupScheme (CommRingCat.of k) K) x) := by
  let T := ((Over.map (algebraBaseMap k Ω)).obj
    (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))))
  let S := CommAlgCat.of k Ω
  let e : (algSpec (CommRingCat.of k)).obj (op S) ⟶ T :=
    Over.homMk (𝟙 _) (by simp [T, S, algebraBaseMap])
  have he : e ≫ GroupScheme.baseChangePointsEquiv (algebraBaseMap k Ω)
      (groupScheme (CommRingCat.of k) K) _ x =
      baseChangeCoeffEquiv k Ω (groupScheme (CommRingCat.of k) K) x := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, e, Over.homMk_left,
      GroupScheme.baseChangePointsEquiv_left, baseChangeCoeffEquiv_left, Category.id_comp]
  have hp := pointsEquiv_naturality (CommRingCat.of k) K e
    (GroupScheme.baseChangePointsEquiv (algebraBaseMap k Ω)
      (groupScheme (CommRingCat.of k) K) _ x)
  rw [he] at hp
  apply Units.ext
  have hpv := congrArg Units.val hp
  change _ = Algebra.TensorProduct.lTensor (S := K) K
    (AlgHom.id (CommRingCat.of k) _) _ at hpv
  rw [Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map_id] at hpv
  exact hpv.symm

omit [FiniteDimensional k K] in
/-- Evaluation of tensor units commutes with the affine global-section comparison. -/
theorem tensorCoordinate_affineSections (τ : K →ₐ[k] Ω) (y : K ⊗[k] Ω) :
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom
      (tensorCoordinate (embeddingCoefficientMap k Ω
        (Over.mk (𝟙 (Spec (CommRingCat.of Ω))))) τ
        (Algebra.TensorProduct.lTensor (R := k) (S := K) K
          (Corepresented.affineSectionsIso (R := CommRingCat.of k) (CommAlgCat.of k Ω)).inv.hom y)) =
      tensorCoordinate (AlgHom.id k Ω) τ y := by
  induction y using TensorProduct.inductionOn with
  | tmul a b =>
      simp only [Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, tensorCoordinate_tmul, map_mul]
      change (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom
          ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv (τ a)) *
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom
          ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv b) = τ a * b
      simp
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb

/-- Affine embedding coordinates evaluate the tensor unit in the chosen embedding. -/
theorem embeddingPointsEquiv_rational
    (x : rationalPoints (baseChanged k Ω (groupScheme (CommRingCat.of k) K)))
    (τ : K →ₐ[k] Ω) :
    Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.toMonoidHom
        (embeddingPointsEquiv k K Ω h (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) x τ) =
      Units.map (tensorCoordinate (AlgHom.id k Ω) τ).toMonoidHom
        (extensionUnitsEquiv k Ω K x) := by
  rw [embeddingPointsEquiv_apply, pointsEquiv_rationalBaseChange]
  erw [Corepresented.pointsEquiv_eq_affinePointsEquiv]
  apply Units.ext
  exact tensorCoordinate_affineSections k K Ω τ (extensionUnitsEquiv k Ω K x)

/-- Extending a rational Weil-restriction point gives its embedded unit in each coordinate. -/
theorem embeddingPointsEquiv_rationalExtend
    (x : rationalPoints (groupScheme (CommRingCat.of k) K)) (τ : K →ₐ[k] Ω) :
    Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.toMonoidHom
        (embeddingPointsEquiv k K Ω h (Over.mk (𝟙 (Spec (CommRingCat.of Ω))))
          (rationalExtend k Ω (groupScheme (CommRingCat.of k) K) x) τ) =
      Units.map τ.toMonoidHom (rationalUnitsEquiv k K x) := by
  rw [embeddingPointsEquiv_rational, extensionUnitsEquiv_extend]
  apply Units.ext
  simp [tensorCoordinate]

/-- Every actual character evaluates on an extended rational point as the embedding monomial. -/
theorem rationalCharacterEval_extend_eq_prod [Fintype (K →ₐ[k] Ω)]
    (χ : rationalCharacters (baseChanged k Ω (groupScheme (CommRingCat.of k) K)))
    (x : rationalPoints (groupScheme (CommRingCat.of k) K)) :
    rationalCharacterEval χ (rationalExtend k Ω (groupScheme (CommRingCat.of k) K) x) =
      ∏ τ, Units.map τ.toMonoidHom (rationalUnitsEquiv k K x) ^
        embeddingCharacterEquiv k K Ω h χ τ := by
  let m := embeddingCharacterEquiv k K Ω h χ
  have hc := embeddingCharacterEquiv_symm_points k K Ω h m
    (Over.mk (𝟙 (Spec (CommRingCat.of Ω))))
    (rationalExtend k Ω (groupScheme (CommRingCat.of k) K) x)
  rw [AddEquiv.symm_apply_apply] at hc
  change Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.toMonoidHom
    (Gm.pointsEquiv (Spec (CommRingCat.of Ω))
      (Over.mk (𝟙 (Spec (CommRingCat.of Ω))))
      (rationalExtend k Ω (groupScheme (CommRingCat.of k) K) x ≫ χ.toMul.hom.hom)) = _
  erw [hc, map_prod]
  apply Finset.prod_congr rfl
  intro τ _
  rw [map_zpow, embeddingPointsEquiv_rationalExtend]

/-- Every character of a unit-coordinate point is its embedding monomial. -/
theorem rationalCharacterEval_extendedUnitPoint_eq_prod [Fintype (K →ₐ[k] Ω)]
    (χ : rationalCharacters (baseChanged k Ω (groupScheme (CommRingCat.of k) K)))
    (t : Kˣ) :
    rationalCharacterEval χ (extendedUnitPoint k K Ω t) =
      ∏ τ, Units.map τ.toMonoidHom t ^ embeddingCharacterEquiv k K Ω h χ τ := by
  simpa only [extendedUnitPoint_apply, MulEquiv.apply_symm_apply] using
    rationalCharacterEval_extend_eq_prod k K Ω h χ ((rationalUnitsEquiv k K).symm t)

end Langlands.GroupScheme.WeilGm
