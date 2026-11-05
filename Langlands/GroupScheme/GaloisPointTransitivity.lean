import Langlands.GroupScheme.GaloisPointTower
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.Data.Fintype.BigOperators

/-! # Transitivity of the coefficient-point norm -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.GaloisPoint

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  [Normal k L] [Normal k M]

omit [Normal k M] in
@[simp] theorem restrictNormal_relativeAut (σ : M ≃ₐ[L] M) :
    (σ.restrictScalars k).restrictNormal L = 1 := by
  ext x
  apply (algebraMap L M).injective
  rw [AlgEquiv.restrictNormal_commutes]
  exact σ.commutes x

private theorem restrictNormal_lift_mul (τ : L ≃ₐ[k] L) (σ : M ≃ₐ[L] M) :
    (τ.liftNormal M * σ.restrictScalars k).restrictNormal L = τ := by
  change (AlgEquiv.restrictNormalHom L) (τ.liftNormal M * σ.restrictScalars k) = τ
  rw [map_mul]
  change (τ.liftNormal M).restrictNormal L * (σ.restrictScalars k).restrictNormal L = τ
  rw [AlgEquiv.restrict_liftNormal, restrictNormal_relativeAut, mul_one]

private theorem towerAutMap_bijective :
    Function.Bijective (fun p : (L ≃ₐ[k] L) × (M ≃ₐ[L] M) =>
      p.1.liftNormal M * p.2.restrictScalars k) := by
  constructor
  · rintro ⟨τ, σ⟩ ⟨τ', σ'⟩ h
    have hτ : τ = τ' := by
      simpa only [restrictNormal_lift_mul] using
        congrArg (fun θ : M ≃ₐ[k] M => θ.restrictNormal L) h
    subst τ'
    have hσ : σ = σ' :=
      AlgEquiv.restrictScalars_injective k (mul_left_cancel h)
    subst σ'
    rfl
  · intro θ
    let τ := θ.restrictNormal L
    let δ : M ≃ₐ[k] M := (τ.liftNormal M)⁻¹ * θ
    have hδ : δ.restrictNormal L = 1 := by
      change (AlgEquiv.restrictNormalHom L) ((τ.liftNormal M)⁻¹ * θ) = 1
      rw [map_mul, map_inv]
      change ((τ.liftNormal M).restrictNormal L)⁻¹ * θ.restrictNormal L = 1
      rw [AlgEquiv.restrict_liftNormal]
      exact inv_mul_cancel τ
    let σ : M ≃ₐ[L] M :=
      { δ.toRingEquiv with
        commutes' := fun x => by
          change δ (algebraMap L M x) = algebraMap L M x
          rw [← δ.restrictNormal_commutes L x, hδ]
          rfl }
    refine ⟨(τ, σ), ?_⟩
    have hσ : σ.restrictScalars k = δ := by ext; rfl
    change τ.liftNormal M * σ.restrictScalars k = θ
    rw [hσ]
    exact mul_inv_cancel_left _ _

/-- A lift of a quotient automorphism followed by a relative automorphism
parametrizes each automorphism of the larger normal extension exactly once. -/
def towerAutEquiv : ((L ≃ₐ[k] L) × (M ≃ₐ[L] M)) ≃ (M ≃ₐ[k] M) :=
  Equiv.ofBijective _ (towerAutMap_bijective k L M)

@[simp] theorem towerAutEquiv_apply (τ : L ≃ₐ[k] L) (σ : M ≃ₐ[L] M) :
    towerAutEquiv k L M (τ, σ) = τ.liftNormal M * σ.restrictScalars k := rfl

variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

omit [Normal k L] [Normal k M] in
@[simp] theorem relativeExtend_extend (x : G.affinePoints (CommAlgCat.of k k)) :
    relativeExtend k L M G (extend k L G x) = extend k M G x := by
  apply (coordinates k G M).injective
  ext a
  simp only [coordinates_relativeExtend, coordinates_extend]
  exact (IsScalarTower.algebraMap_apply k L M _).symm

omit [Normal k M] in
theorem relativeExtend_conjugate (σ : M ≃ₐ[k] M)
    (x : G.affinePoints (CommAlgCat.of k L)) :
    relativeExtend k L M G (conjugate k L G (σ.restrictNormal L) x) =
      conjugate k M G σ (relativeExtend k L M G x) := by
  apply (coordinates k G M).injective
  ext a
  simp only [coordinates_relativeExtend, coordinates_conjugate]
  exact σ.restrictNormal_commutes L _

theorem relativeExtend_conjugate_lift (τ : L ≃ₐ[k] L)
    (x : G.affinePoints (CommAlgCat.of k L)) :
    relativeExtend k L M G (conjugate k L G τ x) =
      conjugate k M G (τ.liftNormal M) (relativeExtend k L M G x) := by
  simpa only [AlgEquiv.restrict_liftNormal] using
    relativeExtend_conjugate k L M G (τ.liftNormal M) x

variable [FiniteDimensional k L] [FiniteDimensional k M] [FiniteDimensional L M]
  [IsGalois k L] [IsGalois k M] [IsGalois L M]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

/-- Norms in a finite-Galois tower compose on the original coefficient points. -/
theorem norm_relativeNorm (x : affinePoints T.toGrp (CommAlgCat.of k M)) :
    norm k L T (relativeNorm k L M T x) = norm k M T x := by
  apply extend_injective k M T.toGrp
  calc
    extend k M T.toGrp (norm k L T (relativeNorm k L M T x)) =
        relativeExtend k L M T.toGrp
          (extend k L T.toGrp (norm k L T (relativeNorm k L M T x))) :=
      (relativeExtend_extend k L M T.toGrp _).symm
    _ = ∏ τ : L ≃ₐ[k] L,
        conjugate k M T.toGrp (τ.liftNormal M)
          (relativeExtend k L M T.toGrp (relativeNorm k L M T x)) := by
      rw [extend_norm, map_prod]
      exact Finset.prod_congr rfl (fun τ _ =>
        relativeExtend_conjugate_lift k L M T.toGrp τ _)
    _ = ∏ τ : L ≃ₐ[k] L, ∏ σ : M ≃ₐ[L] M,
        conjugate k M T.toGrp (τ.liftNormal M * σ.restrictScalars k) x := by
      simp only [relativeExtend_norm, map_prod, relativeConjugate, conjugate_mul]
    _ = ∏ θ : M ≃ₐ[k] M, conjugate k M T.toGrp θ x := by
      simpa only [Fintype.prod_prod_type, towerAutEquiv_apply] using
        (towerAutEquiv k L M).prod_comp (fun θ => conjugate k M T.toGrp θ x)
    _ = extend k M T.toGrp (norm k M T x) := (extend_norm k M T x).symm

end Langlands.GroupScheme.GaloisPoint
