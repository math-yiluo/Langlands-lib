import Langlands.GroupScheme.SimplyConnected.SpecialLinearTitsCocycleStatement

/-! # All-test algebra of the special-linear Galois discrepancy -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinearTitsCocycle

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

@[simp] theorem coverAut_one :
    coverAut K L (1 : L ≃ₐ[K] L) = 𝟙 (cover K L) := by
  apply Over.OverMorphism.ext
  exact galoisBaseMap_one K L

theorem coverAut_mul (σ τ : L ≃ₐ[K] L) :
    coverAut K L (σ * τ) = coverAut K L σ ≫ coverAut K L τ := by
  apply Over.OverMorphism.ext
  exact galoisBaseMap_mul K L σ τ

/-- Pulling back a cover point pulls back its coefficient homomorphism. -/
theorem coefficients_naturality {Z W : Over (Spec (CommRingCat.of K))}
    (t : W ⟶ Z) (a : Z ⟶ cover K L) :
    coefficients (t ≫ a) = t.left.appTop.hom.comp (coefficients a) := by
  ext x
  simp [coefficients]
  rfl

/-- Changing the cover point by `Spec σ` precomposes its coefficients by `σ`. -/
theorem coefficients_coverAut {Z : Over (Spec (CommRingCat.of K))}
    (a : Z ⟶ cover K L) (σ : L ≃ₐ[K] L) :
    coefficients (a ≫ coverAut K L σ) = (coefficients a).comp σ.toRingHom := by
  change (((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫
      (galoisBaseMap K L σ).appTop ≫ a.left.appTop).hom) = _
  unfold galoisBaseMap
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  rfl

variable {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
    (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
      (cover K L))

/-- The discrepancy is a group automorphism of determinant-one matrices over
the global sections of each test scheme. -/
def discrepancyAut (σ : L ≃ₐ[K] L) {Z : Over (Spec (CommRingCat.of K))}
    (a : Z ⟶ cover K L) :
    Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤) ≃*
      Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤) :=
  (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).symm.trans
    ((E.toFun (a ≫ coverAut K L σ)).trans
      ((E.toFun a).symm.trans
        (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z)))

@[simp] theorem discrepancyAut_apply (σ : L ≃ₐ[K] L)
    {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K L)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
    discrepancyAut E σ a g = discrepancy E σ a g := rfl

/-- The identity Galois element has identity discrepancy on every test. -/
@[simp] theorem discrepancy_one {Z : Over (Spec (CommRingCat.of K))}
    (a : Z ⟶ cover K L)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
    discrepancy E 1 a g = g := by
  simp only [discrepancy, coverAut_one, Category.comp_id,
    MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

/-- Discrepancies compose in the order fixed by `Spec (σ * τ) = Spec σ ≫ Spec τ`. -/
theorem discrepancy_mul (σ τ : L ≃ₐ[K] L)
    {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K L)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
    discrepancy E (σ * τ) a g =
      discrepancy E σ a (discrepancy E τ (a ≫ coverAut K L σ) g) := by
  simp only [discrepancy, coverAut_mul, Category.assoc,
    MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]

/-- The discrepancy at a pulled-back test is the coefficientwise pullback of
the original discrepancy. -/
theorem discrepancy_naturality (σ : L ≃ₐ[K] L)
    {Z W : Over (Spec (CommRingCat.of K))} (t : W ⟶ Z) (a : Z ⟶ cover K L)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
    discrepancy E σ (t ≫ a) (Matrix.SpecialLinearGroup.map t.left.appTop.hom g) =
      Matrix.SpecialLinearGroup.map t.left.appTop.hom (discrepancy E σ a g) := by
  have hg :
      (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) W).symm
          (Matrix.SpecialLinearGroup.map t.left.appTop.hom g) =
        t ≫ (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).symm g := by
    apply (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) W).injective
    rw [MulEquiv.apply_symm_apply, SpecialLinear.pointsEquiv_naturality,
      MulEquiv.apply_symm_apply]
  unfold discrepancy
  rw [hg, Category.assoc, E.naturality]
  have hE :
      (E.toFun (t ≫ a)).symm (t ≫ E.toFun (a ≫ coverAut K L σ)
          ((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).symm g)) =
        t ≫ (E.toFun a).symm (E.toFun (a ≫ coverAut K L σ)
          ((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).symm g)) :=
    E.symm.naturality t a _
  rw [hE, SpecialLinear.pointsEquiv_naturality]

end Langlands.GroupScheme.SpecialLinearTitsCocycle
