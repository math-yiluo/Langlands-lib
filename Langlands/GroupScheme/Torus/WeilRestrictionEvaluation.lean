import Langlands.GroupScheme.Torus.WeilRestrictionBaseChange

/-! # Evaluation of Weil-restriction points over the coefficient ring -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.WeilGm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Algebra

variable (A B R : Type u) [CommRing A] [CommRing B] [CommRing R]
  [Algebra A B] [Algebra A R] [Algebra B R] [IsScalarTower A B R]

/-- Multiply the coefficient factor into an algebra over `B`. -/
def evaluationCoefficient : B ⊗[A] R →ₐ[B] R :=
  (AlgHom.liftEquiv A B R R) (AlgHom.id A R)

@[simp] theorem evaluationCoefficient_tmul (b : B) (r : R) :
    evaluationCoefficient A B R (b ⊗ₜ[A] r) = algebraMap B R b * r := by
  simp [evaluationCoefficient, Algebra.smul_def]

theorem evaluationCoefficient_naturality
    {R' : Type u} [CommRing R'] [Algebra A R'] [Algebra B R'] [IsScalarTower A B R']
    (φ : R →ₐ[B] R') (ψ : R →ₐ[A] R') (h : ∀ r, ψ r = φ r) (w : B ⊗[A] R) :
    evaluationCoefficient A B R' (Algebra.TensorProduct.lTensor (S := B) B ψ w) =
      φ (evaluationCoefficient A B R w) := by
  induction w using TensorProduct.inductionOn with
  | tmul b r => simp [h]
  | add w w' hw hw' => simp only [map_add, hw, hw']

end Algebra

variable (A B : CommRingCat.{u}) [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

/-- Evaluate a Weil-restriction point on a `B`-test as a global unit. -/
def evaluationUnits (T : Over (Spec B)) :
    (((Over.map (baseMap A B)).obj T) ⟶ (groupScheme A B).X) →* Γ(T.left, ⊤)ˣ :=
  (Units.map (evaluationCoefficient A B (restrictedSections A B T)).toMonoidHom).comp
    (pointsEquiv A B ((Over.map (baseMap A B)).obj T)).toMonoidHom

/-- Scalar evaluation commutes with every morphism of tests over `Spec B`. -/
theorem evaluationUnits_naturality {T T' : Over (Spec B)} (a : T' ⟶ T)
    (x : (Over.map (baseMap A B)).obj T ⟶ (groupScheme A B).X) :
    evaluationUnits A B T' ((Over.map (baseMap A B)).map a ≫ x) =
      Units.map a.left.appTop.hom.toMonoidHom (evaluationUnits A B T x) := by
  change Units.map _ (pointsEquiv A B _ _) = _
  rw [pointsEquiv_naturality]
  apply Units.ext
  exact evaluationCoefficient_naturality A B (restrictedSections A B T)
    (R' := restrictedSections A B T')
    ((algΓ B).map a).unop.hom
    ((algΓ A).map ((Over.map (baseMap A B)).map a)).unop.hom
    (fun _ => rfl) _

end Langlands.GroupScheme.WeilGm
