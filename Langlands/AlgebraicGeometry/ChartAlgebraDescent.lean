import Langlands.AlgebraicGeometry.ChartAlgebraInvariants

/-! # Effective finite étale algebra descent from functorial chart transitions -/

noncomputable section
universe u
open CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.ChartAlgebraDescent

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C]

/-- An actual descended finite projective étale algebra, with invariant chart recovery. -/
structure Descended (D : Datum A B C) where
  ring : Type u
  [commRing : CommRing ring]
  [algebra : Algebra A ring]
  [finite : Module.Finite A ring]
  [projective : Module.Projective A ring]
  [etale : Algebra.Etale A ring]
  equiv : B ⊗[A] ring ≃ₐ[B] C
  invariant : ∀ (T : CommAlgCat.{u} (CommRingCat.of A)) (f₁ f₂ : B →ₐ[A] T) (b : ring),
    D.equiv T f₁ f₂
        (letI := f₂.toRingHom.toAlgebra; (1 : T) ⊗ₜ[B] equiv (1 ⊗ₜ[A] b)) =
      (letI := f₁.toRingHom.toAlgebra; (1 : T) ⊗ₜ[B] equiv (1 ⊗ₜ[A] b))

attribute [instance] Descended.commRing Descended.algebra Descended.finite
  Descended.projective Descended.etale

omit [Algebra A B] [Algebra B C] in
/-- Effective invariant-algebra descent with normalized ring-map scalar structures. -/
def descendOfRingHom (φ : A →+* B) (F : B →+* C)
    (hφ : φ.FaithfullyFlat) (hfin : F.Finite) (het : F.Etale) :
    letI := φ.toAlgebra
    letI := F.toAlgebra
    ∀ D : Datum A B C, Descended D := by
  letI := φ.toAlgebra
  letI := F.toAlgebra
  letI := (F.comp φ).toAlgebra
  letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  intro D
  let a := D.coaction
  refine {
    ring := a.invariants
    commRing := inferInstance
    algebra := inferInstance
    finite := a.finite_invariants hφ hfin
    projective := a.projective_invariants hφ hfin het
    etale := a.etale_invariants hφ het
    equiv := a.descentEquiv hφ
    invariant := ?_ }
  intro T f₁ f₂ b
  have hb : a.map (b : C) = (1 : B) ⊗ₜ[A] (b : C) := b.property
  rw [Datum.coaction_map_apply φ F D] at hb
  simpa only [FaithfullyFlatAlgebraDescent.Coaction.descentEquiv_tmul, map_one, one_mul] using
    D.equiv_tmul_of_coactionMap_eq (b : C) hb T f₁ f₂

namespace Datum

/-- Construct the actual descended algebra from the functorial chart datum. -/
def descend (D : Datum A B C) (hφ : (algebraMap A B).FaithfullyFlat)
    (hfin : (algebraMap B C).Finite) (het : (algebraMap B C).Etale) : Descended D := by
  let φ := algebraMap A B
  let F := algebraMap B C
  have hφalg : φ.toAlgebra = (inferInstance : Algebra A B) := toAlgebra_algebraMap
  have hFalg : F.toAlgebra = (inferInstance : Algebra B C) := toAlgebra_algebraMap
  have h := descendOfRingHom φ F hφ hfin het
  change (∀ E : @Datum A B C _ _ _ φ.toAlgebra F.toAlgebra,
    @Descended A B C _ _ _ φ.toAlgebra F.toAlgebra E) at h
  rw [hφalg, hFalg] at h
  exact h D

end Datum
end Langlands.AlgebraicGeometry.ChartAlgebraDescent
