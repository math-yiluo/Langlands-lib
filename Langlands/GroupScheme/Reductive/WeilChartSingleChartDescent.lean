import Langlands.GroupScheme.Reductive.WeilChartFactorCover
import Langlands.GroupScheme.Reductive.AffineWeilPairEtaleDescentReduction

/-! # Descent of Weil-restriction presentations along one étale cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Langlands.GroupScheme.WeilChart

variable {A A' C B : Type u} [CommRing A] [CommRing A'] [CommRing C] [CommRing B]
  [Algebra A A'] [Algebra A' C] [Algebra A B]

/-- The `B`-algebra structure on `C ≃ A' ⊗[A] B`, `b ↦ e (1 ⊗ b)`. -/
abbrev coverAlgebra (e : A' ⊗[A] B ≃ₐ[A'] C) : Algebra B C :=
  ((e : A' ⊗[A] B →+* C).comp
    (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := B)).toRingHom).toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- `e` as an isomorphism of `B`-algebras. -/
def coverAlgEquiv (e : A' ⊗[A] B ≃ₐ[A'] C) :
    letI := coverAlgebra e
    A' ⊗[A] B ≃ₐ[B] C :=
  letI := coverAlgebra e
  { e.toRingEquiv with commutes' := fun _ => rfl }

theorem coverAlgebra_etale [Algebra.Etale A A'] (e : A' ⊗[A] B ≃ₐ[A'] C) :
    letI := coverAlgebra e
    Algebra.Etale B C := by
  letI := coverAlgebra e
  letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  haveI : Algebra.Etale B (A' ⊗[A] B) := etale_tensor_right A A' B
  exact Algebra.Etale.of_equiv (coverAlgEquiv e)

theorem coverAlgebra_faithfullyFlat [Module.FaithfullyFlat A A'] (e : A' ⊗[A] B ≃ₐ[A'] C) :
    letI := coverAlgebra e
    Module.FaithfullyFlat B C := by
  letI := coverAlgebra e
  letI : Algebra B (A' ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let c : B ⊗[A] A' ≃ₐ[B] A' ⊗[A] B :=
    { (Algebra.TensorProduct.comm A B A').toRingEquiv with
      commutes' := fun b => by
        change Algebra.TensorProduct.comm A B A' (b ⊗ₜ 1) = 1 ⊗ₜ b
        rw [Algebra.TensorProduct.comm_tmul] }
  exact Module.FaithfullyFlat.of_linearEquiv B (B ⊗[A] A')
    ((c.trans (coverAlgEquiv e)).symm.toLinearEquiv)

end Langlands.GroupScheme.WeilChart

namespace Langlands.GroupScheme

open WeilChart

/-- **Descent of a Weil-restriction presentation along one étale cover**, from factor rigidity and
descent of finite étale algebras. -/
theorem affineWeilPairSingleChartDescent (hR : WeilFactorIdempotentRigidityStatement.{u})
    (hK : Langlands.AlgebraicGeometry.FiniteEtaleChartDescentStatement.{u}) :
    AffineWeilPairSingleChartDescentStatement.{u} := by
  intro A A' _ _ _ _ hsurj G _ _ C _ _ _ _ _ H _ _ hred hsimple hP
  obtain ⟨P⟩ := hP
  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap A A'))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  haveI : Module.FaithfullyFlat A A' :=
    RingHom.faithfullyFlat_algebraMap_iff.mp
      ((flat_and_surjective_SpecMap_iff _).mp ⟨hflat, hsurj⟩)
  obtain ⟨B, _, _, _, _, _, e, hinv⟩ := exists_chartDescent P hR hred hsimple hK hsurj
  have hinv' : ∀ (T : CommAlgCat.{u} (CommRingCat.of A)) (f₁ f₂ : A' →ₐ[A] T) (b : B),
      chartAlgEquiv P hR hred hsimple f₁ f₂ (coeffTmul f₂ 1 (e (1 ⊗ₜ[A] b))) =
        coeffTmul f₁ 1 (e (1 ⊗ₜ[A] b)) := hinv
  letI : Algebra B C := coverAlgebra e
  have hBC : ∀ b : B, algebraMap B C b = e ((1 : A') ⊗ₜ[A] b) := fun _ => rfl
  haveI : Algebra.Etale B C := coverAlgebra_etale e
  haveI : Module.FaithfullyFlat B C := coverAlgebra_faithfullyFlat e
  haveI : Etale (Spec.algebraMap B C) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  haveI : Surjective (Spec.algebraMap B C) :=
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap B C))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).2
  haveI := factorGroup_isAffine e P hR hred hsimple hinv'
  haveI := factorGroup_locallyOfFiniteType e P hR hred hsimple hinv'
  exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    factorGroup e P hR hred hsimple hinv', inferInstance, inferInstance,
    factorGroup_isReductive e P hR hred hsimple hinv' hBC,
    factorGroup_isAlmostSimple e P hR hred hsimple hinv' hBC,
    ⟨weilIso e P hR hred hsimple hinv'⟩⟩

/-- **Étale pair descent**, from factor rigidity and descent of finite étale algebras. This is the
input `hD` of the adjoint Weil-restriction assembly. -/
theorem affineWeilPairEtaleDescent (hR : WeilFactorIdempotentRigidityStatement.{u})
    (hK : Langlands.AlgebraicGeometry.FiniteEtaleChartDescentStatement.{u}) :
    AffineWeilPairEtaleDescentStatement.{u} :=
  affineWeilPairEtaleDescent_of_singleChart hR (affineWeilPairSingleChartDescent hR hK)

end Langlands.GroupScheme
