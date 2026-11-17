import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Statement: descent of a finite étale algebra from functorial chart isomorphisms -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry

/-- **Descent of a finite étale algebra from functorial chart isomorphisms.**
Let `A → A'` be étale with `Spec A' → Spec A` surjective and let `C` be a finite, projective,
étale `A'`-algebra. For an `A`-algebra `T` and an `A`-algebra map `f : A' → T`, write
`C_f = T ⊗[A', f] C` (a `T`-algebra through the left factor). Suppose given, for every `T` and
all `f₁ f₂ : A' → T`, `T`-algebra isomorphisms `θ T f₁ f₂ : C_{f₂} ≃ C_{f₁}` that are the
identity for `f₁ = f₂`, satisfy the cocycle condition `θ f₁ f₂ ∘ θ f₂ f₃ = θ f₁ f₃`, and are
natural along every map of `A`-algebras `χ : T → T₁` (with the chart maps `χ ∘ fₖ`). Then there
are a finite, projective, étale `A`-algebra `B` and an `A'`-algebra isomorphism
`e : A' ⊗[A] B ≃ C` such that every `θ T f₁ f₂` fixes `1 ⊗ e (1 ⊗ b)` for `b ∈ B`. -/
def FiniteEtaleChartDescentStatement : Prop :=
  ∀ (A A' C : Type u) [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A' C]
    [Algebra.Etale A A'] [Module.Finite A' C] [Module.Projective A' C] [Algebra.Etale A' C],
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap A A'))) →
    ∀ (θ : ∀ (T : CommAlgCat.{u} (CommRingCat.of A)) (f₁ f₂ : A' →ₐ[A] T),
        (letI := f₂.toRingHom.toAlgebra; T ⊗[A'] C) ≃ₐ[T]
          (letI := f₁.toRingHom.toAlgebra; T ⊗[A'] C)),
      (∀ (T : CommAlgCat.{u} (CommRingCat.of A)) (f : A' →ₐ[A] T),
        θ T f f = AlgEquiv.refl) →
      (∀ (T : CommAlgCat.{u} (CommRingCat.of A)) (f₁ f₂ f₃ : A' →ₐ[A] T),
        (θ T f₂ f₃).trans (θ T f₁ f₂) = θ T f₁ f₃) →
      (∀ (T T₁ : CommAlgCat.{u} (CommRingCat.of A)) (χ : T ⟶ T₁) (f₁ f₂ : A' →ₐ[A] T)
        (x : letI := f₂.toRingHom.toAlgebra; T ⊗[A'] C),
        θ T₁ (χ.hom.comp f₁) (χ.hom.comp f₂)
            (letI := f₂.toRingHom.toAlgebra
             letI := (χ.hom.comp f₂).toRingHom.toAlgebra
             Algebra.TensorProduct.map
               ({ χ.hom.toRingHom with commutes' := fun _ => rfl } : T →ₐ[A'] T₁)
               (AlgHom.id A' C) x) =
          (letI := f₁.toRingHom.toAlgebra
           letI := (χ.hom.comp f₁).toRingHom.toAlgebra
           Algebra.TensorProduct.map
             ({ χ.hom.toRingHom with commutes' := fun _ => rfl } : T →ₐ[A'] T₁)
             (AlgHom.id A' C) (θ T f₁ f₂ x))) →
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Finite A B)
        (_ : Module.Projective A B) (_ : Algebra.Etale A B) (e : A' ⊗[A] B ≃ₐ[A'] C),
        ∀ (T : CommAlgCat.{u} (CommRingCat.of A)) (f₁ f₂ : A' →ₐ[A] T) (b : B),
          θ T f₁ f₂ (letI := f₂.toRingHom.toAlgebra; (1 : T) ⊗ₜ[A'] e (1 ⊗ₜ[A] b)) =
            (letI := f₁.toRingHom.toAlgebra; (1 : T) ⊗ₜ[A'] e (1 ⊗ₜ[A] b))

end Langlands.AlgebraicGeometry
