import Langlands.AlgebraicGeometry.FiniteEtale.Statements
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

open CategoryTheory CategoryTheory.Limits

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- A finite morphism to the spectrum of a field has only finitely many sections. -/
theorem finite_sections_of_isFinite {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (.of K)) [IsFinite f] :
    Finite {x : Spec (.of K) ⟶ X // x ≫ f = 𝟙 _} := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let e := Scheme.ΓSpecIso (.of K)
  let φ : CommRingCat.of K ⟶ Γ(X, ⊤) := e.inv ≫ f.appTop
  let _ : Algebra K Γ(X, ⊤) := φ.hom.toAlgebra
  have : Module.Finite K Γ(X, ⊤) := by
    have h : φ.hom.Finite :=
      RingHom.Finite.comp f.finite_appTop
        (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso e.inv).2)
    exact h
  let ev : {x : Spec (.of K) ⟶ X // x ≫ f = 𝟙 _} → (Γ(X, ⊤) →ₐ[K] K) := fun x =>
    { toRingHom := (x.1.appTop ≫ e.hom).hom
      commutes' := fun r => by
        have hx : f.appTop ≫ x.1.appTop = 𝟙 _ := by
          rw [← Scheme.Hom.comp_appTop, x.2, Scheme.Hom.id_appTop]
        have h : e.inv ≫ f.appTop ≫ x.1.appTop ≫ e.hom = 𝟙 _ := by
          rw [reassoc_of% hx, Iso.inv_hom_id]
        exact congrArg (fun g : CommRingCat.of K ⟶ CommRingCat.of K => g.hom r) h }
  refine Finite.of_injective ev ?_
  intro x y hxy
  apply Subtype.ext
  apply ext_of_isAffine
  have h : x.1.appTop ≫ e.hom = y.1.appTop ≫ e.hom := by
    ext a
    exact DFunLike.congr_fun hxy a
  exact (cancel_mono e.hom).1 h

/-- Every actual geometric fibre of a finite étale cover is finite. -/
theorem geometricFiberFinite {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : GeometricFiberFinite s := by
  intro Y
  have := finite_sections_of_isFinite (pullback.snd Y.obj.hom s)
  refine Finite.of_injective
    (fun x : Fiber s Y =>
      (⟨(fiberEquivPoints s Y x).left, by simpa using Over.w (fiberEquivPoints s Y x)⟩ :
        {p : Spec (.of Ω) ⟶ pullback Y.obj.hom s // p ≫ pullback.snd Y.obj.hom s = 𝟙 _})) ?_
  intro x y hxy
  apply (fiberEquivPoints s Y).injective
  exact Over.OverMorphism.ext (congrArg Subtype.val hxy)

end Langlands.AlgebraicGeometry.FiniteEtale
