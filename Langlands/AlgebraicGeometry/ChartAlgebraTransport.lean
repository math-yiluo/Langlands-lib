import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Transport of algebra points from functorial chart transitions -/

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

/-- The original chart base change with the specified chart scalar action. -/
abbrev Fiber (T : CommAlgCat.{u} (CommRingCat.of A)) (f : B →ₐ[A] T) :=
  letI := f.toRingHom.toAlgebra
  T ⊗[B] C

/-- A point of the chart algebra with a specified compatible chart map. -/
abbrev Point (T : CommAlgCat.{u} (CommRingCat.of A)) (f : B →ₐ[A] T) :=
  letI := f.toRingHom.toAlgebra
  C →ₐ[B] T

/-- The actual coefficient map on the chart tensor algebras. -/
def tensorMap {T T' : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T')
    (f : B →ₐ[A] T) : Fiber (C := C) T f →+* Fiber (C := C) T' (χ.hom.comp f) := by
  letI := f.toRingHom.toAlgebra
  letI := (χ.hom.comp f).toRingHom.toAlgebra
  exact (Algebra.TensorProduct.map
    ({ χ.hom.toRingHom with commutes' := fun _ => rfl } : T →ₐ[B] T')
    (AlgHom.id B C)).toRingHom

@[simp] theorem tensorMap_tmul {T T' : CommAlgCat.{u} (CommRingCat.of A)}
    (χ : T ⟶ T') (f : B →ₐ[A] T) (t : T) (c : C) :
    letI := f.toRingHom.toAlgebra
    letI := (χ.hom.comp f).toRingHom.toAlgebra
    tensorMap (C := C) χ f (t ⊗ₜ[B] c) = χ.hom t ⊗ₜ[B] c := by
  rfl

/-- Functorial chart-transition algebra isomorphisms and their three laws. -/
structure Datum (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] where
  equiv : ∀ (T : CommAlgCat.{u} (CommRingCat.of A)) (f₁ f₂ : B →ₐ[A] T),
    Fiber (C := C) T f₂ ≃ₐ[T] Fiber (C := C) T f₁
  identity : ∀ T f, equiv T f f = AlgEquiv.refl
  cocycle : ∀ T f₁ f₂ f₃, (equiv T f₂ f₃).trans (equiv T f₁ f₂) = equiv T f₁ f₃
  naturality : ∀ (T T' : CommAlgCat.{u} (CommRingCat.of A)) (χ : T ⟶ T')
    (f₁ f₂ : B →ₐ[A] T) (x : Fiber (C := C) T f₂),
    equiv T' (χ.hom.comp f₁) (χ.hom.comp f₂) (tensorMap χ f₂ x) =
      tensorMap χ f₁ (equiv T f₁ f₂ x)

/-- Tensor adjunction extends a compatible chart point by multiplication. -/
def evalEquiv (T : CommAlgCat.{u} (CommRingCat.of A)) (f : B →ₐ[A] T) :
    Point (C := C) T f ≃ (Fiber (C := C) T f →ₐ[T] T) := by
  letI := f.toRingHom.toAlgebra
  exact AlgHom.liftEquiv B T C T

/-- Postcompose a chart point along a coefficient-algebra map. -/
def pointMap {T T' : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T')
    (f : B →ₐ[A] T) (g : Point (C := C) T f) : Point (C := C) T' (χ.hom.comp f) := by
  letI := f.toRingHom.toAlgebra
  letI := (χ.hom.comp f).toRingHom.toAlgebra
  exact { χ.hom.toRingHom.comp g.toRingHom with
    commutes' := fun b => by
      change χ.hom (g (algebraMap B C b)) = χ.hom (f b)
      rw [g.commutes]
      rfl }

@[simp] theorem pointMap_apply {T T' : CommAlgCat.{u} (CommRingCat.of A)}
    (χ : T ⟶ T') (f : B →ₐ[A] T) (g : Point (C := C) T f) (c : C) :
    pointMap χ f g c = χ.hom (g c) := rfl

namespace Datum

variable (D : Datum A B C)

/-- Change the chart of a compatible point by the prescribed transition. -/
def transport (T : CommAlgCat.{u} (CommRingCat.of A)) (f₁ f₂ : B →ₐ[A] T)
    (g : Point (C := C) T f₂) : Point (C := C) T f₁ :=
  (evalEquiv T f₁).symm ((evalEquiv T f₂ g).comp (D.equiv T f₂ f₁).toAlgHom)

/-- Extending a transported point recovers the transition on the entire tensor algebra. -/
theorem eval_transport (T : CommAlgCat.{u} (CommRingCat.of A)) (f₁ f₂ : B →ₐ[A] T)
    (g : Point (C := C) T f₂) :
    evalEquiv T f₁ (D.transport T f₁ f₂ g) =
      (evalEquiv T f₂ g).comp (D.equiv T f₂ f₁).toAlgHom :=
  (evalEquiv T f₁).apply_symm_apply _

@[simp] theorem transport_apply (T : CommAlgCat.{u} (CommRingCat.of A))
    (f₁ f₂ : B →ₐ[A] T) (g : Point (C := C) T f₂) (c : C) :
    letI := f₁.toRingHom.toAlgebra
    D.transport T f₁ f₂ g c = evalEquiv T f₂ g (D.equiv T f₂ f₁ (1 ⊗ₜ[B] c)) := rfl

/-- Identity transitions give identity transport. -/
@[simp] theorem transport_self (T : CommAlgCat.{u} (CommRingCat.of A))
    (f : B →ₐ[A] T) (g : Point (C := C) T f) : D.transport T f f g = g := by
  apply (evalEquiv T f).injective
  rw [eval_transport, D.identity]
  rfl

/-- The chart-point transports satisfy the same cocycle. -/
theorem transport_trans (T : CommAlgCat.{u} (CommRingCat.of A))
    (f₁ f₂ f₃ : B →ₐ[A] T) (g : Point (C := C) T f₃) :
    D.transport T f₁ f₂ (D.transport T f₂ f₃ g) = D.transport T f₁ f₃ g := by
  apply (evalEquiv T f₁).injective
  rw [eval_transport, eval_transport, eval_transport]
  ext x
  exact congrArg (fun e => evalEquiv T f₃ g (e x)) (D.cocycle T f₃ f₂ f₁)

/-- Evaluation commutes with the original coefficient maps. -/
theorem eval_pointMap {T T' : CommAlgCat.{u} (CommRingCat.of A)}
    (χ : T ⟶ T') (f : B →ₐ[A] T) (g : Point (C := C) T f)
    (x : Fiber (C := C) T f) :
    evalEquiv T' (χ.hom.comp f) (pointMap χ f g) (tensorMap χ f x) =
      χ.hom (evalEquiv T f g x) := by
  let := f.toRingHom.toAlgebra
  let := (χ.hom.comp f).toRingHom.toAlgebra
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul t c =>
    change χ.hom t * χ.hom (g c) = χ.hom (t * g c)
    exact (map_mul χ.hom t (g c)).symm

/-- Compatible point transport is natural along every coefficient-algebra map. -/
theorem transport_naturality {T T' : CommAlgCat.{u} (CommRingCat.of A)}
    (χ : T ⟶ T') (f₁ f₂ : B →ₐ[A] T) (g : Point (C := C) T f₂) :
    pointMap χ f₁ (D.transport T f₁ f₂ g) =
      D.transport T' (χ.hom.comp f₁) (χ.hom.comp f₂) (pointMap χ f₂ g) := by
  let := f₁.toRingHom.toAlgebra
  let := (χ.hom.comp f₁).toRingHom.toAlgebra
  apply AlgHom.ext
  intro c
  have hn := D.naturality T T' χ f₂ f₁ (1 ⊗ₜ[B] c)
  have he := congrArg (evalEquiv T' (χ.hom.comp f₂) (pointMap χ f₂ g)) hn
  rw [tensorMap_tmul, map_one, eval_pointMap] at he
  exact he.symm

end Datum
end Langlands.AlgebraicGeometry.ChartAlgebraDescent
