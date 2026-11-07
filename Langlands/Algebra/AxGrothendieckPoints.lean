import Mathlib.FieldTheory.AxGrothendieck
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Ax–Grothendieck on points of a finite-type algebra -/

noncomputable section

universe u v

namespace Langlands.Algebra

open MvPolynomial

/-- An endomorphism of a finite-type algebra over an algebraically closed field
induces a surjection on field-valued points whenever it induces an injection. -/
theorem axGrothendieck_algHom
    {k : Type u} [Field k] [IsAlgClosed k]
    {A : Type v} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (f : A →ₐ[k] A)
    (hinj : Function.Injective (fun x : A →ₐ[k] k => x.comp f)) :
    Function.Surjective (fun x : A →ₐ[k] k => x.comp f) := by
  classical
  obtain ⟨n, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k A)
  let coords : (A →ₐ[k] k) → (Fin n → k) := fun x i => x (q (X i))
  have hEval (x : A →ₐ[k] k) : aeval (coords x) = x.comp q := by
    ext i
    simp [coords]
  have hcoords : Function.Injective coords := by
    intro x y h
    apply AlgHom.ext
    intro a
    obtain ⟨p, rfl⟩ := hq a
    change (x.comp q) p = (y.comp q) p
    rw [← hEval x, ← hEval y, h]
  let I := RingHom.ker q.toRingHom
  have hmem (x : A →ₐ[k] k) : coords x ∈ zeroLocus k I := by
    intro p hp
    rw [hEval]
    change x (q p) = 0
    rw [show q p = 0 from hp, map_zero]
  have hlift (v : Fin n → k) (hv : v ∈ zeroLocus k I) :
      ∃ x : A →ₐ[k] k, coords x = v := by
    have hker : RingHom.ker q.toRingHom ≤ RingHom.ker (aeval v).toRingHom := by
      intro p hp
      exact (mem_zeroLocus_iff.mp hv) p hp
    let x := q.liftOfSurjective hq (aeval v) hker
    refine ⟨x, ?_⟩
    funext i
    change q.liftOfSurjective hq (aeval v) _ (q (X i)) = v i
    rw [AlgHom.liftOfSurjective_apply, aeval_X]
  choose p hp using fun i : Fin n => hq (f (q (X i)))
  have hpoly (x : A →ₐ[k] k) :
      (fun i => eval (coords x) (p i)) = coords (x.comp f) := by
    funext i
    change aeval (coords x) (p i) = x (f (q (X i)))
    rw [hEval]
    change x (q (p i)) = _
    rw [hp]
  have hmaps : (zeroLocus k I).MapsTo
      (fun v i => eval v (p i)) (zeroLocus k I) := by
    intro v hv
    obtain ⟨x, rfl⟩ := hlift v hv
    change (fun i => eval (coords x) (p i)) ∈ zeroLocus k I
    rw [hpoly]
    exact hmem _
  have hinj' : (zeroLocus k I).InjOn (fun v i => eval v (p i)) := by
    intro v hv w hw hvw
    obtain ⟨x, rfl⟩ := hlift v hv
    obtain ⟨y, rfl⟩ := hlift w hw
    change (fun i => eval (coords x) (p i)) = (fun i => eval (coords y) (p i)) at hvw
    rw [hpoly, hpoly] at hvw
    exact congrArg coords (hinj (hcoords hvw))
  intro y
  obtain ⟨v, hv, hpolyv⟩ := ax_grothendieck_zeroLocus I p hmaps hinj' (hmem y)
  obtain ⟨x, rfl⟩ := hlift v hv
  exact ⟨x, hcoords ((hpoly x).symm.trans hpolyv)⟩

end Langlands.Algebra
