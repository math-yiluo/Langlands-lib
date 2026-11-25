module

public import Mathlib.RingTheory.Extension.Presentation.Basic

/-! # Algebra maps specified on the generators of a presentation

Two algebra maps out of an algebra with chosen generators are equal when they agree on the
generators (`Algebra.Generators.algHom_ext`). For a presentation `P` of `S` over `R`, a family
`x` in an `R`-algebra `T` satisfying the relations of `P` defines the algebra map
`P.lift x hx : S →ₐ[R] T` sending the `i`-th generator to `x i` (`Algebra.Presentation.lift_val`).
-/

@[expose] public section

open MvPolynomial

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Two algebra maps that agree on the generators are equal. -/
theorem Generators.algHom_ext {ι : Type*} (P : Generators R S ι) {T : Type*} [Semiring T]
    [Algebra R T] {f g : S →ₐ[R] T} (h : ∀ i, f (P.val i) = g (P.val i)) : f = g := by
  apply (AlgHom.cancel_right P.aeval_val_surjective).mp
  apply MvPolynomial.algHom_ext
  simpa using h

namespace Presentation

variable {ι σ : Type*} (P : Presentation R S ι σ) {T : Type*} [CommRing T] [Algebra R T]

/-- The algebra map out of a presented algebra sending the generators to a family that satisfies
the relations. -/
noncomputable def lift (x : ι → T) (hx : ∀ r, aeval x (P.relation r) = 0) : S →ₐ[R] T :=
  (aeval P.val).liftOfSurjective P.aeval_val_surjective (aeval x) <| by
    change RingHom.ker (aeval P.val) ≤ RingHom.ker (aeval x)
    calc
      _ = Ideal.span (Set.range P.relation) :=
        P.ker_eq_ker_aeval_val.symm.trans P.span_range_relation_eq_ker.symm
      _ ≤ _ := Ideal.span_le.mpr (by rintro _ ⟨r, rfl⟩; exact hx r)

@[simp]
theorem lift_val (x : ι → T) (hx : ∀ r, aeval x (P.relation r) = 0) (i : ι) :
    P.lift x hx (P.val i) = x i := by
  calc
    _ = P.lift x hx (aeval P.val (X i)) := congrArg _ (aeval_X P.val i).symm
    _ = aeval x (X i) := AlgHom.liftOfSurjective_apply ..
    _ = _ := aeval_X x i

end Presentation
end Algebra
