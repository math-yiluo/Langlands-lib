import Langlands.Cohomology.Profinite.Functoriality
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Finite `ℓ`-primary classes of degree two die in `ℓ`-power cyclotomic extensions

This module states that a degree-two Galois cohomology class of a number field with
coefficients in a finite module killed by a power of a prime `ℓ` restricts to zero over
every extension containing a primitive `ℓ ^ r`-th root of unity, for some `r`. The
statement is not proved here.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology

universe u

/-- Let `K` be a number field with separable closure `Ω`, let `A` be a finite smooth module
of `Gal(Ω/K)` (written additively, with scalars `ULift ℤ`) killed by `ℓ ^ a` for a prime `ℓ`,
and let `β ∈ H²(Gal(Ω/K), A)`. Then there is `r` such that the restriction of `β` to
`Gal(Ω/E)` vanishes for every intermediate field `E` of `Ω/K` containing a primitive
`ℓ ^ r`-th root of unity. -/
def NumberFieldFiniteModuleCyclotomicKillingStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (A : Rep.{u} (ULift.{u} ℤ) (Ω ≃ₐ[K] Ω)) [IsSmoothRep A] [Finite A]
    (ℓ a : ℕ), ℓ.Prime → (∀ x : A, ℓ ^ a • x = 0) → ∀ β : cohomology A 2,
      ∃ r : ℕ, ∀ E : IntermediateField K Ω, (∃ ζ : Ω, ζ ∈ E ∧ IsPrimitiveRoot ζ (ℓ ^ r)) →
        (res A E.fixingSubgroup 2).hom β = 0

end Langlands.GaloisCohomology
