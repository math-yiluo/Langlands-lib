import Langlands.GaloisCohomology.Field.Modules
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Torsion classes with coefficients in `Ωˣ ⊗ X` die in cyclotomic extensions

This module states the Galois-cohomological form of the splitting of torsion torus classes
over a number field: a locally constant `1`-cocycle of `Gal(Ω/K)` with values in
`Ωˣ ⊗ X`, for a smooth lattice `X`, whose class is killed by `m > 0` becomes a coboundary
on `Gal(Ω/E)` for every intermediate field `E` containing a primitive `N`-th root of unity,
for some `N > 0` whose prime factors divide `m`. The statement is not proved here.
-/

namespace Langlands.GaloisCohomology

open CategoryTheory MonoidalCategory

universe u

/-- Let `K` be a number field with separable closure `Ω` and let `X` be a smooth module of
`Gal(Ω/K)` over `ULift ℤ` that is free of finite rank. Let `c` be a locally constant
`1`-cocycle of `Gal(Ω/K)` with values in `Ωˣ ⊗ X` (the tensor product of representations,
with the diagonal action), and suppose that `m • c` is a coboundary for some `m > 0`. Then
there is `N > 0`, each of whose prime factors divides `m`, such that the restriction of `c`
to `Gal(Ω/E)` is a coboundary for every intermediate field `E` of `Ω/K` containing a
primitive `N`-th root of unity. -/
def NumberFieldUnitsLatticeCyclotomicSplittingStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (X : Rep.{u} (ULift.{u} ℤ) (Ω ≃ₐ[K] Ω)) [IsSmoothRep X]
    [Module.Free (ULift.{u} ℤ) X] [Module.Finite (ULift.{u} ℤ) X]
    (c : (Ω ≃ₐ[K] Ω) → ↑(unitsModule K Ω ⊗ X)), IsLocallyConstant c →
    (∀ σ τ : Ω ≃ₐ[K] Ω, c (σ * τ) = c σ + (unitsModule K Ω ⊗ X).ρ σ (c τ)) →
    ∀ m : ℕ, 0 < m →
      (∃ b : ↑(unitsModule K Ω ⊗ X), ∀ σ, m • c σ = (unitsModule K Ω ⊗ X).ρ σ b - b) →
      ∃ N : ℕ, 0 < N ∧ (∀ q : ℕ, q.Prime → q ∣ N → q ∣ m) ∧
        ∀ E : IntermediateField K Ω, (∃ ζ : Ω, ζ ∈ E ∧ IsPrimitiveRoot ζ N) →
          ∃ b : ↑(unitsModule K Ω ⊗ X),
            ∀ σ ∈ E.fixingSubgroup, c σ = (unitsModule K Ω ⊗ X).ρ σ b - b

end Langlands.GaloisCohomology
