import Langlands.Global.ArchimedeanRelativeAdjoint
import Langlands.Representation.HorizontalAlternating

/-!
# Horizontal equivariant alternating spaces for the actual archimedean pair

This module constructs the underlying spaces only. It does not provide a
coefficient Lie action, a relative differential, or cohomology.
-/

noncomputable section

universe u v w z

set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

/-- Actual reduced adjoint action restricted to the full standard compact group. -/
def reducedCompactRepresentation :
    Representation ℂ (standardInfiniteCompact K n) (ReducedComplexLieAlgebra K n) where
  toFun k := (reducedComplexLieConjugation K n k.val).toLinearEquiv.toLinearMap
  map_one' := by
    ext X
    simp
  map_mul' k l := by
    apply LinearMap.ext
    intro X
    exact congrArg (fun e => e X)
      (reducedComplexLieConjugation_mul K n k.val l.val)

/-- Actual compact adjoint action of the full standard compact group. -/
def compactAdjointRepresentation :
    Representation ℂ (standardInfiniteCompact K n) (CompactComplexLieAlgebra K n) where
  toFun k := (compactComplexLieConjugation K n k).toLinearEquiv.toLinearMap
  map_one' := by
    ext X
    simp
  map_mul' k l := by
    apply LinearMap.ext
    intro X
    exact congrArg (fun e => e X) (compactComplexLieConjugation_mul K n k l)

@[simp] theorem reducedCompactRepresentation_apply (k : standardInfiniteCompact K n)
    (X : ReducedComplexLieAlgebra K n) :
    reducedCompactRepresentation K n k X = reducedComplexLieConjugation K n k.val X :=
  rfl

@[simp] theorem compactAdjointRepresentation_apply (k : standardInfiniteCompact K n)
    (X : CompactComplexLieAlgebra K n) :
    compactAdjointRepresentation K n k X = compactComplexLieConjugation K n k X :=
  rfl

/-- The actual compact-to-reduced inclusion as an intertwiner. -/
def compactToReducedIntertwiner :
    Representation.IntertwiningMap
      (compactAdjointRepresentation K n) (reducedCompactRepresentation K n) where
  toLinearMap := (compactToReducedComplex K n).toLinearMap
  isIntertwining' k := by
    apply LinearMap.ext
    intro X
    exact compactToReducedComplex_conjugation K n k X

theorem compactToReducedComplex_injective :
    Function.Injective (compactToReducedComplex K n) := by
  intro X Y h
  apply compactComplexInclusion_injective K n
  simpa only [reducedComplexInclusion_compact] using
    congrArg (reducedComplexInclusion K n) h

/-- The actual image of the complex compact algebra in the reduced algebra. -/
def compactInReducedSubmodule : Submodule ℂ (ReducedComplexLieAlgebra K n) :=
  LinearMap.range (compactToReducedComplex K n).toLinearMap

@[simp] theorem mem_compactInReducedSubmodule (X : ReducedComplexLieAlgebra K n) :
    X ∈ compactInReducedSubmodule K n ↔
      ∃ Y : CompactComplexLieAlgebra K n, compactToReducedComplex K n Y = X :=
  Iff.rfl

theorem compactInReducedSubmodule_stable (k : standardInfiniteCompact K n)
    {X : ReducedComplexLieAlgebra K n} (hX : X ∈ compactInReducedSubmodule K n) :
    reducedCompactRepresentation K n k X ∈ compactInReducedSubmodule K n := by
  obtain ⟨Y, rfl⟩ := hX
  exact ⟨compactComplexLieConjugation K n k Y,
    compactToReducedComplex_conjugation K n k Y⟩

variable {V : Type v} [AddCommGroup V] [Module ℂ V]
  {W : Type w} [AddCommGroup W] [Module ℂ W]
  {Z : Type z} [AddCommGroup Z] [Module ℂ Z]

/-- Actual horizontal, full-compact-equivariant alternating maps on the reduced algebra. -/
def horizontalEquivariantSubmodule
    (ρ : Representation ℂ (standardInfiniteCompact K n) V) (q : ℕ) :
    Submodule ℂ ((ReducedComplexLieAlgebra K n) [⋀^Fin q]→ₗ[ℂ] V) :=
  HorizontalAlternating.submodule (compactInReducedSubmodule K n)
    (reducedCompactRepresentation K n) ρ q

theorem mem_horizontalEquivariantSubmodule
    (ρ : Representation ℂ (standardInfiniteCompact K n) V) (q : ℕ)
    (f : (ReducedComplexLieAlgebra K n) [⋀^Fin q]→ₗ[ℂ] V) :
    f ∈ horizontalEquivariantSubmodule K n ρ q ↔
      (∀ (x : Fin q → ReducedComplexLieAlgebra K n) (i : Fin q)
        (Y : CompactComplexLieAlgebra K n),
        x i = compactToReducedComplex K n Y → f x = 0) ∧
      (∀ (k : standardInfiniteCompact K n) (x : Fin q → ReducedComplexLieAlgebra K n),
        f (fun i => reducedComplexLieConjugation K n k.val (x i)) = ρ k (f x)) := by
  change ((∀ x i, x i ∈ compactInReducedSubmodule K n → f x = 0) ∧ _) ↔ _
  constructor
  · rintro ⟨hh, he⟩
    refine ⟨?_, he⟩
    intro x i Y h
    exact hh x i ⟨Y, h.symm⟩
  · rintro ⟨hh, he⟩
    refine ⟨?_, he⟩
    rintro x i ⟨Y, hY⟩
    exact hh x i Y hY.symm

variable {ρ : Representation ℂ (standardInfiniteCompact K n) V}
  {τ : Representation ℂ (standardInfiniteCompact K n) W}
  {υ : Representation ℂ (standardInfiniteCompact K n) Z} (q : ℕ)

/-- Postcomposition by an actual full-compact coefficient intertwiner. -/
def horizontalMapCoefficients (A : Representation.IntertwiningMap ρ τ) :
    horizontalEquivariantSubmodule K n ρ q →ₗ[ℂ]
      horizontalEquivariantSubmodule K n τ q :=
  HorizontalAlternating.mapCoefficients (compactInReducedSubmodule K n)
    (reducedCompactRepresentation K n) q A

@[simp] theorem horizontalMapCoefficients_apply (A : Representation.IntertwiningMap ρ τ)
    (f : horizontalEquivariantSubmodule K n ρ q)
    (x : Fin q → ReducedComplexLieAlgebra K n) :
    (horizontalMapCoefficients K n q A f).val x = A (f.val x) := rfl

@[simp] theorem horizontalMapCoefficients_id :
    horizontalMapCoefficients K n q (Representation.IntertwiningMap.id ρ) =
      LinearMap.id :=
  HorizontalAlternating.mapCoefficients_id _ _ _

@[simp] theorem horizontalMapCoefficients_comp (A : Representation.IntertwiningMap ρ τ)
    (B : Representation.IntertwiningMap τ υ) :
    horizontalMapCoefficients K n q (B.comp A) =
      (horizontalMapCoefficients K n q B).comp (horizontalMapCoefficients K n q A) :=
  HorizontalAlternating.mapCoefficients_comp _ _ _ A B

/-- Coefficient representation equivalences transport the actual archimedean spaces. -/
def horizontalCoefficientEquiv (e : Representation.Equiv ρ τ) :
    horizontalEquivariantSubmodule K n ρ q ≃ₗ[ℂ]
      horizontalEquivariantSubmodule K n τ q :=
  HorizontalAlternating.coefficientEquiv (compactInReducedSubmodule K n)
    (reducedCompactRepresentation K n) q e

/-- Degree-zero underlying horizontal space equals the full compact fixed vectors. -/
def horizontalDegreeZeroEquiv
    (ρ : Representation ℂ (standardInfiniteCompact K n) V) :
    horizontalEquivariantSubmodule K n ρ 0 ≃ₗ[ℂ] ρ.invariants :=
  HorizontalAlternating.degreeZeroEquiv (compactInReducedSubmodule K n)
    (reducedCompactRepresentation K n) ρ

end Langlands.Global.ArchimedeanGL
