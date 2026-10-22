import Langlands.ClassFieldTheory.Local.Cohomology

/-! # Closure-choice independence of actual absolute degree-two restriction -/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- The actual absolute restriction map in degree two is independent of the
base-compatible algebra structure between the specified algebraic closures. -/
def AbsoluteRestrictionClosureIndependence : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
    (α β : Algebra (AlgebraicClosure K) (AlgebraicClosure L))
    (hα : letI := α
      IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L))
    (hβ : letI := β
      IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)),
    (letI := α
     letI := hα
     absoluteRestriction K L 2) =
    (letI := β
     letI := hβ
     absoluteRestriction K L 2)

end Langlands.ClassFieldTheory.Local
