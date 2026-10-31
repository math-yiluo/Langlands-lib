import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.QuasiIso

set_option autoImplicit false

universe u

open CategoryTheory

namespace Langlands.Cohomology.ModuleComplex

/-- Explicit cycle and boundary tests imply a categorical quasi-isomorphism. -/
def NatModuleQuasiIsoCriterionStatement : Prop :=
  ∀ (R : Type u) [CommRing R]
    (K C : CochainComplex (ModuleCat.{u} R) ℕ) (φ : K ⟶ C),
    (∀ x : K.X 0, K.d 0 1 x = 0 → φ.f 0 x = 0 → x = 0) →
    (∀ y : C.X 0, C.d 0 1 y = 0 →
      ∃ x : K.X 0, K.d 0 1 x = 0 ∧ φ.f 0 x = y) →
    (∀ (i : ℕ) (x : K.X (i + 1)),
      K.d (i + 1) (i + 2) x = 0 →
      φ.f (i + 1) x ∈ LinearMap.range (C.d i (i + 1)).hom →
      x ∈ LinearMap.range (K.d i (i + 1)).hom) →
    (∀ (i : ℕ) (y : C.X (i + 1)),
      C.d (i + 1) (i + 2) y = 0 →
      ∃ x : K.X (i + 1), K.d (i + 1) (i + 2) x = 0 ∧
        φ.f (i + 1) x - y ∈ LinearMap.range (C.d i (i + 1)).hom) →
    QuasiIso φ

end Langlands.Cohomology.ModuleComplex
