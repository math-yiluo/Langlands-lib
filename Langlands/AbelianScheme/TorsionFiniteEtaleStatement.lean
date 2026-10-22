import Langlands.AbelianScheme.Basic
import Langlands.AbelianScheme.Torsion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finite etale torsion of abelian schemes -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Positive torsion of an abelian scheme is finite etale over the base when
its index is invertible on the base. This is a statement target, not a proof. -/
def TorsionFiniteEtaleStatement : Prop :=
  ∀ (S : Scheme.{u}) (A : AbelianScheme S) (n : ℕ),
    0 < n → IsUnit (n : Γ(S, ⊤)) →
      IsFinite (GroupScheme.torsion A.toGrp (n : ℤ)).X.hom ∧
        Etale (GroupScheme.torsion A.toGrp (n : ℤ)).X.hom

end Langlands.AbelianScheme
