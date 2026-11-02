import Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamic
import Langlands.GroupScheme.Examples.QuasiSplitUnitarySplitting
import Langlands.GroupScheme.Torus.Split
import Langlands.GroupScheme.Reductive.Basic

/-! # The quasi-split unitary group `U(1,1)` has split rank one over `F`: statement -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.QuasiSplitUnitary

/-- For a nontrivial conjugation `c`, the cocharacter `t ↦ diag(t, t⁻¹)` of `U(1,1)` is a closed
subgroup, every split torus of `U(1,1)` over `F` has rank at most one, and the base change of
`U(1,1)` to `E` contains a split torus of rank two. -/
def RankStatement : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    (κ : Type u) [Fintype κ] (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E))
    (c : E ≃ₐ[F] E), c ≠ AlgEquiv.refl →
      IsClosedSubgroup (cocharacter b c) ∧
      (∀ (I : Type u) [Finite I]
        (i : splitTorus (Spec (CommRingCat.of F)) I ⟶ groupScheme b c),
          IsClosedSubgroup i → Nat.card I ≤ 1) ∧
      ∃ (I : Type u) (_ : Finite I), Nat.card I = 2 ∧
        ∃ i : splitTorus (Spec (CommRingCat.of E)) I ⟶ baseChangeGroupScheme b c,
          IsClosedSubgroup i

end Langlands.GroupScheme.QuasiSplitUnitary
