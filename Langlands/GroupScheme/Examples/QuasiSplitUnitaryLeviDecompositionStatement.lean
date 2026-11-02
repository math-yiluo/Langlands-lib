import Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamic
import Langlands.GroupScheme.Dynamic.Basic

/-! # Levi decomposition of the quasi-split unitary dynamic parabolic: statement -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

/-- Normalization, unique Levi factorization and opposite-subgroup intersections
for the hyperbolic cocharacter of the quasi-split unitary group. -/
def LeviDecompositionStatement : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
    (κ : Type u) [Fintype κ] (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E))
    (c : E ≃ₐ[F] E), c ≠ AlgEquiv.refl →
      (Dynamic.unipotent (cocharacter b c)).IsNormalizedBy
        (Dynamic.parabolic (cocharacter b c)) ∧
      (∀ (T : Over (Spec (CommRingCat.of F))) (g : T ⟶ (groupScheme b c).X),
        g ∈ (Dynamic.parabolic (cocharacter b c)).carrier T →
          ∃! p : (T ⟶ (groupScheme b c).X) × (T ⟶ (groupScheme b c).X),
            p.1 ∈ (Dynamic.centralizer (cocharacter b c)).carrier T ∧
            p.2 ∈ (Dynamic.unipotent (cocharacter b c)).carrier T ∧
            g = p.1 * p.2) ∧
      Dynamic.parabolic (cocharacter b c) ⊓ Dynamic.parabolic (inverseCocharacter b c) =
        Dynamic.centralizer (cocharacter b c) ∧
      Dynamic.unipotent (inverseCocharacter b c) ⊓ Dynamic.parabolic (cocharacter b c) = ⊥

end Langlands.GroupScheme.QuasiSplitUnitary
