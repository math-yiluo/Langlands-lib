import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.Analysis.Complex.Basic

/-! # Statement: the anisotropic form of a real semisimple group (Milne 25.56) -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The anisotropic form** (Milne, *Algebraic Groups*, Theorem 25.56 (Cartan)). Let `G` be a
semisimple group over `ℝ`. A form of `G` is a group over `ℝ` that becomes isomorphic to `G`
over `ℂ`.
1. `G` has a semisimple form `G'` that is anisotropic (has split rank zero).
2. Any two anisotropic semisimple forms of `G` are isomorphic over `ℝ`.

This is a statement only; nothing is proved here. -/
def RealAnisotropicFormStatement : Prop :=
  ∀ G : GroupScheme (Spec (CommRingCat.of ℝ)), IsSemisimple G →
    (∃ G' : GroupScheme (Spec (CommRingCat.of ℝ)), IsSemisimple G' ∧ IsAnisotropic G' ∧
      Nonempty ((GroupScheme.baseChange (algebraBaseMap ℝ ℂ)).obj G' ≅
        (GroupScheme.baseChange (algebraBaseMap ℝ ℂ)).obj G)) ∧
    ∀ G₁ G₂ : GroupScheme (Spec (CommRingCat.of ℝ)),
      IsSemisimple G₁ → IsSemisimple G₂ → IsAnisotropic G₁ → IsAnisotropic G₂ →
      Nonempty ((GroupScheme.baseChange (algebraBaseMap ℝ ℂ)).obj G₁ ≅
        (GroupScheme.baseChange (algebraBaseMap ℝ ℂ)).obj G) →
      Nonempty ((GroupScheme.baseChange (algebraBaseMap ℝ ℂ)).obj G₂ ≅
        (GroupScheme.baseChange (algebraBaseMap ℝ ℂ)).obj G) →
      Nonempty (G₁ ≅ G₂)

end Langlands.GroupScheme
