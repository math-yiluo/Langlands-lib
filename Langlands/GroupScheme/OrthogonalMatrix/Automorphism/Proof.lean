import Langlands.GroupScheme.OrthogonalMatrix.Automorphism.RootScaling
import Langlands.GroupScheme.OrthogonalMatrix.Automorphism.TorusNormalization

/-! # Automorphisms of the split `SO_{2n}` are conjugations by similitudes

Proof of `SpecialOrthogonalAutomorphismStatement`: an automorphism of `SO_{2n}`, `n ≥ 2`, is
first composed with a conjugation by a similitude so that it fixes the diagonal torus
(`exists_isSimilitudeConj_comp_fix`), and the result is a conjugation by a diagonal similitude
(`isSimilitudeConj_of_comp_identityTorus`).
-/

universe u

namespace Langlands.GroupScheme.OrthogonalMatrix

/-- **`Aut(SO_{2n}) = PGO_{2n}`.** Every automorphism of the split `SO_{2n}` over a field,
`n ≥ 2`, is conjugation by a similitude of the split quadratic form. -/
theorem specialOrthogonalAutomorphism : SpecialOrthogonalAutomorphismStatement.{u} := by
  intro L _ n hn α
  obtain ⟨γ, hγ, hfix⟩ := exists_isSimilitudeConj_comp_fix hn α
  exact (isSimilitudeConj_of_comp_identityTorus hn (α ≪≫ γ) hfix).of_trans hγ

end Langlands.GroupScheme.OrthogonalMatrix
