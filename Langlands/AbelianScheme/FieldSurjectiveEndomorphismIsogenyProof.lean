import Langlands.AbelianScheme.FieldSurjectiveEndomorphismIsogenyStatement
import Langlands.AbelianScheme.FlatEqualDimensionQuasiFinite

/-! # Proof that surjective endomorphisms of abelian varieties are isogenies -/

universe u

namespace Langlands.AbelianScheme

/-- `FieldSurjectiveEndomorphismIsogenyStatement` holds. -/
theorem fieldSurjectiveEndomorphismIsogeny : FieldSurjectiveEndomorphismIsogenyStatement.{u} :=
  fun _ _ _ _ α hα => SurjectiveIsogeny.isIsogeny_of_surjective α hα

end Langlands.AbelianScheme
