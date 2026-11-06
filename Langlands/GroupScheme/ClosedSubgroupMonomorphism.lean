import Langlands.GroupScheme.Reductive.Basic

/-! # Monicity of a closed subgroup over the base -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

universe u

/-- A closed subgroup is a monomorphism over the base. -/
theorem IsClosedSubgroup.mono_overHom {S : Scheme.{u}} {H G : GroupScheme S}
    {i : H ⟶ G} (hi : IsClosedSubgroup i) : Mono i.hom.hom := by
  have : IsClosedImmersion i.hom.hom.left := hi
  exact Over.mono_of_mono_left _

end Langlands.GroupScheme
