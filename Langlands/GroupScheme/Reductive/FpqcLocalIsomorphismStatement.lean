import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: fpqc-locally isomorphic reductive groups are étale-locally isomorphic -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Fpqc-local isomorphism implies étale-local isomorphism** (Conrad, *Reductive group
schemes* (2014), Proposition 6.2.11(1)). Let `G` and `G'` be reductive group schemes over a
scheme `S`. If there is an fpqc covering family `{Uᵢ ⟶ S}` such that `G_{Uᵢ} ≅ G'_{Uᵢ}` as group
schemes over every `Uᵢ`, then there is an étale covering family `{Vⱼ ⟶ S}` such that
`G_{Vⱼ} ≅ G'_{Vⱼ}` as group schemes over every `Vⱼ`. -/
def ReductiveFpqcLocalIsomorphismStatement : Prop :=
  ∀ (S : Scheme.{u}) (G G' : GroupScheme S), IsReductive G → IsReductive G' →
    (∃ 𝒰 : Scheme.Cover.{u} Scheme.fpqcPrecoverage S,
      ∀ i : 𝒰.I₀,
        Nonempty ((GroupScheme.baseChange (𝒰.f i)).obj G ≅
          (GroupScheme.baseChange (𝒰.f i)).obj G')) →
    ∃ 𝒱 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      ∀ j : 𝒱.I₀,
        Nonempty ((GroupScheme.baseChange (𝒱.f j)).obj G ≅
          (GroupScheme.baseChange (𝒱.f j)).obj G')

end Langlands.GroupScheme
