import Langlands.GroupScheme.Torus.DiagonalizableUniversalSubtorus
import Langlands.GroupScheme.Torus.UniversalSubtorusDescent
import Langlands.GroupScheme.Torus.RelativeLargestSubtorusReduction

/-! # Largest subtori of groups of multiplicative type over arbitrary bases -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace RelativeMultiplicativeType

/-- Every group of relative multiplicative type has a universal subtorus. -/
theorem IsMultiplicativeType.exists_universalSubtorus
    {S : Scheme.{u}} {H : GroupScheme S} (hH : IsMultiplicativeType H) :
    ∃ (T : GroupScheme S) (j : T ⟶ H), IsUniversalSubtorus j := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := hH
  choose N r hr using fun i => (h𝒰 i).exists_universalSubtorus
  let C := UniversalSubtorusDescent.representative 𝒰 N r hr
  exact ⟨C.group, C.hom, UniversalSubtorusDescent.universal 𝒰 N r hr⟩

end RelativeMultiplicativeType

/-- The largest closed relative subtorus exists and every largest representative
remains largest after arbitrary base change, in every universe. -/
theorem relativeMultiplicativeTypeLargestSubtorus :
    RelativeMultiplicativeTypeLargestSubtorusStatement.{u} :=
  relativeMultiplicativeTypeLargestSubtorus_of_exists_universal
    fun _ _ hH => hH.exists_universalSubtorus

end Langlands.GroupScheme
