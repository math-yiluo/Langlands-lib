import Langlands.GroupScheme.Reductive.MultiplicativeTypeNormalCentrality
import Langlands.GroupScheme.ConnectedResidueFibres
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Normal immersed multiplicative-type subgroups are central -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeMultiplicativeType

/-- A normal immersed subgroup of multiplicative type is central when the ambient
group has connected canonical residue fibres. -/
theorem isCentral_of_isNormal_of_connectedFibres
    {S : Scheme.{u}} {K H : GroupScheme S} (h : H ⟶ K)
    (hK : ∀ s : S, ConnectedSpace
      ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj K).X.left)
    (hi : IsImmersion h.hom.hom.left) (hH : IsMultiplicativeType H)
    (hn : (SubgroupFunctor.range h).IsNormal) : IsCentral h := by
  let : GeometricallyConnected K.X.hom :=
    geometricallyConnected_of_connectedResidueFibres K hK
  let : IsImmersion h.hom.hom.left := hi
  let : Mono h.hom.hom := Over.mono_of_mono_left _
  exact MultiplicativeTypeNormalCentral.isCentral_of_isNormal hH h hn

end Langlands.GroupScheme.RelativeMultiplicativeType
