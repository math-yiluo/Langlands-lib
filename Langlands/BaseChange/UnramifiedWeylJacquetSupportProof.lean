import Langlands.BaseChange.UnramifiedWeylJacquetSupport.OppositeOrder
import Langlands.BaseChange.UnramifiedWeylJacquetSupport.SphericalGeneric

/-!
# Weyl Jacquet support of unramified principal series

The associated-Levi geometric filtration and exactness compute the Weyl multiset
and bound the multiplicities of every irreducible subquotient. Ordered spherical
generation and the top derivative give the two spherical conclusions.
-/

namespace Langlands.BaseChange

open Langlands.Unramified Langlands.Unramified.SphericalExistence
open WeylJacquet

universe uF uV

/-- The exact Weyl multiplicities, subquotient bound, and spherical order assertions
for the actual normalized Borel Jacquet modules. -/
theorem unramifiedWeylJacquetSupport : UnramifiedWeylJacquetSupportStatement.{uF, uV} := by
  intro p _ F r z
  have hW := principalSeries_borelJacquetMultiset F z
  refine ⟨hW, ?_⟩
  intro A hA
  have hle := borelJacquetMultiset_le_of_subquotient F
    (principalSeriesOfTuple_isAdmissible F z) A.property.2 hA
  refine ⟨hle.trans (le_of_eq hW), ?_⟩
  intro ψ hψ
  constructor
  · intro hs
    exact borelJacquetMultiset_of_spherical_generic F z A ⟨hs, hA⟩ ψ hψ
  · intro hs w hw ho
    exact spherical_of_opposite_borelJacquet_weight F A hw ho hs

end Langlands.BaseChange
