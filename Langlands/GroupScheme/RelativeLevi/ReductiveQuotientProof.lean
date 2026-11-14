import Langlands.GroupScheme.RelativeLevi.ReductiveQuotientReduction
import Langlands.GroupScheme.RelativeLevi.ReductiveQuotientLocalDynamic
import Langlands.GroupScheme.RelativeLevi.ReductiveAnnihilationLocalDynamic
import Langlands.GroupScheme.RelativeLevi.ReductiveQuotientCoverBridge
import Langlands.GroupScheme.RelativeLevi.DynamicProof
import Langlands.GroupScheme.RelativeLevi.ParabolicClosedProof

/-! # The universal reductive quotient of a relative parabolic subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every scheme, a relative parabolic modulo its supplied relative
unipotent radical is a reductive fppf quotient with the universal property
for scheme-surjective homomorphisms to reductive groups. -/
theorem relativeParabolicReductiveQuotient :
    RelativeParabolicReductiveQuotientStatement.{u} := by
  apply relativeParabolicReductiveQuotientReduction
  · intro S G P U i r hG hP hU
    exact RelativeLevi.exists_reductiveQuotient_of_pointwise_dynamic
      dynamicRelativeLevi i r hG hP hU
      (RelativeLevi.pointwise_dynamic_of_etaleLocalDynamic
        relativeParabolicEtaleLocalDynamic i hG hP)
  · intro S G P U i r hG hP hU H f hH hf
    exact RelativeLevi.annihilates_radical_of_pointwise_dynamic
      dynamicRelativeLevi i r hG hP hU
      (RelativeLevi.pointwise_dynamic_of_etaleLocalDynamic
        relativeParabolicEtaleLocalDynamic i hG hP) f hH hf

end Langlands.GroupScheme
