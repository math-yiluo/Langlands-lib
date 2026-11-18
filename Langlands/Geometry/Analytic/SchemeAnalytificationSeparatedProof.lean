import Langlands.Geometry.Analytic.SchemeAnalytificationSeparatedStatement
import Langlands.Geometry.Analytic.SeparatedAnalytificationForward

/-! # Proof: separatedness and Hausdorff scheme analytification -/

universe u

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry

/-- A morphism locally of finite type from a scheme to the spectrum of a complete ultrametric
nontrivially normed field is separated if and only if its glued analytification is
Hausdorff. -/
theorem schemeAnalytificationSeparated : SchemeAnalytificationSeparatedStatement.{u} := by
  intro K _ _ _ X f _
  constructor
  · intro _
    exact SeparatedForward.t2Space_of_isSeparated K f
  · intro _
    exact SeparatedReverse.isSeparated_of_t2Space K f

end Langlands.Analytic.SchemeAnalytification
