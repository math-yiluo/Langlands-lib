import Langlands.GroupScheme.CentralSimpleNormOneSplitting
import Langlands.GroupScheme.SpecialLinearSimplyConnected
import Langlands.GroupScheme.SimplyConnected.AlgebraicExtensionReflection
import Langlands.GroupScheme.Reductive.AbsoluteStarAction

/-! # The actual absolute pinning of the reduced-norm-one group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.CentralSimpleUnits

open Langlands.CentralSimple

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [Algebra.IsCentral k A] [IsSimpleRing A]

/-- The reduced-norm-one group of any central simple algebra is simply connected. -/
theorem normOne_isSimplyConnected : IsSimplyConnected (normOne k A) := by
  apply IsSimplyConnected.of_algebraicExtension (K := SeparableClosure k)
  exact IsSimplyConnected.of_iso (Splitting.splittingIso k A (separableClosureChart k A))
    (SpecialLinear.isSimplyConnected (Fin (reducedDegree k A)) (SeparableClosure k))

/-- Absolute Galois pinning data of the actual reduced-norm-one group. -/
def normOneAbsolutePinning :
    letI : IsAffineHom (normOne k A).X.hom := isAffineHom_of_isAffine _
    GaloisPinningData k (SeparableClosure k) (normOne k A) := by
  letI : IsAffineHom (normOne k A).X.hom := isAffineHom_of_isAffine _
  exact GaloisPinningData.ofSeparableClosure
    (normOne_isSimplyConnected k A).isSemisimple.isConnectedReductive

end Langlands.GroupScheme.CentralSimpleUnits
