import Langlands.GroupScheme.Dynamic.GeneralLinearRationalPoints
import Langlands.GroupScheme.Rational.MaximalTorusRationalConjugacyFinitenessStatement

/-! # Finiteness of rational conjugacy classes of maximal tori in `GL_n` -/

open AlgebraicGeometry

namespace Langlands.GroupScheme

universe u

/-- The maximal tori in the general linear group over a characteristic-zero
nonarchimedean local field have finitely many conjugacy classes under its
rational points. -/
def GeneralLinearMaximalTorusConjugacyFinitenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] (n : ℕ),
    HasFiniteMaximalTorusConjugacyClasses
      (GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))

end Langlands.GroupScheme
