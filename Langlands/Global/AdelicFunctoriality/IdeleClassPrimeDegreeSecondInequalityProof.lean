import Langlands.Global.AdelicFunctoriality.IdeleClassPrimeDegreeSecondInequalityStatement
import Langlands.Global.AdelicFunctoriality.CyclotomicSecondInequalityReduction
import Langlands.Global.AdelicFunctoriality.IdeleClassNormIndexFiniteProof
import Langlands.Global.AdelicFunctoriality.IdeleClassNormTowerProof
import Langlands.ClassFieldTheory.Global.IdeleClassGaloisDescentProof
import Langlands.ClassFieldTheory.Global.CyclicIdeleClassHerbrandAssembly
import Langlands.Global.Arithmetic.KummerSecondInequality
import Langlands.Global.Arithmetic.CyclicNonsplitPrimeProof

/-! # The prime-degree second inequality for actual idele classes -/

namespace Langlands.Global.AdelicFunctoriality

universe u v

/-- The actual idele-class norm index divides the degree in every Galois
prime-degree extension of number fields. -/
theorem ideleClassPrimeDegreeSecondInequality :
    IdeleClassPrimeDegreeSecondInequality.{u, v} :=
  ideleClassCyclotomicSecondInequalityReduction_holds.{u, v}
    ideleClassNormIndexFinite.{u, v} ideleClassNormTower.{u, v, v}
    (Langlands.Global.Arithmetic.KummerSecondInequality.ideleClassKummerPrimeDegreeSecondInequality_of.{v}
        Langlands.Global.cyclicNonsplitPrimeStatement.{v, v}
        Langlands.ClassFieldTheory.Global.ideleClassGaloisDescent.{v, v}
        Langlands.ClassFieldTheory.Global.cyclicIdeleClassHerbrandQuotient.{v, v})

end Langlands.Global.AdelicFunctoriality
