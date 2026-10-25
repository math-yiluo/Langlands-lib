import Langlands.Global.AdelicFunctoriality.IdeleClassPrimeDegreeSecondInequalityStatement
import Langlands.Global.AdelicFunctoriality.IdeleClassNormIndexFiniteStatement
import Langlands.Global.AdelicFunctoriality.IdeleClassNormLawsStatement
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Kummer case and cyclotomic reduction for the second inequality -/

universe u v

namespace Langlands.Global.AdelicFunctoriality

/-- The actual idele-class second inequality for Galois prime-degree extensions
whose base contains a primitive root of unity of that prime order. -/
def IdeleClassKummerPrimeDegreeSecondInequality : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    Nat.Prime (Module.finrank K L) →
      (∃ ζ : K, IsPrimitiveRoot ζ (Module.finrank K L)) →
        (ideleClassNorm (K := K) (L := L)).toMonoidHom.range.index ∣
          Module.finrank K L

/-- The finite norm-index bound and norm tower law reduce the general
prime-degree inequality to its root-containing case. -/
def IdeleClassCyclotomicSecondInequalityReduction : Prop :=
  IdeleClassNormIndexFinite.{u, v} →
    IdeleClassNormTower.{u, v, v} →
      IdeleClassKummerPrimeDegreeSecondInequality.{v, v} →
        IdeleClassPrimeDegreeSecondInequality.{u, v}

end Langlands.Global.AdelicFunctoriality
