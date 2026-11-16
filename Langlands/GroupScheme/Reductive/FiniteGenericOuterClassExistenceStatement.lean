import Langlands.GroupScheme.Adjoint.RelativeQuotient
import Langlands.GroupScheme.OuterIsomorphismScheme
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! # A finite outer component containing a prescribed generic isomorphism class -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The outer class of each prescribed generic isomorphism is contained in
a finite relative scheme, for every supplied actual Isom and outer quotient. -/
def FiniteGenericOuterClassExistenceStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (G H : GroupScheme (Spec (CommRingCat.of R))),
    IsReductive G → IsReductive H →
    ∀ (f : (baseChange (Spec.algebraMap R K)).obj G ≅
      (baseChange (Spec.algebraMap R K)).obj H)
      (A : GroupScheme (Spec (CommRingCat.of R))) (q : G ⟶ A)
      (hq : IsRelativeAdjointQuotient q) (I : GroupIsomorphismScheme G H)
      (O : OuterIsomorphismScheme I hq.innerAction),
    Nonempty (FiniteGenericOuterClass O (I.classify
      (LocalGroupIso.ofBaseChangeIso (U := Over.mk (Spec.algebraMap R K)) f)))

end Langlands.GroupScheme
