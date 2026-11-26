import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalSupport

/-! Supercuspidal support adds under normalized products. -/

namespace Langlands.AllFieldBZ.CuspidalSupport

open LocalFieldPackage.TopologicalData

universe uF uV

/-- Every irreducible constituent of the normalized upper-block product
has the sum of the given supports of its factors. -/
def ProductConstituentSupportStatement (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : GeneralLinear.BlockShape n)
      (A : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
      (s : Fin B.length → Multiset (CuspidalDatum.{uV, uF} T)),
    (∀ i, T.IsSupercuspidalSupport (A i) (s i)) →
    let I := (T.normalizedProductInductionFunctor B).obj A
    ∀ P : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
      P.IsIrreducible → SmoothRep.IsSubquotient P I → T.IsSupercuspidalSupport P (∑ i, s i)

end Langlands.AllFieldBZ.CuspidalSupport
