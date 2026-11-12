import Langlands.Automorphic.ArchimedeanPlaceParameter

/-! # Archimedean place parameters of mixed-rank cuspidal classes

The archimedean place parameters of actual cuspidal classes, for the mixed-rank classes
`PositiveRankCuspidalClass F` used by isobaric data, together with the rank conditions they
carry. No parameter is constructed or asserted to exist.
-/

noncomputable section

universe u

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.LocalFactor.Archimedean

variable {F : Type u} [Field F] [NumberField F]

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

namespace OperatorRealization

variable {n : ℕ}

/-- The blocks of a real place parameter have total rank `n`. -/
theorem IsoClass.HasRealPlaceParameter.realRank_eq {c : IsoClass F n} {v : RP}
    {ds : List RealBlock} (h : c.HasRealPlaceParameter v ds) : realRank ds = n := by
  induction c using Quotient.inductionOn with
  | h S => exact h.1

/-- A complex place parameter has `n` blocks. -/
theorem IsoClass.HasComplexPlaceParameter.length_eq {c : IsoClass F n} {v : CP}
    {ds : List ComplexCharacterData} (h : c.HasComplexPlaceParameter v ds) :
    ds.length = n := by
  induction c using Quotient.inductionOn with
  | h S => exact h.1

end OperatorRealization

variable [CompactSpace (AdeleQuotient F)]

namespace PositiveRankCuspidalClass

/-- The real place parameter of a mixed-rank actual cuspidal class. -/
def HasRealPlaceParameter (c : PositiveRankCuspidalClass F) (v : RP) (ds : List RealBlock) :
    Prop :=
  c.2.HasRealPlaceParameter v ds

/-- The complex place parameter of a mixed-rank actual cuspidal class. -/
def HasComplexPlaceParameter (c : PositiveRankCuspidalClass F) (v : CP)
    (ds : List ComplexCharacterData) : Prop :=
  c.2.HasComplexPlaceParameter v ds

@[simp]
theorem hasRealPlaceParameter_ofFixedRank {r : ℕ}
    (c : CuspidalOperatorRealization.IsoClass F r) (v : RP) (ds : List RealBlock) :
    (ofFixedRank c).HasRealPlaceParameter v ds ↔ c.HasRealPlaceParameter v ds :=
  Iff.rfl

@[simp]
theorem hasComplexPlaceParameter_ofFixedRank {r : ℕ}
    (c : CuspidalOperatorRealization.IsoClass F r) (v : CP) (ds : List ComplexCharacterData) :
    (ofFixedRank c).HasComplexPlaceParameter v ds ↔ c.HasComplexPlaceParameter v ds :=
  Iff.rfl

/-- The blocks of a real place parameter have total rank the rank of the class. -/
theorem HasRealPlaceParameter.realRank_eq {c : PositiveRankCuspidalClass F} {v : RP}
    {ds : List RealBlock} (h : c.HasRealPlaceParameter v ds) : realRank ds = c.rank :=
  OperatorRealization.IsoClass.HasRealPlaceParameter.realRank_eq h

/-- A complex place parameter has as many blocks as the rank of the class. -/
theorem HasComplexPlaceParameter.length_eq {c : PositiveRankCuspidalClass F} {v : CP}
    {ds : List ComplexCharacterData} (h : c.HasComplexPlaceParameter v ds) :
    ds.length = c.rank :=
  OperatorRealization.IsoClass.HasComplexPlaceParameter.length_eq h

end PositiveRankCuspidalClass

end Langlands.Automorphic
