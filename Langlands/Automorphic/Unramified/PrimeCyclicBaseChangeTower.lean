import Langlands.Automorphic.Unramified.IsobaricWeakTransfer
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Finite prime cyclic towers and supplied isobaric chains

Internal vocabulary for B6 of the operator external-inputs plan, Section 2.2.
Levels are numbered upwards from the actual base field to the actual top field.
No existence, uniqueness, transitivity or local compatibility result is asserted.
-/

noncomputable section

universe uF uK uV uW

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global

namespace IsobaricData

variable {F : Type uF} {K : Type uK} [Field F] [Field K]
  [NumberField F] [NumberField K]
  [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient K)]

/-- Pull each constituent back along the specified field equivalence, retaining its
rank and multiplicity. The direction is from data over `K` to data over `F`. -/
def arithmeticComap (e : F ≃+* K) (D : IsobaricData K) : IsobaricData F :=
  D.map (PositiveRankCuspidalClass.arithmeticComap e)

@[simp]
theorem rank_arithmeticComap (e : F ≃+* K) (D : IsobaricData K) :
    (D.arithmeticComap e).rank = D.rank := by
  simp only [rank, arithmeticComap, Multiset.map_map, Function.comp_def,
    PositiveRankCuspidalClass.rank_arithmeticComap]

@[simp]
theorem arithmeticComap_ofCuspidal (e : F ≃+* K) (c : PositiveRankCuspidalClass K) :
    (ofCuspidal c).arithmeticComap e = ofCuspidal (c.arithmeticComap e) :=
  Multiset.map_singleton _ _

end IsobaricData

namespace Unramified

variable (F : Type uF) (K : Type uK) [Field F] [Field K]
  [NumberField F] [NumberField K] [Algebra F K]

/-- A finite increasing tower of intermediate fields of `K/F`, with bottom `F`,
top `K`, and cyclic Galois prime-degree steps for the actual inclusion algebras.
The endpoint equalities are equalities of intermediate fields, not of their carriers
with `F` or `K`. Length zero is permitted. -/
structure PrimeCyclicBaseChangeTower where
  length : ℕ
  level : Fin (length + 1) → IntermediateField F K
  monotone_level : Monotone level
  bottom_eq : level 0 = ⊥
  top_eq : level (Fin.last length) = ⊤
  primeCyclic_step : ∀ i : Fin length,
    letI := (IntermediateField.inclusion (monotone_level (Fin.castSucc_le_succ i))).toAlgebra
    IsGalois (level i.castSucc) (level i.succ) ∧
      IsCyclic (level i.succ ≃ₐ[level i.castSucc] level i.succ) ∧
      (Module.finrank (level i.castSucc) (level i.succ)).Prime

namespace PrimeCyclicBaseChangeTower

variable {F K}

/-- The embedding of the lower level into the next upper level. -/
def stepMap (T : PrimeCyclicBaseChangeTower F K) (i : Fin T.length) :
    T.level i.castSucc →ₐ[F] T.level i.succ :=
  IntermediateField.inclusion (T.monotone_level (Fin.castSucc_le_succ i))

/-- The adjacent algebra structure, installed locally when using weak base change. -/
@[instance_reducible]
def stepAlgebra (T : PrimeCyclicBaseChangeTower F K) (i : Fin T.length) :
    Algebra (T.level i.castSucc) (T.level i.succ) :=
  (T.stepMap i).toAlgebra

/-- The specified identification from the bottom carrier to the actual base field. -/
def bottomEquiv (T : PrimeCyclicBaseChangeTower F K) : T.level 0 ≃ₐ[F] F :=
  (IntermediateField.equivOfEq T.bottom_eq).trans (IntermediateField.botEquiv F K)

/-- The specified identification from the top carrier to the actual top field. -/
def topEquiv (T : PrimeCyclicBaseChangeTower F K) :
    T.level (Fin.last T.length) ≃ₐ[F] K :=
  (IntermediateField.equivOfEq T.top_eq).trans IntermediateField.topEquiv

/-- The zero-length tower over the identity extension. There are no adjacent steps. -/
def refl (F : Type uF) [Field F] [NumberField F] : PrimeCyclicBaseChangeTower F F where
  length := 0
  level := fun _ => ⊥
  monotone_level := fun _ _ _ => le_rfl
  bottom_eq := rfl
  top_eq := Subsingleton.elim _ _
  primeCyclic_step := Fin.elim0

variable (T : PrimeCyclicBaseChangeTower F K)
  [∀ i, CompactSpace (AdeleQuotient (T.level i))]

/-- Supplied constituent data, one actual isobaric multiset at every level.
No transfer or unitarity condition is part of this type. -/
abbrev IsobaricChain :=
  ∀ i : Fin (T.length + 1), IsobaricData (T.level i)

namespace IsobaricChain

variable {T}

/-- Every supplied level consists of unitarizable cuspidal constituents; intermediate
levels may have several constituents of different ranks. -/
def IsUnitary (D : T.IsobaricChain) : Prop :=
  ∀ i, (D i).IsUnitary

/-- Each upper datum is a weak base change of the immediately lower datum, using
the inclusion algebra at that step. Each relation includes the existing spectral
attachment and rank-equality conditions. -/
def IsSuccessiveWeakBaseChange (D : T.IsobaricChain) : Prop :=
  ∀ i : Fin T.length,
    letI := T.stepAlgebra i
    IsobaricData.IsWeakBaseChangeOf.{uK, uK, uV, uW} (D i.succ) (D i.castSucc)

variable [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient K)]

/-- The bottom datum is the pullback of the given data over the actual base field
along `bottomEquiv : bottom ≃ F`. -/
def StartsAt (D : T.IsobaricChain) (DF : IsobaricData F) : Prop :=
  D 0 = DF.arithmeticComap T.bottomEquiv.toRingEquiv

/-- Start at the one-constituent data of a fixed-rank actual cuspidal class over `F`.
The Library's rank index `r` means total rank `r + 1`. -/
def StartsAtCuspidal (D : T.IsobaricChain) {r : ℕ}
    (c : CuspidalOperatorRealization.IsoClass F r) : Prop :=
  D.StartsAt (IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank c))

/-- The terminal data over the actual field `K`: pull back the last level's data
along the inverse `K ≃ top` of the specified endpoint equivalence. -/
def terminal (D : T.IsobaricChain) : IsobaricData K :=
  (D (Fin.last T.length)).arithmeticComap T.topEquiv.symm.toRingEquiv

omit [CompactSpace (AdeleQuotient F)] in
@[simp]
theorem rank_terminal (D : T.IsobaricChain) :
    D.terminal.rank = (D (Fin.last T.length)).rank :=
  IsobaricData.rank_arithmeticComap _ _

end IsobaricChain
end PrimeCyclicBaseChangeTower
end Unramified
end Langlands.Automorphic
