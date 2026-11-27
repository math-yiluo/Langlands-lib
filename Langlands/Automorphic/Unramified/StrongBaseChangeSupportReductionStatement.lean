import Langlands.Automorphic.Unramified.CyclicStrongBaseChangeSupportStatement
import Langlands.Automorphic.Unramified.CyclicWeakBaseChangeSupercuspidalStatement
import Langlands.Automorphic.Unramified.TowerBaseChangeHeckeComponentStatement
import Langlands.Automorphic.Unramified.CyclicWeakBaseChangeComplexPlaceStatement

/-!
# B5, B6 and B7 from strong cyclic base change on support and parameters

Six implications. Each has the named external input
`CyclicStrongBaseChangeSupportStatement` (derived from Arthur–Clozel 1989, Theorem III.5.1) as
its only premise, at fixed universe levels, and a published interface as its conclusion, at
all of its universe levels: B5 (`CyclicWeakBaseChangeSupercuspidalStatement`), B6
(`TowerBaseChangeHeckeComponentStatement`), B7 (`CyclicWeakBaseChangeComplexPlaceStatement`)
and their totally complex forms. Statements only; see the paired Markdown.
-/

universe uF uE uK uV uW

namespace Langlands.Automorphic.Unramified

/-- B5 from strong cyclic base change: the premise, with local fields in `uF` and local
representation spaces in `max uF uE`, implies `CyclicWeakBaseChangeSupercuspidalStatement`. -/
def CyclicWeakBaseChangeSupercuspidalReductionStatement : Prop :=
  CyclicStrongBaseChangeSupportStatement.{uF, max uF uE, uF, uE, uV, uW} →
    CyclicWeakBaseChangeSupercuspidalStatement.{uF, uE, uV, uW}

/-- The totally complex form of B5 from the same instantiation of strong cyclic base change. -/
def CyclicWeakBaseChangeSupercuspidalReductionTCStatement : Prop :=
  CyclicStrongBaseChangeSupportStatement.{uF, max uF uE, uF, uE, uV, uW} →
    CyclicWeakBaseChangeSupercuspidalTCStatement.{uF, uE, uV, uW}

/-- B6 from strong cyclic base change: the premise, with both global fields, the local fields
and the local representation spaces in the universe `uK` of the tower's levels, implies
`TowerBaseChangeHeckeComponentStatement`. -/
def TowerBaseChangeHeckeComponentReductionStatement : Prop :=
  CyclicStrongBaseChangeSupportStatement.{uK, uK, uK, uK, uV, uW} →
    TowerBaseChangeHeckeComponentStatement.{uF, uK, uV, uW}

/-- The totally complex form of B6 from the same instantiation of strong cyclic base change. -/
def TowerBaseChangeHeckeComponentReductionTCStatement : Prop :=
  CyclicStrongBaseChangeSupportStatement.{uK, uK, uK, uK, uV, uW} →
    TowerBaseChangeHeckeComponentTCStatement.{uF, uK, uV, uW}

/-- B7 from strong cyclic base change: the premise, at the instantiation used for B5, implies
`CyclicWeakBaseChangeComplexPlaceStatement`. Only its complex-place clause C is meant to be
used. -/
def CyclicWeakBaseChangeComplexPlaceReductionStatement : Prop :=
  CyclicStrongBaseChangeSupportStatement.{uF, max uF uE, uF, uE, uV, uW} →
    CyclicWeakBaseChangeComplexPlaceStatement.{uF, uE, uV, uW}

/-- The totally complex form of B7 from the same instantiation of strong cyclic base change. -/
def CyclicWeakBaseChangeComplexPlaceReductionTCStatement : Prop :=
  CyclicStrongBaseChangeSupportStatement.{uF, max uF uE, uF, uE, uV, uW} →
    CyclicWeakBaseChangeComplexPlaceTCStatement.{uF, uE, uV, uW}

end Langlands.Automorphic.Unramified
