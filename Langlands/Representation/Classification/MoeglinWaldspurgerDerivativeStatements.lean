import Langlands.Representation.Classification.MoeglinWaldspurger

/-!
# Bottom-up unmatched endings and two MW compatibility targets

The bottom-up matching of intervals ending at `x` with intervals ending at `x - 1`,
and two proposition targets relating it to the concrete MW recursion.
-/

namespace Langlands.MoeglinWaldspurger

/-- Scan order: increasing beginning, and at equal beginnings longer intervals first. -/
def ScanLE (I J : Interval) : Prop :=
  I.beginning < J.beginning ∨ (I.beginning = J.beginning ∧ J.ending ≤ I.ending)

instance : DecidableRel ScanLE := fun I J => by unfold ScanLE; infer_instance

instance : Std.Total ScanLE where
  total I J := by unfold ScanLE; omega

instance : IsTrans Interval ScanLE where
  trans I J K := by unfold ScanLE; omega

instance : Std.Antisymm ScanLE where
  antisymm I J hIJ hJI := by
    unfold ScanLE at hIJ hJI
    exact Interval.ext (by omega) (by omega)

/-- Scan a list with a pool of available intervals ending at `x - 1`. An interval
ending at `x` consumes one pool element if the pool is nonempty and is otherwise
recorded as unmatched. Other intervals are ignored. -/
def unmatchedScan (x : ℤ) : List Interval → ℕ → List Interval
  | [], _ => []
  | I :: l, pool =>
    if I.ending = x - 1 then unmatchedScan x l (pool + 1)
    else if I.ending = x then
      if pool = 0 then I :: unmatchedScan x l pool else unmatchedScan x l (pool - 1)
    else unmatchedScan x l pool

/-- The occurrences ending at `x` left unmatched by the bottom-up scan of `a`. -/
def unmatched (a : Multisegment) (x : ℤ) : Multisegment :=
  (unmatchedScan x (a.sort ScanLE) 0 : Multiset Interval)

/-- Shorten exactly the unmatched occurrences ending at `x` at their right end. -/
def leftDerivative (a : Multisegment) (x : ℤ) : Multisegment :=
  a - unmatched a x + shorten (unmatched a x)

/-- The one-point interval `[x,x]`. -/
def point (x : ℤ) : Interval := ⟨x, x, le_refl x⟩

/-- For an input whose endings are `x` or `x - 1`, the MW output contains the point
`[x,x]` exactly once for each unmatched occurrence, and shortening the unmatched
occurrences removes exactly these points from the output. Proved as `topUnmatchedCompatibility` in
module `MoeglinWaldspurgerTopCompatibility`. -/
def TopUnmatchedCompatibility : Prop :=
  ∀ (J : Multisegment) (x : ℤ), (∀ I ∈ J, I.ending = x ∨ I.ending = x - 1) →
    (dual J).count (point x) = (unmatched J x).card ∧
      dual (leftDerivative J x) =
        dual J - Multiset.replicate (unmatched J x).card (point x)

/-- At the beginning `c` of the first emitted interval, the residual has exactly one
fewer unmatched occurrence. If the round selects one interval, the two shortenings
agree. Otherwise shortening the input yields a round emitting `[c+1, e]` whose
residual is the shortened residual. Proved as `chainUnmatchedCompatibility` in module
`MoeglinWaldspurgerChainCompatibility`. -/
def ChainUnmatchedCompatibility : Prop :=
  ∀ (a : Multisegment) (r : Round), round a = some r →
    (unmatched a r.emitted.beginning).card =
        (unmatched r.residual r.emitted.beginning).card + 1 ∧
      (r.tail = [] →
        leftDerivative a r.emitted.beginning =
          leftDerivative r.residual r.emitted.beginning) ∧
      (r.tail ≠ [] →
        ∃ r' : Round, round (leftDerivative a r.emitted.beginning) = some r' ∧
          r'.emitted.beginning = r.emitted.beginning + 1 ∧
          r'.emitted.ending = r.emitted.ending ∧
          r'.residual = leftDerivative r.residual r.emitted.beginning)

end Langlands.MoeglinWaldspurger
