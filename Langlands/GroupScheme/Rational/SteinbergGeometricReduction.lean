import Langlands.GroupScheme.Rational.SplitSteinbergQuotientStatement
import Langlands.GroupScheme.Rational.SteinbergFieldBaseChange
import Langlands.GroupScheme.SimplyConnected.GeometricReduction

/-! # Algebraic-closure reduction for the supplied split Steinberg product -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The canonical quotient isomorphism on every supplied split Steinberg product over
an algebraically closed field, with the same data and conclusion as the full statement. -/
def SplitSteinbergQuotientAlgClosedStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G), IsSimplyConnected G →
    ∀ (r : ℕ) (e : Fin r ≃ p.base.support)
      (x : p.NormalizedSimpleRootParametrizations)
      (n : p.SimpleReflectionRepresentatives),
      IsIso (SplitPinning.steinbergProduct e x n ≫ ClassFunctions.rho G)

/-- The full theorem restricts to algebraically closed fields. -/
theorem splitSteinbergQuotientAlgClosed_of_splitSteinbergQuotient
    (h : SplitSteinbergQuotientStatement.{u}) :
    SplitSteinbergQuotientAlgClosedStatement.{u} := by
  intro k _ _ G _ p hG r e x n
  exact h k G p hG r e x n

/-- Algebraic-closure ascent of simple connectedness and the algebraically closed theorem
imply the exact arbitrary-field quotient theorem for all originally supplied data. -/
theorem splitSteinbergQuotient_of_algClosed
    (hascent : IsSimplyConnectedAlgebraicClosureAscentStatement.{u})
    (hclosed : SplitSteinbergQuotientAlgClosedStatement.{u}) :
    SplitSteinbergQuotientStatement.{u} := by
  intro k _ G _ p hG r e x n
  let K := AlgebraicClosure k
  let GK := (GroupScheme.baseChange (algebraBaseMap k K)).obj G
  have : IsAffineHom GK.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
    infer_instance
  have hGK : IsSimplyConnected GK := hascent k G hG
  have hproduct :=
    hclosed K GK (p.baseChange (F := K)) hGK r
      (SplitPinning.fieldBaseChangeOrder (F := K) e)
      (SplitPinning.fieldBaseChangeRootMaps (F := K) x)
      (SplitPinning.fieldBaseChangeRepresentatives (F := K) n)
  exact (SplitPinning.isIso_steinbergQuotient_baseChange_iff (F := K) e x n).mp hproduct

/-- Once simple-connectedness ascent is available, the arbitrary-field theorem is
equivalent to its algebraically closed restriction. -/
theorem splitSteinbergQuotient_iff_algClosed
    (hascent : IsSimplyConnectedAlgebraicClosureAscentStatement.{u}) :
    SplitSteinbergQuotientStatement.{u} ↔ SplitSteinbergQuotientAlgClosedStatement.{u} :=
  ⟨splitSteinbergQuotientAlgClosed_of_splitSteinbergQuotient,
    splitSteinbergQuotient_of_algClosed hascent⟩

end Langlands.GroupScheme
