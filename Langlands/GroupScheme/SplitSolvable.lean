import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Split-solvable group schemes over an arbitrary field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

namespace SplitSolvable

/-- An actual group scheme over `k` is an elementary split-solvable quotient
when it is a one-dimensional vector group or is isomorphic over `k` to Gm. -/
def IsElementaryQuotient (V : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  RelativeRoot.IsVectorGroupOfDimension V 1 ∨
    Nonempty (V ≅ (Gm (Spec (CommRingCat.of k))).toGrp)

/-- A finite normal series with actual represented fppf quotients Ga or Gm.
Normality and triviality are tested on every relative scheme. -/
def HasSeries : ℕ → GroupScheme (Spec (CommRingCat.of k)) → Prop
  | 0, H => SubgroupFunctor.range (𝟙 H) = ⊥
  | n + 1, H =>
      ∃ (N V : GroupScheme (Spec (CommRingCat.of k))) (j : N ⟶ H) (q : H ⟶ V),
        IsClosedSubgroup j ∧ Smooth N.X.hom ∧ ConnectedSpace N.X.left ∧
          (SubgroupFunctor.range j).IsNormal ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q ∧
          IsElementaryQuotient V ∧ HasSeries n N

variable {H : GroupScheme (Spec (CommRingCat.of k))}

@[simp]
theorem hasSeries_zero_iff :
    HasSeries 0 H ↔ SubgroupFunctor.range (𝟙 H) = ⊥ := Iff.rfl

@[simp]
theorem hasSeries_succ_iff (n : ℕ) :
    HasSeries (n + 1) H ↔
      ∃ (N V : GroupScheme (Spec (CommRingCat.of k))) (j : N ⟶ H) (q : H ⟶ V),
        IsClosedSubgroup j ∧ Smooth N.X.hom ∧ ConnectedSpace N.X.left ∧
          (SubgroupFunctor.range j).IsNormal ∧
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q ∧
          IsElementaryQuotient V ∧ HasSeries n N := Iff.rfl

/-- Construct the length-zero series from all-test triviality. -/
theorem HasSeries.zero (h : SubgroupFunctor.range (𝟙 H) = ⊥) : HasSeries 0 H :=
  h

/-- Construct a successor series from a specified normal subgroup and fppf quotient. -/
theorem HasSeries.succ {n : ℕ} {N V : GroupScheme (Spec (CommRingCat.of k))}
    (j : N ⟶ H) (q : H ⟶ V)
    (hj : IsClosedSubgroup j) (hs : Smooth N.X.hom) (hc : ConnectedSpace N.X.left)
    (hn : (SubgroupFunctor.range j).IsNormal)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q)
    (hV : IsElementaryQuotient V) (hN : HasSeries n N) : HasSeries (n + 1) H :=
  ⟨N, V, j, q, hj, hs, hc, hn, hq, hV, hN⟩

/-- A Ga-only series is also a Ga/Gm series; the existing predicate is unchanged. -/
theorem HasSeries.of_splitSeries {n : ℕ} (h : RelativeRoot.HasSplitSeries n H) :
    HasSeries n H := by
  induction n generalizing H with
  | zero => exact h
  | succ n ih =>
      obtain ⟨N, V, j, q, hj, hs, hc, hn, hq, hV, hN⟩ := h
      exact HasSeries.succ j q hj hs hc hn hq (Or.inl hV) (ih hN)

end SplitSolvable

/-- A smooth connected affine solvable group scheme over `k` with a finite
normal series whose represented fppf quotients are Ga or Gm over `k`. -/
structure IsSplitSolvableGroupScheme (H : GroupScheme (Spec (CommRingCat.of k))) :
    Prop where
  smooth : Smooth H.X.hom
  isAffineHom : IsAffineHom H.X.hom
  connectedSpace : ConnectedSpace H.X.left
  isSolvableGroupScheme : IsSolvableGroupScheme H
  hasSeries : ∃ n : ℕ, SplitSolvable.HasSeries n H

variable {H : GroupScheme (Spec (CommRingCat.of k))}

/-- All outer structure hypotheses and the finite series witness. -/
theorem isSplitSolvableGroupScheme_iff :
    IsSplitSolvableGroupScheme H ↔
      Smooth H.X.hom ∧ IsAffineHom H.X.hom ∧ ConnectedSpace H.X.left ∧
        IsSolvableGroupScheme H ∧ ∃ n : ℕ, SplitSolvable.HasSeries n H :=
  ⟨fun h => ⟨h.smooth, h.isAffineHom, h.connectedSpace, h.isSolvableGroupScheme, h.hasSeries⟩,
    fun ⟨hs, ha, hc, hv, hn⟩ => ⟨hs, ha, hc, hv, hn⟩⟩

/-- A split-unipotent series supplies the series field when all the required
outer structure hypotheses are also supplied explicitly. -/
theorem IsSplitSolvableGroupScheme.of_isSplitUnipotent
    (hs : Smooth H.X.hom) (ha : IsAffineHom H.X.hom) (hc : ConnectedSpace H.X.left)
    (hv : IsSolvableGroupScheme H) (hu : RelativeRoot.IsSplitUnipotent H) :
    IsSplitSolvableGroupScheme H := by
  obtain ⟨n, hn⟩ := hu
  exact ⟨hs, ha, hc, hv, n, SplitSolvable.HasSeries.of_splitSeries hn⟩

end Langlands.GroupScheme
