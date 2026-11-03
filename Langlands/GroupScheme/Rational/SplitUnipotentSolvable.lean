import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Rational.WeightSemigroup
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Uniform all-test solvability of split unipotent group schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {B : Scheme.{u}}

/-- The actual point-group derived series, as a subgroup functor on all tests. -/
def derivedSeriesFunctor (H : GroupScheme B) (n : ℕ) : SubgroupFunctor H where
  carrier T := derivedSeries (T ⟶ H.X) n
  comp_mem a x hx := by
    let f := (H.points.map a.op).hom
    exact (map_derivedSeries_le_derivedSeries f n) (Subgroup.mem_map_of_mem f hx)

@[simp] theorem derivedSeriesFunctor_carrier (H : GroupScheme B) (n : ℕ)
    (T : Over B) : (derivedSeriesFunctor H n).carrier T = derivedSeries (T ⟶ H.X) n :=
  rfl

/-- An extension by a group with commuting elements increases a known uniform
bound for the kernel's derived series by one. Pointwise surjectivity of the
quotient homomorphism is unnecessary. -/
private theorem derivedSeries_extension_bound {K H V : Type*}
    [Group K] [Group H] [Group V] (f : K →* H) (q : H →* V)
    (hker : q.ker ≤ f.range) (hcomm : ∀ x y : V, x * y = y * x)
    (n : ℕ) (hn : derivedSeries K n = ⊥) : derivedSeries H (n + 1) = ⊥ := by
  let : IsMulCommutative V := ⟨⟨hcomm⟩⟩
  have hbase : derivedSeries H 1 ≤ (derivedSeries K 0).map f := by
    simpa only [derivedSeries_one, derivedSeries_zero, Subgroup.map_top] using
      (Abelianization.commutator_subset_ker q).trans hker
  have hstep : ∀ m : ℕ, derivedSeries H (m + 1) ≤ (derivedSeries K m).map f := by
    intro m
    induction m with
    | zero => exact hbase
    | succ m ih => exact Subgroup.commutator_le_map_commutator ih ih
  exact le_bot_iff.mp (by simpa only [hn, Subgroup.map_bot] using hstep n)

/-- A split series of length `n` gives the same derived-series bound on every
scheme over the base. -/
theorem HasSplitSeries.derivedSeries_eq_bot {n : ℕ} {H : GroupScheme B}
    (h : HasSplitSeries n H) (T : Over B) : derivedSeries (T ⟶ H.X) n = ⊥ := by
  induction n generalizing H with
  | zero =>
      apply le_antisymm
      · intro x _
        have hx : x ∈ (SubgroupFunctor.range (𝟙 H)).carrier T :=
          ⟨x, Category.comp_id x⟩
        simpa only [show SubgroupFunctor.range (𝟙 H) = ⊥ from h,
          SubgroupFunctor.bot_carrier] using hx
      · exact bot_le
  | succ n ih =>
      obtain ⟨K, V, j, q, _, _, _, _, hq, hv, hK⟩ := h
      obtain ⟨e, _⟩ := hv
      let f := ((pointsMap j).app (op T)).hom
      let qT := ((pointsMap q).app (op T)).hom
      have hker : qT.ker ≤ f.range := by
        intro x hx
        change x ∈ (SubgroupFunctor.range j).carrier T
        rw [← hq.2.2.2]
        exact (mem_range_kernelι_iff q x).mpr hx
      have hcomm : ∀ x y : T ⟶ V.X, x * y = y * x := by
        intro x y
        apply (e T).injective
        rw [map_mul, map_mul, mul_comm]
      exact derivedSeries_extension_bound f qT hker hcomm n (ih hK)

/-- A split series kills the all-test derived subgroup functor at its length. -/
theorem HasSplitSeries.derivedSeriesFunctor_eq_bot {n : ℕ} {H : GroupScheme B}
    (h : HasSplitSeries n H) : derivedSeriesFunctor H n = ⊥ := by
  apply SubgroupFunctor.ext
  intro T
  exact h.derivedSeries_eq_bot T

/-- Split unipotence implies the uniform all-test solvability required by the
semigroup ordered-product theorem. -/
theorem IsSplitUnipotent.isSolvableScheme {H : GroupScheme B}
    (h : IsSplitUnipotent H) : IsSolvableScheme H := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun T => hn.derivedSeries_eq_bot T⟩

end Langlands.GroupScheme.RelativeRoot
