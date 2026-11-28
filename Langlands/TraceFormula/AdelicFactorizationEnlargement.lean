import Langlands.TraceFormula.GeneralLinearBaseChangeLocal

/-! # Enlarging the set of places in an adelic factorization -/

universe u

open CategoryTheory AlgebraicGeometry NumberField
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

/-- The same adelic function has a factorization over a larger finite set when
the new local factors are the indicators of the corresponding tail subgroups. -/
theorem IsAdelicFactorization.of_subset {K : Type u} [Field K] [NumberField K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    {S T : Finset (Place K)} {φloc ψloc : (i : Place K) → PlaceGroupPoints K G i → ℂ}
    {U : (i : Place K) → Subgroup (PlaceGroupPoints K G i)}
    {φ : AdelicGroupPoints K G → ℂ} (hφ : IsAdelicFactorization K S φloc U φ)
    (hST : S ⊆ T) (hkeep : ∀ i ∈ S, ψloc i = φloc i)
    (hnew : ∀ i ∈ T, i ∉ S →
      ψloc i = (U i : Set (PlaceGroupPoints K G i)).indicator 1) :
    IsAdelicFactorization K T ψloc U φ := by
  classical
  intro x
  let tail (A : Finset (Place K)) : Set (AdelicGroupPoints K G) :=
    {y | ∀ i ∉ A, atPlace K G i y ∈ U i}
  change φ x = (tail T).indicator (fun y => ∏ i ∈ T, ψloc i (atPlace K G i y)) x
  rw [hφ x]
  change (tail S).indicator (fun y => ∏ i ∈ S, φloc i (atPlace K G i y)) x = _
  by_cases hS : x ∈ tail S
  · have hT : x ∈ tail T := fun i hi => hS i (fun his => hi (hST his))
    rw [Set.indicator_of_mem hS, Set.indicator_of_mem hT]
    calc
      _ = ∏ i ∈ S, ψloc i (atPlace K G i x) :=
        Finset.prod_congr rfl fun i hi => by rw [hkeep i hi]
      _ = _ := Finset.prod_subset hST fun i hiT hiS => by
        rw [hnew i hiT hiS, Set.indicator_of_mem (hS i hiS), Pi.one_apply]
  · rw [Set.indicator_of_notMem hS]
    by_cases hT : x ∈ tail T
    · rw [Set.indicator_of_mem hT]
      have hfail : ∃ i, i ∉ S ∧ atPlace K G i x ∉ U i := by
        by_contra hnone
        exact hS fun i hiS => by
          by_contra hiU
          exact hnone ⟨i, hiS, hiU⟩
      obtain ⟨i, hiS, hiU⟩ := hfail
      have hiT : i ∈ T := by
        by_contra hi
        exact hiU (hT i hi)
      exact (Finset.prod_eq_zero hiT (by rw [hnew i hiT hiS, Set.indicator_of_notMem hiU])).symm
    · rw [Set.indicator_of_notMem hT]

end Langlands.TraceFormula
