import Langlands.Representation.Filtration.GradedRepetitionStatement
import Langlands.Representation.Filtration.MultiplicityAdditivityProof

/-! An additive multiplicity proof of the graded repetition criterion. -/

open scoped BigOperators

namespace Langlands

universe uK uG uY

namespace ObjectRepFiltration

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {Y : Rep.{uY} k G} {N m : ℕ}

/-- Two distinct equivalent nonzero graded pieces force repetition in any
actual composition series of their ambient representation. -/
theorem exists_equiv_factors_of_equiv_graded
    (t : ObjectRepFiltration Y N) (ht : t.HasSimpleFactors)
    (u : ObjectRepFiltration Y m) {i j : Fin m} (hij : i ≠ j)
    (e : (u.gradedRepresentation i).ρ.Equiv (u.gradedRepresentation j).ρ)
    (hnt : Nontrivial (u.gradedRepresentation i)) :
    ∃ a b : Fin N, a ≠ b ∧
      Nonempty ((t.gradedRepresentation a).ρ.Equiv (t.gradedRepresentation b).ρ) := by
  classical
  have hY : repLength Y.ρ = N := repLength_eq_of_hasSimpleFactors t ht
  have hfin :
      IsFiniteLength (MonoidAlgebra k G) (u.gradedRepresentation i).ρ.asModule := by
    apply Module.length_ne_top_iff.mp
    have hle : repLength (u.gradedRepresentation i).ρ ≤ (N : ℕ∞) := by
      rw [← hY, repLength_eq_sum_of_filtration u]
      exact Finset.single_le_sum
        (f := fun a : Fin m => repLength (u.gradedRepresentation a).ρ)
        (fun _ _ => zero_le) (Finset.mem_univ i)
    exact ne_top_of_le_ne_top (by simp) hle
  obtain ⟨n, r, hr⟩ := MultiplicityAdditivityProof.exists_series hfin
  have hn : 0 < n := by
    have hpos : 0 < repLength (u.gradedRepresentation i).ρ :=
      repLength_pos_iff.mpr hnt
    rw [repLength_eq_of_hasSimpleFactors r hr] at hpos
    exact_mod_cast hpos
  let τ := r.gradedRepresentation ⟨0, hn⟩
  have hpos : 0 < r.factorMultiplicity τ := by
    unfold factorMultiplicity
    exact Nat.card_pos_iff.mpr
      ⟨⟨⟨⟨0, hn⟩, ⟨Representation.Equiv.refl _⟩⟩⟩, inferInstance⟩
  obtain ⟨lengths, counts, H, -, hsum⟩ :=
    jordanHolderFiltrationDecomposition k G Y τ N (t.factorMultiplicity τ) m
      ⟨t, ht⟩ ⟨N, t, ht, rfl⟩ u
  have hi : HasJordanHolderMultiplicity (u.gradedRepresentation i) τ (counts i) := by
    obtain ⟨s, hs, hc⟩ := H i
    exact ⟨lengths i, s, hs, hc⟩
  have hj : HasJordanHolderMultiplicity (u.gradedRepresentation j) τ (counts j) := by
    obtain ⟨s, hs, hc⟩ := H j
    exact ⟨lengths j, s, hs, hc⟩
  have hi_eq : counts i = r.factorMultiplicity τ :=
    HasJordanHolderMultiplicity.unique hi ⟨n, r, hr, rfl⟩
  have hj_eq : counts j = counts i :=
    HasJordanHolderMultiplicity.unique hj
      ((equivJordanHolderMultiplicityTransport k G
        (u.gradedRepresentation i) (u.gradedRepresentation j) τ τ e
        (Representation.Equiv.refl _) (counts i)).mp hi)
  have hpair : counts i + counts j ≤ ∑ a, counts a := by
    calc
      counts i + counts j = ∑ a ∈ ({i, j} : Finset (Fin m)), counts a := by
        simp [hij]
      _ ≤ ∑ a, counts a := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have htwo : 2 ≤ t.factorMultiplicity τ := by omega
  by_contra hrep
  have hfree : ∀ a b : Fin N,
      Nonempty ((t.gradedRepresentation a).ρ.Equiv (t.gradedRepresentation b).ρ) →
        a = b := by
    intro a b hab
    by_contra hne
    exact hrep ⟨a, b, hne, hab⟩
  have hle : t.factorMultiplicity τ ≤ 1 := by
    unfold factorMultiplicity
    rw [Finite.card_le_one_iff_subsingleton]
    constructor
    rintro ⟨a, ⟨f⟩⟩ ⟨b, ⟨g⟩⟩
    exact Subtype.ext (hfree a b ⟨f.trans g.symm⟩)
  omega

end ObjectRepFiltration

/-- Closed generic criterion, with three independent universes. -/
theorem gradedFactorRepetitionCriterion :
    GradedFactorRepetitionCriterion.{uK, uG, uY} := by
  intro k _ G _ Y N m t ht u i j hij e hnt
  exact t.exists_equiv_factors_of_equiv_graded ht u hij e hnt

end Langlands
