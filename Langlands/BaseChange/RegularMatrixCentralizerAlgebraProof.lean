import Langlands.BaseChange.RegularMatrixCentralizerAlgebraStatement

/-! # The étale centralizer algebra of a regular matrix -/

noncomputable section

open Polynomial

namespace Langlands.BaseChange

universe u

/-- A monic separable polynomial gives a standard étale presentation with
localization at one. -/
private theorem etale_adjoinRoot {F : Type u} [Field F] {p : F[X]}
    (hp : p.Monic) (hsep : p.Separable) : Algebra.Etale F (AdjoinRoot p) := by
  let P : StandardEtalePair F := {
    f := p
    monic_f := hp
    g := 1
    cond := by
      obtain ⟨a, b, hab⟩ := (separable_def' p).mp hsep
      exact ⟨b, a, 0, by simpa only [pow_zero, mul_comm, add_comm] using hab⟩
  }
  have hunit : IsUnit (AdjoinRoot.mk P.f P.g) := by
    change IsUnit (AdjoinRoot.mk p 1)
    simp
  let e := IsLocalization.atUnit (AdjoinRoot p)
    (Localization.Away (AdjoinRoot.mk P.f P.g)) _ hunit
  exact Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans (e.symm.restrictScalars F))

/-- The characteristic-polynomial algebra identifies with the full commutant. -/
theorem regularMatrixCentralizerAlgebra : RegularMatrixCentralizerAlgebraStatement.{u} := by
  intro F _ n A hA
  obtain ⟨v, hv⟩ := regularCyclicBasis F n A hA
  refine ⟨etale_adjoinRoot A.charpoly_monic hA, ?_,
    charpolyRootEvaluation_injective A v hv, ?_⟩
  · change Module.finrank F (F[X] ⧸ Ideal.span {A.charpoly}) = n
    rw [finrank_quotient_span_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  · intro B
    constructor
    · rintro ⟨a, rfl⟩
      simpa only [charpolyRootEvaluation_root] using
        (Commute.all a (AdjoinRoot.root A.charpoly)).map (charpolyRootEvaluation A)
    · intro h
      obtain ⟨c, hc⟩ := exists_sum_pow_of_commute hv h
      refine ⟨AdjoinRoot.mk _ (∑ j : Fin n, monomial (j : ℕ) (c j)), ?_⟩
      rw [charpolyRootEvaluation_mk, hc, map_sum]
      simp only [aeval_monomial, Algebra.smul_def]

end Langlands.BaseChange
