import Langlands.Automorphic.CuspidalInvariantPairingCriterion

/-! # Symmetry of the contragredient relation for cuspidal realizations -/

set_option autoImplicit false

universe u

namespace Langlands.Automorphic.CuspidalOperatorRealization

open NumberField Langlands.Global

/-- For actual cuspidal realizations of the same rank, the contragredient relation
is symmetric. -/
theorem isContragredientOf_symm {F : Type u} [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] {r : ℕ}
    {S T : CuspidalOperatorRealization F r}
    (h : T.realization.IsContragredientOf S.realization) :
    S.realization.IsContragredientOf T.realization := by
  obtain ⟨B, hB⟩ := h
  obtain ⟨hfinite, hcompact, hlie⟩ := hB.1
  have hInvariant : T.realization.IsInvariantPairing S.realization B.flip :=
    ⟨fun d x y => hfinite d y x, fun k x y => hcompact k y x,
      fun X x y => (add_comm _ _).trans (hlie X y x)⟩
  apply isContragredientOf_of_nonzero_invariant hInvariant
  intro hzero
  obtain ⟨x, hx⟩ := exists_ne (0 : T.Space)
  have hEq : B.flip x = B.flip (0 : T.Space) := by
    simp only [hzero, LinearMap.zero_apply]
  exact hx (hB.2.2.1 hEq)

end Langlands.Automorphic.CuspidalOperatorRealization

namespace Langlands.Automorphic

open NumberField Langlands.Global

/-- The contragredient relation on actual cuspidal realizations of each rank is symmetric. -/
def CuspidalContragredientSymmetryStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (S T : CuspidalOperatorRealization F r),
    T.realization.IsContragredientOf S.realization →
      S.realization.IsContragredientOf T.realization

/-- Reversing a contragredient pairing yields the symmetry statement in every field universe. -/
theorem cuspidalContragredientSymmetry : CuspidalContragredientSymmetryStatement.{u} := by
  intro F _ _ _ r S T h
  exact CuspidalOperatorRealization.isContragredientOf_symm h

end Langlands.Automorphic
