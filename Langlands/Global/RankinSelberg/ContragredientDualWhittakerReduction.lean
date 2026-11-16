import Langlands.Automorphic.ContragredientUniqueness
import Langlands.Automorphic.CuspidalOperatorMultiplicityOneStatement
import Langlands.Global.RankinSelberg.CuspidalTransposeInverseContragredientStatement
import Langlands.Global.RankinSelberg.ContragredientDualWhittakerIdentity
import Langlands.Global.RankinSelberg.ContragredientDualSpherical
import Langlands.Global.RankinSelberg.EqualDualEulerFactorizationReduction

/-! # Reduction of the contragredient Whittaker identity

`ContragredientDualWhittakerStatement` follows from multiplicity one for actual cuspidal
operator realizations (`CuspidalOperatorMultiplicityOneStatement`) and the fact that the
dual cusp forms `φ̃(g) = φ(w_n ᵗg⁻¹)` lie in an actual cuspidal realization of the
contragredient (`CuspidalTransposeInverseContragredientStatement`). See the paired
Markdown.
-/

noncomputable section

universe u

namespace Langlands.Global.RankinSelbergGlobal

/-- An actual cuspidal operator realization is determined by its underlying operator
realization; irreducibility and cuspidality are propositions. -/
theorem cuspidalOperatorRealization_ext {F : Type u} [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] {r : ℕ}
    {T T' : Automorphic.CuspidalOperatorRealization F r}
    (h : T.realization = T'.realization) : T = T' := by
  cases T
  cases T'
  cases h
  rfl

/-- The reduction: multiplicity one and the realization of the dual cusp forms in a
cuspidal contragredient imply the contragredient Whittaker identity. -/
def ContragredientDualWhittakerReductionStatement : Prop :=
  Automorphic.CuspidalOperatorMultiplicityOneStatement.{u} →
    CuspidalTransposeInverseContragredientStatement.{u} →
      ContragredientDualWhittakerStatement.{u}

/-- Proof of the reduction. The contragredient `T'` of `T` containing the dual cusp forms
is equivalent to `Td` (uniqueness of contragredients), hence equal to `Td` (multiplicity
one). The vector `xd` of `Td` whose cusp form is `φ̃_x` is spherical outside `S`
(`isSphericalOutside_of_cuspFunction_eq_dual`) and has `ψ⁻¹`-Whittaker function
`W̃_x` (`cuspWhittaker_inv_eq_dualFunction`). -/
theorem contragredientDualWhittakerReduction :
    ContragredientDualWhittakerReductionStatement.{u} := by
  intro hA hB F _ _ _ ψ hψ r T Td hTd S x hx
  obtain ⟨T', hT', hdual⟩ := hB F r T
  obtain ⟨e⟩ :=
    Automorphic.OperatorRealization.IsContragredientOf.nonempty_equivalence hT' hTd
  have hT'eq : T' = Td := cuspidalOperatorRealization_ext (hA F r T' Td ⟨e⟩)
  subst hT'eq
  obtain ⟨xd, hxd⟩ := hdual x
  exact ⟨xd, isSphericalOutside_of_cuspFunction_eq_dual F T T' S x xd hxd hx,
    cuspWhittaker_inv_eq_dualFunction F T T' ψ.complex
      (isStandardAdditiveCharacter_of_unitary ψ hψ) x xd hxd⟩

end Langlands.Global.RankinSelbergGlobal
