import Langlands.Automorphic.CuspidalAdmissible.Separation
import Langlands.Automorphic.CuspidalAdmissible.AdmissibilityReduction
import Langlands.Automorphic.CuspidalAdmissible.ContragredientAssembly

/-!
# Joint admissibility of unitary cuspidal realizations

Given Siegel finiteness for the adelic `GL_n` Siegel sets, every actual cuspidal realization
with unitary central character is jointly admissible: the band unitary form satisfies the
separation property, which yields joint admissibility. Hence actual unitary cuspidal
contragredients exist.
-/

noncomputable section

universe uF

open MeasureTheory

namespace Langlands.Automorphic.CuspidalAdmissible

open Langlands.Global Langlands.ClassField.Global.RelativeWeilGroup

/-- **Joint admissibility**, given Siegel finiteness. -/
theorem isJointlyAdmissible_of_siegelFiniteness
    (hSF : PrimitiveAdelicHeight.SiegelSetGLFinitenessStatement.{uF})
    {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (T : CuspidalOperatorRealization F r) (hT : HasUnitaryCentralCharacter T) :
    T.realization.IsJointlyAdmissible := by
  obtain ⟨χ, hχ, hTχ⟩ := hT
  let : MeasurableSpace (AdelicGL F (r + 1)) := borel _
  have : BorelSpace (AdelicGL F (r + 1)) := ⟨rfl⟩
  obtain ⟨t, ht, hcover, hfinite⟩ :=
    T.realization.exists_band_cover T.cuspidal (lo := 1) (hi := 2) one_pos
  have hL2 : ∀ f : T.realization.Space, MemLp (OperatorDeterminantSlice.toQuotient F (r + 1)
      T.realization f) 2 ((OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)).restrict
        (OperatorDeterminantSlice.band F (r + 1))) := fun f =>
    OperatorDeterminantSlice.memLp_band_of_cover F (r + 1) T.realization t ht
      (fun x hx => hcover x hx.1 hx.2) f (hfinite _ f)
  exact isJointlyAdmissible_of_separating T.irreducible
    (OperatorDeterminantSlice.unitaryForm F (r + 1) T.realization (Nat.succ_ne_zero r)
      T.cuspidal χ hχ hTχ hL2)
    (separating_of_bandNorm T.realization hSF (Nat.succ_ne_zero r) T.cuspidal χ hχ hTχ _
      (bandNorm_eq_ofReal_inner T.realization (Nat.succ_ne_zero r) T.cuspidal χ hχ hTχ hL2))

/-- **Contragredient existence**, given Siegel finiteness. -/
theorem contragredientExistence_of_siegelFiniteness
    (hSF : PrimitiveAdelicHeight.SiegelSetGLFinitenessStatement.{uF}) :
    CuspidalUnitaryContragredientExistenceStatement.{uF} :=
  contragredientExistence_of_isJointlyAdmissible fun _ _ _ _ _ T hT =>
    isJointlyAdmissible_of_siegelFiniteness hSF T hT

end Langlands.Automorphic.CuspidalAdmissible
