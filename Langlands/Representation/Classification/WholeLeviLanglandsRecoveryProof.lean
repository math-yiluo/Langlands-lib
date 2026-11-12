import Langlands.Representation.Classification.WholeLeviLanglandsRecoveryStatement
import Langlands.Representation.Classification.WholeLeviTemperedFactorizationProof
import Langlands.Representation.Classification.WholeLeviQuotientUniverse
import Langlands.Representation.Classification.RegularLanglandsParameterProof
import Langlands.Representation.Classification.RegularLanglandsTensorRecoveryProof
import Langlands.Representation.Classification.RegularLanglandsRecovery

/-! Recovery of arbitrary whole-Levi Langlands data with independent universes. -/

noncomputable section

namespace Langlands

open CategoryTheory WholeLeviQuotientUniverse

universe uF uV uW uJ uK

/-- Equivalent arbitrary irreducible quotients recover the ordered shape,
real parameter and untwisted whole-Levi input in all five independent universes. -/
theorem glWholeLeviLanglandsRecovery :
    GLWholeLeviLanglandsRecoveryStatement.{uF, uV, uW, uJ, uK} := by
  intro p _ F T
  let := T.topology
  intro n hn B C σ τ hσ hσT hτ hτT t u ht hu J K hJ hK hqJ hqK hJK
  obtain ⟨A, hA, _hAdmissible, hAT, ⟨eσ⟩⟩ :=
    glWholeLeviTemperedFactorization.{uF, uV} p F T n hn B σ hσ hσT
  obtain ⟨D, hD, _hDadmissible, hDT, ⟨eτ⟩⟩ :=
    glWholeLeviTemperedFactorization.{uF, uW} p F T n hn C τ hτ hτT
  obtain ⟨qJ, hqJ⟩ := hqJ
  obtain ⟨qK, hqK⟩ := hqK
  have hJs : IsSmooth J.ρ :=
    isSmooth_of_surjective_induced T B _ J qJ hqJ
  have hKs : IsSmooth K.ρ :=
    isSmooth_of_surjective_induced T C _ K qK hqK
  let d := liftedDatum.{uF, uV, uJ, max uW uK} T B A hA hAT t ht
  let e := liftedDatum.{uF, uW, uK, max uV uJ} T C D hD hDT u hu
  let π := quotientLift.{uF, uV, uJ, max uW uK} T J hJs
  let κ := quotientLift.{uF, uW, uK, max uV uJ} T K hKs
  have hπ : d.IsLanglandsQuotient π :=
    isLanglandsQuotient_quotientLift.{uF, uV, uJ, max uW uK}
      T B A hA hAT t ht σ eσ J qJ hqJ hJ
  have hκ : e.IsLanglandsQuotient κ :=
    isLanglandsQuotient_quotientLift.{uF, uW, uK, max uV uJ}
      T C D hD hDT u hu τ eτ K qK hqK hK
  obtain ⟨E⟩ := hJK
  have hπκ : Nonempty (π ≅ κ) :=
    ⟨quotientLiftIso.{uF, uV, uW, uJ, uK, 0}
      T J K hJs hKs E⟩
  obtain ⟨a, ha⟩ :=
    glRegularLanglandsParameterUniqueness.{uF, max uV uW uJ uK}
      p F T n hn d e π κ hπ hκ hπκ
  have hShape : B = C :=
    GeneralLinear.BlockShape.eq_of_orderIso B C a (fun i => (ha i).1)
  refine ⟨hShape, ?_⟩
  cases hShape
  change t = u ∧ Nonempty (σ.ρ.Equiv τ.ρ)
  have haId : a = OrderIso.refl (Fin B.length) := Subsingleton.elim _ _
  have htu : t = u := by
    funext i
    have hi : t i = u (a i) := (ha i).2
    rw [haId] at hi
    exact hi
  refine ⟨htu, ?_⟩
  subst u
  exact fixedRegularLeviRecovery T hn B σ τ hσ hσT hτ hτT t ht J hJ
    qJ hqJ (E.symm.toIntertwiningMap.comp qK) (E.symm.surjective.comp hqK)

end Langlands
