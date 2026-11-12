import Langlands.Representation.Classification.RegularLanglandsParameterProof
import Langlands.Representation.Classification.RegularLanglandsTensorRecoveryProof
import Langlands.Representation.Classification.RegularLanglandsRecovery

/-! Ordered tempered Langlands data are recovered from arbitrary isomorphic
irreducible quotients of their actual standard modules. -/

noncomputable section

namespace Langlands

open CategoryTheory

universe uF uV

/-- The exact ordered tempered Langlands-data uniqueness statement. -/
theorem glRegularLanglandsDataUniqueness :
    GLRegularLanglandsDataUniquenessStatement.{uF, uV} := by
  intro p hp F T
  let := T.topology
  intro n hn d e π τ hπ hτ hIso
  obtain ⟨a, ha⟩ :=
    glRegularLanglandsParameterUniqueness.{uF, uV} p F T n hn d e π τ hπ hτ hIso
  have hShape : d.shape = e.shape :=
    GeneralLinear.BlockShape.eq_of_orderIso _ _ a (fun i => (ha i).1)
  rcases d with ⟨B, σ, hσ, htσ, t, ht⟩
  rcases e with ⟨B', σ', hσ', htσ', t', ht'⟩
  dsimp only at hShape
  subst B'
  have hOrder : a = OrderIso.refl (Fin B.length) := Subsingleton.elim _ _
  have hExponent : t = t' := by
    funext i
    simpa only [hOrder, OrderIso.refl_apply] using (ha i).2
  subst t'
  obtain ⟨E⟩ := glRegularLanglandsTensorRecovery.{uF, uV}
    p F T n hn B σ σ' hσ hσ' htσ htσ' t ht π τ hπ hτ hIso
  refine ⟨OrderIso.refl _, fun _ => rfl, fun i => ⟨rfl, ?_⟩⟩
  exact ⟨T.blockIsoOfTensorEquiv B σ σ' hσ hσ' E i⟩

end Langlands
