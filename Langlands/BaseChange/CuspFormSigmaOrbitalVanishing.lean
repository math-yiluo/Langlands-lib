import Langlands.BaseChange.CuspFormOrbitalVanishingStatement
import Langlands.BaseChange.LeviTwistedFibre
import Langlands.BaseChange.RegularSemisimpleLevi
import Langlands.BaseChange.RegularLeviNormRepresentative
import Langlands.BaseChange.TwistedOrbitalConjugation
import Langlands.BaseChange.TwistedCharacterRegularValuesReduction

/-!
# σ-orbital integrals of cusp forms vanish off the σ-elliptic set

`cuspFormSigmaOrbitalVanishing` proves `CuspFormSigmaOrbitalVanishingStatement`: for a
nonarchimedean local field `F` of characteristic zero, a field `E` that is a cyclic `F`-algebra
with generator `σ`, and `0 < n`, a Schwartz–Bruhat function on `GL_n(E)` with vanishing constant
terms has vanishing σ-orbital integrals at every σ-regular element that is not σ-elliptic.

The proof moves `δ` by σ-conjugation into a two-block Levi `M(E)` with σ-centralizer in `M(E)`
and applies the abelian fibre vanishing `TwistedFibreData.twistedOrbitalIntegral_eq_zero` to the
unipotent radical of the standard parabolic (`leviTwistedFibreData`). See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure
open Langlands.QuotientIntegration Langlands.TraceFormula Langlands.JacquetLanglands
open Langlands.GeneralLinear Langlands.ProductLeviChamber

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

/-- **σ-orbital integrals of cusp forms vanish off the σ-elliptic set** (Henniart–Lemaire 2011,
II.4.5 (1) and II.5.14). -/
theorem cuspFormSigmaOrbitalVanishing : CuspFormSigmaOrbitalVanishingStatement.{u, v} := by
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hE hn
  have : Module.Finite F E := hE.1
  have := generalLinear_t2Space_of_finite F E n
  have := generalLinear_locallyCompactSpace_of_finite F E n
  let : MeasurableSpace (GeneralLinear n E) := borel _
  have : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  intro μE _ φ hφ δ hreg hell μδ _ _ νδ hν
  have := finiteAlgebra_t2Space F E
  have := generalLinear_secondCountableTopology_of_finite F E n
  have hσ : σ ^ l = 1 := hE.pow_eq_one
  let θ : GeneralLinear n E →* GeneralLinear n E := (entrywiseAut σ n).toMonoidHom
  have hθ : Continuous θ := continuous_entrywiseAut_of_isModuleTopology σ n
  -- a regular semisimple norm, not elliptic, lies in a two-block Levi
  obtain ⟨γ, hγa, hγr⟩ := hreg
  have hγe : ¬ IsRegularElliptic γ := fun h => hell ⟨γ, hγa, h⟩
  obtain ⟨k, hk, hkn, g, m, hgm, -⟩ :=
    exists_twoBlock_of_regularSemisimple_of_not_regularElliptic hn γ hγr hγe
  let B := twoBlock n k hk hkn
  have ha : IsNormAssociated σ l δ (B.leviEmbedding F m) := by
    have h := hγa.twistedConj hσ 1 g
    rwa [inv_one, one_mul, map_one, mul_one, hgm] at h
  have hr : IsRegularSemisimple (B.leviEmbedding F m) := by
    rw [← hgm]
    exact (isRegularSemisimple_conj_iff g γ).2 hγr
  -- a σ-conjugate of `δ` in `M(E)` with exact norm, whose σ-centralizer lies in `M(E)`
  obtain ⟨x, d, hxd, hd⟩ := regularLeviNormRepresentative F E σ l n hσ B m δ ha hr
  let δ' := twistedConj θ x δ
  have hδ'eq : δ' = B.leviEmbedding E d := hxd
  have hN : cyclicNorm σ l δ' = baseChange F E n (B.leviEmbedding F m) := by
    rw [hδ'eq, cyclicNorm_leviEmbedding, baseChange_leviEmbedding]
    congr 1
    funext i
    exact (hd i).1
  have hH : twistedCentralizer θ δ' ≤ B.leviSubgroup E :=
    sigmaCentralizer_le_leviSubgroup_of_regularNorm B hσ hN hr
  have hδM : δ' ∈ B.leviSubgroup E := ⟨d, hδ'eq.symm⟩
  have hB : B.length ≤ 2 := le_rfl
  let D := leviTwistedFibreData B σ δ' hB hδM hH
  -- transport of the measures to `δ'`
  let eδ := twistedCentralizerConj θ δ x
  let μD : Measure (twistedCentralizer θ δ) := μδ
  have : μD.IsHaarMeasure := inferInstanceAs μδ.IsHaarMeasure
  have : μD.IsMulRightInvariant := inferInstanceAs μδ.IsMulRightInvariant
  let μD' : Measure (twistedCentralizer θ δ') := Measure.map eδ μD
  have : μD'.IsHaarMeasure := eδ.isHaarMeasure_map μD
  have : μD'.IsMulRightInvariant := isMulRightInvariant_map eδ μD
  have hν' := isCompatible_map_twistedConj θ δ x μD μD' μE rfl νδ hν
  have key : twistedOrbitalIntegral θ δ' (Measure.map (twistedOrbitQuotientConj θ δ x) νδ) φ = 0 := by
    refine D.twistedOrbitalIntegral_eq_zero hθ
      (leviTwistedFibreData_twist_surjective B σ δ' hB hδM hH) φ.continuous ?_ μE μD' _ hν'
    intro μ hμ y z
    exact (hφ B le_rfl μ hμ).2 y z
  exact (twistedOrbitalIntegral_map_conj θ δ x νδ φ).2.symm.trans key

end Langlands.BaseChange
