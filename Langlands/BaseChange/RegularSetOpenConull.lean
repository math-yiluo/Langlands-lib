import Langlands.Analysis.Local.PolynomialZeroSet
import Langlands.Analysis.Local.UnitsHaarNull
import Langlands.BaseChange.CyclicAlgebraTopology
import Langlands.BaseChange.FiniteAlgebraUnits
import Langlands.BaseChange.RegularLocusPolynomial
import Langlands.BaseChange.RegularSetOpenConullStatement
import Langlands.BaseChange.SigmaLiftCharacterIdentity.RegularOpen
import Langlands.LocalField.NonzeroParameter

/-! # Openness and Haar conullity of the regular loci -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Set _root_.Topology Langlands.Analysis Langlands.JacquetLanglands

universe u v

/-- Over a cyclic algebra, the σ-regular set is open with null complement for every
Borel Haar measure on the general linear group. -/
theorem sigmaRegularOpenConull : SigmaRegularOpenConullStatement.{u, v} := by
  intro F _ _ _ _ E _ _ _ _ _ σ l n hE
  have : Module.Finite F E := hE.1
  have := LocalFieldTopology.t2Space F
  have := LocalFieldTopology.secondCountableTopology F
  have := Langlands.LocalField.nhdsNE_zero_neBot F
  have : Infinite F := infinite_univ_iff.mp (infinite_of_mem_nhds (0 : F) Filter.univ_mem)
  have := generalLinear_locallyCompactSpace_of_finite F E n
  have := generalLinear_secondCountable_of_finiteAlgebra (F := F) (E := E) n
  refine ⟨SigmaLiftCharacterIdentity.sigmaRegularOpen_of_cyclicNormLemma
    cyclicNormLemma F E σ l n hE, ?_⟩
  let : MeasurableSpace (GeneralLinear n E) := borel _
  have : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  intro μ hμ
  let R := Matrix (Fin n) (Fin n) E
  have := finiteAlgebra_locallyCompactSpace F E
  have : SecondCountableTopology E := (finiteAlgebraCoordinates (F := F) (E := E)).secondCountableTopology
  have : LocallyCompactSpace R := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → E))
  have : SecondCountableTopology R := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → E))
  have : Module.Finite F R := inferInstanceAs (Module.Finite F (Fin n → Fin n → E))
  have : IsModuleTopology F R := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  let : MeasurableSpace R := borel R
  have : BorelSpace R := ⟨rfl⟩
  let m := Module.finrank F R
  let b : Module.Basis (Fin m) F R := Module.finBasis F R
  let e : R ≃L[F] (Fin m → F) :=
    { toLinearEquiv := b.equivFun
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  obtain ⟨p, hp, hregular⟩ := exists_sigmaRegular_polynomial hE b
  let νF : Measure F := Measure.addHaar
  have : νF.IsAddHaarMeasure := inferInstanceAs (Measure.addHaar : Measure F).IsAddHaarMeasure
  let νcoords : Measure (Fin m → F) := Measure.pi fun _ => νF
  have : νcoords.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let ν : Measure R := νcoords.map e.symm
  have : ν.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map νcoords
  let Z : Set R := {M | MvPolynomial.eval (e M) p = 0}
  have hZ : MeasurableSet Z :=
    (isClosed_eq ((MvPolynomial.continuous_eval p).comp e.continuous) continuous_const).measurableSet
  have hν : ν Z = 0 := by
    change Measure.map e.symm νcoords Z = 0
    rw [Measure.map_apply e.symm.continuous.measurable hZ]
    have hpre : e.symm ⁻¹' Z = {x | MvPolynomial.eval x p = 0} := by
      ext x
      change MvPolynomial.eval (e (e.symm x)) p = 0 ↔ MvPolynomial.eval x p = 0
      rw [e.apply_symm_apply]
    rw [hpre]
    simpa only [not_not] using ae_iff.mp (ae_eval_ne_zero νF m p hp)
  have hZunits : {δ : GeneralLinear n E | ¬ IsSigmaRegular σ l δ} =
      (Units.val : Rˣ → R) ⁻¹' Z := by
    ext δ
    change (¬ IsSigmaRegular σ l δ) ↔ MvPolynomial.eval (b.equivFun (δ : R)) p = 0
    rw [hregular δ, not_not]
  rw [hZunits]
  exact measure_preimage_unitsVal_eq_zero ν μ
    (finiteAlgebra_isOpenEmbedding_unitsVal (F := F) (A := R)).isOpen_range hZ hν

private theorem isSigmaRegular_one_iff {F : Type u} [Field F] {n : ℕ}
    (δ : GeneralLinear n F) :
    IsSigmaRegular (1 : F ≃ₐ[F] F) 1 δ ↔ IsRegularSemisimple δ := by
  have hbase (γ : GeneralLinear n F) : baseChange F F n γ = γ := by
    apply Units.ext
    ext i j
    simp [baseChange_apply_apply]
  have hnorm : cyclicNorm (1 : F ≃ₐ[F] F) 1 δ = δ := by
    simp [cyclicNorm_succ, entrywiseAut_one_apply]
  constructor
  · rintro ⟨γ, ⟨g, hg⟩, hγ⟩
    rw [hnorm, hbase] at hg
    apply (isRegularSemisimple_conj_iff g δ).mp
    exact hg.symm ▸ hγ
  · intro hδ
    exact ⟨δ, ⟨1, by simp [hnorm, hbase]⟩, hδ⟩

/-- The ordinary regular semisimple locus is open with Haar null complement. -/
theorem regularSemisimpleOpenConull : RegularSemisimpleOpenConullStatement.{u} := by
  intro F _ _ _ _ n
  simpa only [isSigmaRegular_one_iff] using
    sigmaRegularOpenConull.{u, u} F F 1 1 n (isCyclicAlgebra_one (F := F))

end Langlands.BaseChange
