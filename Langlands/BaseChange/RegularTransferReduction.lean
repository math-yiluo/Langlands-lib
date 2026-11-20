import Langlands.BaseChange.CyclicAlgebraTopology
import Langlands.BaseChange.RegularOrbitalProfiles
import Langlands.BaseChange.RegularTransferStatement

noncomputable section

open Set MeasureTheory Topology

namespace Langlands.BaseChange

open Langlands.HarmonicAnalysis Langlands.JacquetLanglands
open Langlands.QuotientIntegration Langlands.TraceFormula
open Langlands.Topology (IsLocallyProfinite isLocallyProfinite_of_mathlib)

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

/-- The regular orbital-integral profiles, with associated normalizations and
common orbit parameters. The ambient groups and measures are those of the transfer statement. -/
def RegularTransferProfileExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l →
    ∀ [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
      [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
      (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
      (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure],
    ∃ (mF : RegularOrbitalMeasures (MonoidHom.id _) μF {γ | IsRegularSemisimple γ})
      (mE : RegularOrbitalMeasures (entrywiseAut σ n).toMonoidHom μE {δ | IsSigmaRegular σ l δ})
      (pF : {γ : GeneralLinear n F // IsRegularSemisimple γ} → Fin n → F)
      (pE : {δ : GeneralLinear n E // IsSigmaRegular σ l δ} → Fin n → F),
      RegularOrbitalProfileData mF pF ∧ RegularOrbitalProfileData mE pE ∧
      (∀ δ γ, pE δ = pF γ ↔ IsNormAssociated σ l (δ : GeneralLinear n E) γ) ∧
      (∀ (δ : {δ : GeneralLinear n E // IsSigmaRegular σ l δ})
        (γ : {γ : GeneralLinear n F // IsRegularSemisimple γ}),
        IsNormAssociated σ l (δ : GeneralLinear n E) γ →
        IsAssociatedMeasure (n := n) σ l (δ : GeneralLinear n E) (γ : GeneralLinear n F)
          (mE.centralizer δ) (mF.centralizer γ))

/-- An ordinary regular semisimple element has commutative centralizer after
extension of scalars to a commutative algebra. -/
def RegularTransferCommutativeCentralizersStatement : Prop :=
  ∀ (F : Type u) [Field F] (E : Type v) [CommRing E] [Algebra F E]
    (n : ℕ) (γ : GeneralLinear n F), IsRegularSemisimple γ →
    ∀ a b : GeneralLinear n E, Commute a (baseChange F E n γ) →
      Commute b (baseChange F E n γ) → Commute a b

/-- Conditional reduction to the profile and centralizer inputs. -/
def RegularTransferReductionStatement : Prop :=
  RegularTransferProfileExistenceStatement.{u, v} →
  RegularTransferCommutativeCentralizersStatement.{u, v} →
  RegularTransferStatement.{u, v}

theorem regularTransferReduction : RegularTransferReductionStatement.{u, v} := by
  intro hprofile hcentralizer F _ _ _ _ _ E _ _ _ _ _ σ l n hcyc _ _ _ _ μF _ μE _
  let : Module.Finite F E := hcyc.1
  let : T2Space F := LocalFieldTopology.t2Space F
  let : SecondCountableTopology F := LocalFieldTopology.secondCountableTopology F
  let : TotallyDisconnectedSpace F := LocalFieldTopology.totallyDisconnectedSpace F
  let : T2Space E := (finiteAlgebraCoordinates (F := F) (E := E)).symm.t2Space
  let : T2Space (GeneralLinear n F) := LocalFieldTopology.generalLinear_t2Space F n
  let : LocallyCompactSpace (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let : TotallyDisconnectedSpace (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  let : SecondCountableTopology (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_secondCountableTopology F n
  let : SecondCountableTopology (GeneralLinear n E) :=
    generalLinear_secondCountable_of_finiteAlgebra (F := F) n
  have hF : IsLocallyProfinite (GeneralLinear n F) := isLocallyProfinite_of_mathlib
  have hE : IsLocallyProfinite (GeneralLinear n E) :=
    generalLinear_isLocallyProfinite_of_finiteAlgebra (F := F) n
  let : T2Space (GeneralLinear n E) := hE.t2Space
  let : LocallyCompactSpace (GeneralLinear n E) := hE.locallyCompactSpace
  have hθ := continuous_entrywiseAut σ n
  obtain ⟨mF, mE, pF, pE, dF, dE, hparam, hassoc⟩ :=
    hprofile F E σ l n hcyc μF μE
  have hconcord (φ : SchwartzBruhat (GeneralLinear n E)) (f : SchwartzBruhat (GeneralLinear n F))
      (heq : ∀ (d : {δ : GeneralLinear n E // IsSigmaRegular σ l δ})
        (g : {γ : GeneralLinear n F // IsRegularSemisimple γ}),
        IsNormAssociated σ l (d : GeneralLinear n E) g →
        sigmaOrbitalIntegral σ n d (mE.quotient d) φ =
          orbitalIntegral (g : GeneralLinear n F) (mF.quotient g) f)
      (δ : GeneralLinear n E) (γ : GeneralLinear n F)
      (ha : IsNormAssociated σ l δ γ) (hg : IsRegularSemisimple γ) :
      ConcordAt σ l μF μE φ f δ γ := by
    let d : {δ : GeneralLinear n E // IsSigmaRegular σ l δ} := ⟨δ, ⟨γ, ha, hg⟩⟩
    let g : {γ : GeneralLinear n F // IsRegularSemisimple γ} := ⟨γ, hg⟩
    let μδ : Measure (sigmaCentralizer σ n δ) := mE.centralizer d
    let μγ : Measure (glCentralizer γ) := mF.centralizer g
    let : μδ.IsHaarMeasure := mE.haar d
    let : μδ.IsMulRightInvariant := mE.rightInvariant d
    let : μγ.IsHaarMeasure := mF.haar g
    let : μγ.IsMulRightInvariant := mF.rightInvariant g
    have hc := isClosed_twistedCentralizer (MonoidHom.id (GeneralLinear n F)) continuous_id γ
    have hj : MeasurableEmbedding (fun t : glCentralizer γ => baseChange F E n t) :=
      ((hcyc.isClosedEmbedding_baseChange n).comp hc.isClosedEmbedding_subtypeVal).measurableEmbedding
    exact ConcordAt.of_associated_pair (μδ := μδ) (μγ := μγ)
      hcyc.pow_eq_one hθ (hcentralizer F E n γ hg) hj
      (mE.compatible d) (mF.compatible g) (hassoc d g ha) (heq d g ha)
  constructor
  · intro φ hφ
    obtain ⟨P, hP, hφval⟩ := dE.exists_profile (f := φ) hφ
    have hP' : Function.support P ⊆ range pF := by
      intro b hb
      obtain ⟨d, rfl⟩ := hP hb
      obtain ⟨γ, ha, hg⟩ := d.property
      exact ⟨⟨γ, hg⟩, ((hparam d ⟨γ, hg⟩).mpr ha).symm⟩
    obtain ⟨f, hf, hfval⟩ := dF.exists_test hF continuous_id P hP'
    refine ⟨f, hf, ?_, hconcord φ f ?_⟩
    · intro γ hg hn μγ _ _ νγ hc
      let g : {γ : GeneralLinear n F // IsRegularSemisimple γ} := ⟨γ, hg⟩
      have hout : pF g ∉ range pE := by
        rintro ⟨d, hd⟩
        exact hn ⟨d, (hparam d g).mp hd⟩
      have hz : P (pF g) = 0 := by
        by_contra hp
        exact hout (hP hp)
      let : (mF.centralizer g).IsHaarMeasure := mF.haar g
      let : (mF.centralizer g).IsMulRightInvariant := mF.rightInvariant g
      exact orbitalIntegral_eq_zero_of_compatible (mF.compatible g) hc ((hfval g).trans hz)
    · intro d g ha
      have hp := (hparam d g).mpr ha
      exact (hφval d).symm.trans ((congrArg P hp).trans (hfval g).symm)
  · intro f hf hv
    obtain ⟨P, hP, hfval⟩ := dF.exists_profile (f := f) hf
    have hP' : Function.support P ⊆ range pE := by
      intro b hb
      obtain ⟨g, rfl⟩ := hP hb
      by_contra hout
      have hnon : ¬ IsNorm σ l (g : GeneralLinear n F) := by
        rintro ⟨δ, ha⟩
        let d : {δ : GeneralLinear n E // IsSigmaRegular σ l δ} := ⟨δ, ⟨g, ha, g.property⟩⟩
        exact hout ⟨d, (hparam d g).mpr ha⟩
      let : (mF.centralizer g).IsHaarMeasure := mF.haar g
      let : (mF.centralizer g).IsMulRightInvariant := mF.rightInvariant g
      apply hb
      exact (hfval g).trans
        (hv g g.property hnon (mF.centralizer g) (mF.quotient g) (mF.compatible g))
    obtain ⟨φ, hφ, hφval⟩ := dE.exists_test hE hθ P hP'
    refine ⟨φ, hφ, hv, hconcord φ f ?_⟩
    intro d g ha
    have hp := (hparam d g).mpr ha
    exact (hφval d).trans ((congrArg P hp).trans (hfval g))

end Langlands.BaseChange
