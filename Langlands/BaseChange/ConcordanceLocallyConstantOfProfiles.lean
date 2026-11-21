import Langlands.BaseChange.CyclicNormLemma
import Langlands.BaseChange.RegularCyclicBasis
import Langlands.BaseChange.RegularSemisimpleOrbit
import Langlands.BaseChange.RegularTransferReduction
import Langlands.BaseChange.SigmaLiftCharacterIdentity.Parameters

/-! # Local constancy of exact concordance from regular orbital profiles -/

noncomputable section

namespace Langlands.BaseChange

open Set MeasureTheory _root_.Topology
open Langlands.HarmonicAnalysis Langlands.JacquetLanglands
open Langlands.QuotientIntegration Langlands.TraceFormula
open Langlands.Topology (IsLocallyProfinite isLocallyProfinite_of_mathlib)
open SigmaLiftCharacterIdentity (coefficients coefficients_conj coefficients_associated
  coefficients_cyclicNorm_conj charpoly_eq_of_baseChange_coefficients continuous_coefficients
  continuous_cyclicNorm continuous_entrywiseAut)

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

section InvariantCutoff

variable {G B A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [TopologicalSpace B] [TopologicalSpace A] [T2Space A]
  {θ : G →* G} {μ : Measure G} {R : Set G}
  {m : RegularOrbitalMeasures θ μ R} {p : R → B}

/-- Extend local constancy from regularly supported tests to arbitrary tests
by cutting off along ambient invariant parameters near a regular orbit. -/
private theorem locallyConstant_orbitalIntegral_of_profiles
    (d : RegularOrbitalProfileData m p) (hG : IsLocallyProfinite G)
    (a : G → A) (ha : Continuous a)
    (hinv : ∀ (x g : G), a (twistedConj θ x g) = a g)
    (hfiber : ∀ (r : R) (g : G), a g = a r → ∃ x : G, twistedConj θ x (r : G) = g)
    (f : SchwartzBruhat G) :
    IsLocallyConstant (fun r : R => twistedOrbitalIntegral θ (r : G) (m.quotient r) f) := by
  apply (IsLocallyConstant.iff_exists_open _).2
  intro r
  obtain ⟨K, hrK, hKo, hKc, hKR⟩ := hG.2 (r : G) R (d.isOpen.mem_nhds r.property)
  let C := a ⁻¹' (a '' K)
  have hCc : IsClosed C := (hKc.image ha).isClosed.preimage ha
  have hCsat : C = ⋃ x : G, twistedConj θ x '' K := by
    ext g
    constructor
    · rintro ⟨k, hk, hkg⟩
      obtain ⟨x, hx⟩ := hfiber ⟨k, hKR hk⟩ g hkg.symm
      exact mem_iUnion.mpr ⟨x, k, hk, hx⟩
    · intro hg
      obtain ⟨x, k, hk, rfl⟩ := mem_iUnion.mp hg
      exact ⟨k, hk, (hinv x k).symm⟩
  have hCo : IsOpen C := by
    rw [hCsat]
    exact isOpen_iUnion fun x =>
      ((isOpenMap_mul_right (θ x)).comp (isOpenMap_mul_left x⁻¹)) K hKo
  have hCR : C ⊆ R := by
    intro g hg
    obtain ⟨x, k, hk, rfl⟩ := mem_iUnion.mp (hCsat ▸ hg)
    obtain ⟨s, hs, -⟩ := d.orbit ⟨k, hKR hk⟩ x
    exact hs ▸ s.property
  have hrC : (r : G) ∈ C := ⟨r, hrK, rfl⟩
  let fC : G → ℂ := C.indicator f
  have hfl : IsLocallyConstant fC := by
    apply (IsLocallyConstant.iff_eventually_eq _).2
    intro x
    by_cases hx : x ∈ C
    · have hf := (IsLocallyConstant.iff_eventually_eq _).1 f.locallyConstant x
      filter_upwards [hCo.mem_nhds hx, hf] with y hy hfy
      simpa only [fC, Set.indicator_of_mem hy, Set.indicator_of_mem hx] using hfy
    · filter_upwards [hCc.isOpen_compl.mem_nhds hx] with y hy
      simp only [fC, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  have hfs : Function.support fC ⊆ Function.support f := by
    intro x hx
    by_contra hz
    exact hx (Set.indicator_apply_eq_zero.mpr fun _ => by simpa [Function.mem_support] using hz)
  let f' : SchwartzBruhat G := ⟨fC, hfl, f.hasCompactSupport.mono hfs⟩
  have hf' : Function.support f' ⊆ R := fun _ hx => hCR (Set.support_indicator_subset hx)
  have hval (s : R) (hs : (s : G) ∈ C) :
      twistedOrbitalIntegral θ (s : G) (m.quotient s) f' =
      twistedOrbitalIntegral θ (s : G) (m.quotient s) f := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      have hx : twistedConj θ x (s : G) ∈ C := by
        change a (twistedConj θ x (s : G)) ∈ a '' K
        rwa [hinv]
      exact Set.indicator_of_mem hx _
  obtain ⟨U, hUo, hrU, hU⟩ := (d.locallyConstant f' hf').exists_open r
  refine ⟨U ∩ Subtype.val ⁻¹' C, hUo.inter (hCo.preimage continuous_subtype_val),
    ⟨hrU, hrC⟩, fun s hs => ?_⟩
  rw [← hval s hs.2, ← hval r hrC]
  exact hU s hs.1

end InvariantCutoff

section Fibers

variable {F : Type u} {E : Type v} [Field F] [CommRing E] [Algebra F E]
  {n l : ℕ} {σ : E ≃ₐ[F] E}

private theorem exists_conj_of_coefficients_eq {γ g : GeneralLinear n F}
    (hγ : IsRegularSemisimple γ) (hg : coefficients g = coefficients γ) :
    ∃ x : GeneralLinear n F, x⁻¹ * γ * x = g := by
  have hpoly := Distribution.charpoly_eq_of_coeff_eq
    (g : Matrix (Fin n) (Fin n) F) (γ : Matrix (Fin n) (Fin n) F) (congrFun hg)
  obtain ⟨y, hy⟩ := exists_matrix_conj_of_charpoly_eq_of_separable _ _ hγ hpoly
  refine ⟨y⁻¹, ?_⟩
  simpa only [inv_inv] using (Units.ext hy : y * γ * y⁻¹ = g)

private theorem exists_twistedConj_of_norm_coefficients_eq
    (hσ : IsCyclicAlgebra σ l) {δ g : GeneralLinear n E}
    (hδ : IsSigmaRegular σ l δ) (hg : coefficients (cyclicNorm σ l g) =
      coefficients (cyclicNorm σ l δ)) :
    ∃ x : GeneralLinear n E, x⁻¹ * δ * entrywiseAut σ n x = g := by
  obtain ⟨γ, hδγ, hγ⟩ := hδ
  obtain ⟨γ', hgγ'⟩ := (cyclicNormLemma F E σ l n hσ).1 g
  have hcoeff : coefficients (baseChange F E n γ') = coefficients (baseChange F E n γ) := by
    rw [← coefficients_associated hgγ', ← coefficients_associated hδγ, hg]
  have hpoly := charpoly_eq_of_baseChange_coefficients hσ hcoeff
  have hc : coefficients γ' = coefficients γ :=
    funext fun i => congrArg (fun p : Polynomial F => p.coeff i.val) hpoly
  obtain ⟨b, hb⟩ := exists_conj_of_coefficients_eq hγ hc
  obtain ⟨x, hx⟩ := hδγ
  obtain ⟨y, hy⟩ := hgγ'
  refine (cyclicNormLemma F E σ l n hσ).2.2 δ g ⟨x * baseChange F E n b * y⁻¹, ?_⟩
  calc
    _ = y * ((baseChange F E n b)⁻¹ * (x⁻¹ * cyclicNorm σ l δ * x) *
        baseChange F E n b) * y⁻¹ := by group
    _ = y * baseChange F E n γ' * y⁻¹ := by
      rw [hx, ← map_inv, ← map_mul, ← map_mul, hb]
    _ = cyclicNorm σ l g := by rw [← hy]; group

end Fibers

/-- Regular orbital profiles imply local constancy of the truth value of
`ConcordAt` on associated regular pairs for arbitrary Schwartz–Bruhat tests. -/
def ConcordanceLocallyConstantOfProfilesStatement : Prop :=
  RegularTransferProfileExistenceStatement.{u, v} →
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l →
    ∀ [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
      [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
      (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
      (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure]
      (φ : SchwartzBruhat (GeneralLinear n E)) (f : SchwartzBruhat (GeneralLinear n F)),
      let D := {q : GeneralLinear n E × GeneralLinear n F //
        IsNormAssociated σ l q.1 q.2 ∧ IsRegularSemisimple q.2}
      IsLocallyConstant (fun q : D => ConcordAt σ l μF μE φ f q.val.1 q.val.2)

set_option maxHeartbeats 950000 in
theorem concordanceLocallyConstantOfProfiles : ConcordanceLocallyConstantOfProfilesStatement.{u, v} := by
  intro hprofile F _ _ _ _ _ E _ _ _ _ _ σ l n hσ _ _ _ _ μF _ μE _ φ f
  let : Module.Finite F E := hσ.1
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
  obtain ⟨mF, mE, pF, pE, dF, dE, _, hAssoc⟩ := hprofile F E σ l n hσ μF μE
  let D := {q : GeneralLinear n E × GeneralLinear n F //
    IsNormAssociated σ l q.1 q.2 ∧ IsRegularSemisimple q.2}
  let lower (q : D) : {γ : GeneralLinear n F // IsRegularSemisimple γ} :=
    ⟨q.val.2, q.property.2⟩
  let upper (q : D) : {δ : GeneralLinear n E // IsSigmaRegular σ l δ} :=
    ⟨q.val.1, q.val.2, q.property.1, q.property.2⟩
  have hLower : Continuous lower := continuous_subtype_val.snd.subtype_mk _
  have hUpper : Continuous upper := continuous_subtype_val.fst.subtype_mk _
  have hFconst := locallyConstant_orbitalIntegral_of_profiles dF hF coefficients
    continuous_coefficients coefficients_conj
    (fun r g hg => exists_conj_of_coefficients_eq r.property hg) f
  have hEconst := locallyConstant_orbitalIntegral_of_profiles dE hE
    (coefficients ∘ cyclicNorm σ l) (continuous_coefficients.comp (continuous_cyclicNorm σ l))
    (coefficients_cyclicNorm_conj hσ.pow_eq_one)
    (fun r g hg => exists_twistedConj_of_norm_coefficients_eq hσ r.property hg) φ
  have hConst := (hEconst.comp_continuous hUpper).comp₂ (hFconst.comp_continuous hLower) (· = ·)
  have hIff (q : D) : ConcordAt σ l μF μE φ f q.val.1 q.val.2 ↔
      sigmaOrbitalIntegral σ n q.val.1 (mE.quotient (upper q)) φ =
        orbitalIntegral q.val.2 (mF.quotient (lower q)) f := by
    let d := upper q
    let g := lower q
    let μδ : Measure (sigmaCentralizer σ n q.val.1) := mE.centralizer d
    let μγ : Measure (glCentralizer q.val.2) := mF.centralizer g
    let : μδ.IsHaarMeasure := mE.haar d
    let : μδ.IsMulRightInvariant := mE.rightInvariant d
    let : μγ.IsHaarMeasure := mF.haar g
    let : μγ.IsMulRightInvariant := mF.rightInvariant g
    have hAssoc' := hAssoc d g q.property.1
    refine ⟨fun h => h μδ μγ (mE.quotient d) (mF.quotient g)
      (mE.compatible d) (mF.compatible g) hAssoc', ?_⟩
    have hClosed := isClosed_twistedCentralizer (MonoidHom.id (GeneralLinear n F))
      continuous_id q.val.2
    have hj : MeasurableEmbedding (fun t : glCentralizer q.val.2 => baseChange F E n t) :=
      ((hσ.isClosedEmbedding_baseChange n).comp hClosed.isClosedEmbedding_subtypeVal).measurableEmbedding
    exact ConcordAt.of_associated_pair (μδ := μδ) (μγ := μγ)
      hσ.pow_eq_one (continuous_entrywiseAut σ n)
      (fun _ _ ha hb => commute_of_regular_baseChange q.property.2 ha hb) hj
      (mE.compatible d) (mF.compatible g) hAssoc'
  change IsLocallyConstant (fun q : D => ConcordAt σ l μF μE φ f q.val.1 q.val.2)
  rw [show (fun q : D => ConcordAt σ l μF μE φ f q.val.1 q.val.2) =
      (fun q : D => sigmaOrbitalIntegral σ n q.val.1 (mE.quotient (upper q)) φ =
        orbitalIntegral q.val.2 (mF.quotient (lower q)) f) from funext fun q => propext (hIff q)]
  exact hConst

end Langlands.BaseChange
