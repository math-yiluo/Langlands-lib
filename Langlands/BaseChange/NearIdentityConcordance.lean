import Langlands.BaseChange.CongruenceTwistedDescent
import Langlands.BaseChange.ConcordanceConjugation
import Langlands.BaseChange.CyclicNormLemma
import Langlands.BaseChange.NormPolynomialPerturbation
import Langlands.BaseChange.RegularCyclicTwistedOrbit
import Langlands.BaseChange.RegularCentralizer
import Langlands.BaseChange.RegularTransferMeasures
import Langlands.Analysis.Local.QuotientCompactOpenDescent
import Langlands.Group.GL.LocalFieldTopology
import Langlands.HarmonicAnalysis.Basic

/-!
# Matching through a descent subgroup (the core of matching near the identity)

For a nonarchimedean local field `F`, a cyclic field extension `E` of `F` with generator `σ` of
order `l` (`IsCyclicAlgebra σ l`, `E` with the module topology) and Haar measures `μF`, `μE` on
`GL_n(F)`, `GL_n(E)`: let `K` be a compact open subgroup of `GL_n(E)` on which σ-conjugacy and
`l`-th powers descend (`IsTwistedDescentSubgroup F σ l K`). If a Schwartz–Bruhat function `φ` on
`GL_n(E)` is supported on the σ-conjugates `κ⁻¹ u κ^σ` (`κ ∈ K`, `u ∈ K ∩ GL_n(F)`), a
Schwartz–Bruhat function `f` on `GL_n(F)` is supported on the `l`-th powers of `K ∩ GL_n(F)`, and
`∫_{K ∩ GL_n(F)} f (κ⁻¹ u^l κ) dμF = ∫_K φ (κ⁻¹ u κ^σ) dμE` for all `u ∈ K ∩ GL_n(F)`, then `φ` and
`f` are concordant in the sense of Henniart–Lemaire (`areConcordant_of_integral_eq`).

On the way: `ConcordAt.of_twistedConj` (concordance at a σ-conjugate gives concordance at `δ`),
`twistedOrbitalIntegral_eq_zero_of_forall`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Set _root_.Topology
open Langlands.QuotientIntegration Langlands.TraceFormula Langlands.JacquetLanglands
open Langlands.HarmonicAnalysis

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

section Transport

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
variable {σ : E ≃ₐ[F] E} {l n : ℕ}
variable [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
variable [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]

/-- Concordance at a σ-conjugate of `δ` gives concordance at `δ`. -/
theorem ConcordAt.of_twistedConj (hσ : σ ^ l = 1)
    {μF : Measure (GeneralLinear n F)} {μE : Measure (GeneralLinear n E)} [μE.IsMulLeftInvariant]
    {φ : GeneralLinear n E → ℂ} {f : GeneralLinear n F → ℂ} {δ : GeneralLinear n E}
    {γ : GeneralLinear n F} (t : GeneralLinear n E)
    (h : ConcordAt σ l μF μE φ f (twistedConj (entrywiseAut σ n) t δ) γ) :
    ConcordAt σ l μF μE φ f δ γ := by
  intro μδ _ _ μγ _ _ νδ νγ hδ hγ hassoc
  obtain ⟨x, hx, hμ⟩ := hassoc
  let θ := entrywiseAut σ n
  let eδ := twistedCentralizerConj θ t δ
  let μδ' := Measure.map eδ μδ
  let νδ' := Measure.map (twistedQuotientConj θ t δ) νδ
  have hHaar : μδ'.IsHaarMeasure := eδ.isHaarMeasure_map μδ
  have hRight : μδ'.IsMulRightInvariant := map_twistedCentralizerConj_isMulRightInvariant θ t δ μδ
  have hδ' : IsCompatible (sigmaCentralizer σ n (twistedConj θ t δ)) μE μδ' νδ' :=
    isCompatible_twistedQuotientConj θ t δ μδ μE νδ hδ
  have hassoc' : IsAssociatedMeasure σ l (twistedConj θ t δ) γ μδ' μγ := by
    refine ⟨t⁻¹ * x, ?_, ?_⟩
    · rw [twistedConj_apply, cyclicNorm_twistedConj, hσ, entrywiseAut_one_apply, ← hx]
      group
    · have heδ : Measurable (eδ : _ → _) := eδ.continuous.measurable
      have hm : Measurable fun c : sigmaCentralizer σ n (twistedConj θ t δ) =>
          (t⁻¹ * x)⁻¹ * (c : GeneralLinear n E) * (t⁻¹ * x) :=
        ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
      rw [Measure.map_map hm heδ, ← hμ]
      congr 1
      funext c
      change (t⁻¹ * x)⁻¹ * (t⁻¹ * c.val * t) * (t⁻¹ * x) = x⁻¹ * c.val * x
      group
  calc sigmaOrbitalIntegral σ n δ νδ φ
      = sigmaOrbitalIntegral σ n (twistedConj θ t δ) νδ' φ :=
        (twistedOrbitalIntegral_twistedQuotientConj θ t δ νδ φ).symm
    _ = orbitalIntegral γ νγ f := @h μδ' hHaar hRight μγ _ _ νδ' νγ hδ' hγ hassoc'

/-- An orbital integral of a function whose orbit function vanishes is zero. -/
theorem twistedOrbitalIntegral_eq_zero_of_forall {G : Type*} [Group G] {Θ : Type*}
    [FunLike Θ G G] [MonoidHomClass Θ G G] (θ : Θ) (δ : G)
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ))) {f : G → ℂ}
    (hf : ∀ x : G, f (x⁻¹ * δ * θ x) = 0) : twistedOrbitalIntegral θ δ ν f = 0 := by
  have : twistedOrbitFunction θ δ f = 0 := by
    funext q
    induction q using Quotient.inductionOn with
    | h x => exact hf x
  rw [twistedOrbitalIntegral, this]
  simp

end Transport


section Core

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable {E : Type v} [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E]
variable {σ : E ≃ₐ[F] E} {l n : ℕ}
variable [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
variable [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
variable [T2Space F] [T2Space E]
variable [T2Space (GeneralLinear n F)] [LocallyCompactSpace (GeneralLinear n F)]
  [SecondCountableTopology (GeneralLinear n F)]
variable [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [SecondCountableTopology (GeneralLinear n E)]

/-- The core of the matching near the identity at a rational base point `baseChange u`,
`u` in a descent subgroup, with `u ^ l` regular semisimple (source `nearCore`, second half). -/
private theorem concordAt_baseChange (hσ : IsCyclicAlgebra σ l)
    (hj : IsClosedEmbedding (baseChange F E n))
    (hθ : Continuous fun g : GeneralLinear n E => entrywiseAut σ n g)
    {μF : Measure (GeneralLinear n F)} [μF.IsHaarMeasure]
    {μE : Measure (GeneralLinear n E)} [μE.IsHaarMeasure]
    (K : Subgroup (GeneralLinear n E)) (hKo : IsOpen (K : Set (GeneralLinear n E)))
    (hKc : IsCompact (K : Set (GeneralLinear n E))) (hK : IsTwistedDescentSubgroup F σ l K)
    {φ : GeneralLinear n E → ℂ} (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    {f : GeneralLinear n F → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hφ : ∀ g, φ g ≠ 0 → ∃ κ ∈ K, ∃ u : GeneralLinear n F, baseChange F E n u ∈ K ∧
      g = κ⁻¹ * baseChange F E n u * entrywiseAut σ n κ)
    (hf : ∀ γ, f γ ≠ 0 → ∃ u : GeneralLinear n F, baseChange F E n u ∈ K ∧ γ = u ^ l)
    (heq : ∀ u : GeneralLinear n F, baseChange F E n u ∈ K →
      ∫ κ in (K.comap (baseChange F E n) : Set (GeneralLinear n F)), f (κ⁻¹ * u ^ l * κ) ∂μF =
        ∫ κ in (K : Set (GeneralLinear n E)),
          φ (κ⁻¹ * baseChange F E n u * entrywiseAut σ n κ) ∂μE)
    {u : GeneralLinear n F} (hu : baseChange F E n u ∈ K) (hreg : IsRegularSemisimple (u ^ l)) :
    ConcordAt σ l μF μE φ f (baseChange F E n u) (u ^ l) := by
  intro μδ _ _ μγ _ _ νδ νγ hδ hγ hassoc
  let : Module.Finite F E := hσ.1
  let : IsReduced E := hσ.2.2.1
  let j : GeneralLinear n F →* GeneralLinear n E := baseChange F E n
  have hjc : Continuous j := hj.continuous
  have hN : cyclicNorm σ l (baseChange F E n u) = baseChange F E n (u ^ l) := cyclicNorm_baseChange σ l u
  -- the association is through the identity
  obtain ⟨x, hx, hmap⟩ := hassoc
  have hcomm : ∀ a b : GeneralLinear n E, Commute a (baseChange F E n (u ^ l)) →
      Commute b (baseChange F E n (u ^ l)) → Commute a b :=
    fun a b ha hb => commute_of_commute_baseChange hreg ha hb
  have h1 : 1⁻¹ * cyclicNorm σ l (baseChange F E n u) * 1 = baseChange F E n (u ^ l) := by simpa using hN
  have hmap' : μδ.map Subtype.val = μγ.map fun t : glCentralizer (u ^ l) => j t := by
    have hfun : (fun c : sigmaCentralizer σ n (baseChange F E n u) => x⁻¹ * (c : GeneralLinear n E) * x) =
        Subtype.val := by
      funext c
      rw [normConjugator_on_sigmaCentralizer hσ.pow_eq_one hcomm hx h1 c]
      simp
    rw [← hfun]
    exact hmap
  have hS : sigmaCentralizer σ n (baseChange F E n u) = (glCentralizer (u ^ l)).map j := hK.sigmaCentralizer_eq hu
  have hT : IsClosed (glCentralizer (u ^ l) : Set (GeneralLinear n F)) :=
    isClosed_twistedCentralizer (MonoidHom.id _) continuous_id (u ^ l)
  -- the two sides as integrals of descended functions
  let ΦE : GeneralLinear n E → ℂ := fun g => φ (g⁻¹ * (baseChange F E n u) * (entrywiseAut σ n) g)
  have hΦEm : Measurable ΦE :=
    (hφc.comp (((continuous_inv.mul continuous_const).mul hθ))).measurable
  have hΦES : ∀ s : sigmaCentralizer σ n (baseChange F E n u), ∀ g, ΦE (s.val * g) = ΦE g := fun s g => by
    simp only [ΦE]
    rw [twistedConj_left_mul]
  -- support of `ΦE`
  have hsuppE : ∀ g, ΦE g ≠ 0 → ∃ h : GeneralLinear n F, ∃ κ ∈ K, g = j h * κ := by
    intro g hg
    obtain ⟨κ, hκ, u', hu', e⟩ := hφ _ hg
    obtain ⟨z, hz⟩ := hK.rational_of_twistedConj u u' hu hu' (g * κ⁻¹) (by
      rw [map_mul, map_inv]
      calc (g * κ⁻¹)⁻¹ * baseChange F E n u * ((entrywiseAut σ n) g * ((entrywiseAut σ n) κ)⁻¹)
          = κ * (g⁻¹ * (baseChange F E n u) * (entrywiseAut σ n) g) * ((entrywiseAut σ n) κ)⁻¹ := by group
        _ = baseChange F E n u' := by rw [e]; group)
    exact ⟨z, κ, hκ, by rw [show j z = g * κ⁻¹ from hz]; group⟩
  -- integrability of the twisted orbit function
  have hdreg : IsRegularSemisimple (cyclicNorm σ l (baseChange F E n u)) := by
    rw [hN]; exact hreg.baseChange
  have : SigmaCompactSpace (GeneralLinear n E) := inferInstance
  have : SigmaCompactSpace (GeneralLinear n F) := inferInstance
  have hintE : Integrable (descend (sigmaCentralizer σ n (baseChange F E n u)) ΦE hΦES) νδ := by
    obtain ⟨hc, hs⟩ := continuous_hasCompactSupport_cyclicTwistedOrbitFunction hσ
      (baseChange F E n u) φ hdreg hφc hφs
    have := hδ.regular
    exact hc.integrable_of_hasCompactSupport hs
  -- the averages over `K`
  let ΨE : GeneralLinear n F → ℂ := fun h => ∫ κ in (K : Set (GeneralLinear n E)), ΦE (j h * κ) ∂μE
  have hjS : ∀ t : glCentralizer (u ^ l), j t.val ∈ sigmaCentralizer σ n (baseChange F E n u) :=
    fun t => hS ▸ Subgroup.mem_map_of_mem j t.property
  have hΨET : ∀ t : glCentralizer (u ^ l), ∀ h, ΨE (t.val * h) = ΨE h := by
    intro t h
    simp only [ΨE]
    congr 1
    funext κ
    rw [map_mul, mul_assoc]
    exact hΦES ⟨j t.val, hjS t⟩ (j h * κ)
  have hE := hδ.integral_descend_eq_of_compactOpen (Φ := ΦE) j hj K hKo hKc hT hS hmap' hγ
    hΦEm hΦES hsuppE hintE ΨE (fun _ => rfl) hΨET
  -- the ordinary side
  let K' : Subgroup (GeneralLinear n F) := K.comap j
  have hK'o : IsOpen (K' : Set (GeneralLinear n F)) := hKo.preimage hjc
  have hK'c : IsCompact (K' : Set (GeneralLinear n F)) := hj.isCompact_preimage hKc
  let ΦF : GeneralLinear n F → ℂ := fun g => f (g⁻¹ * u ^ l * (MonoidHom.id _) g)
  have hΦFm : Measurable ΦF :=
    (hfc.comp ((continuous_inv.mul continuous_const).mul continuous_id)).measurable
  have hΦFS : ∀ s : glCentralizer (u ^ l), ∀ g, ΦF (s.val * g) = ΦF g := fun s g => by
    simp only [ΦF]
    rw [twistedConj_left_mul]
  have hintF : Integrable (descend (glCentralizer (u ^ l)) ΦF hΦFS) νγ := by
    have hs := hasCompactSupport_regularSemisimpleOrbitFunction (u ^ l) hreg hfs
    have hc : Continuous (descend (glCentralizer (u ^ l)) ΦF hΦFS) :=
      (hfc.comp ((continuous_inv.mul continuous_const).mul continuous_id)).quotient_lift _
    have := hγ.regular
    exact hc.integrable_of_hasCompactSupport hs
  let ΨF : GeneralLinear n F → ℂ := fun h =>
    ∫ κ in (K' : Set (GeneralLinear n F)), ΦF ((MonoidHom.id _) h * κ) ∂μF
  have hΨFT : ∀ t : glCentralizer (u ^ l), ∀ h, ΨF (t.val * h) = ΨF h := by
    intro t h
    simp only [ΨF]
    congr 1
    funext κ
    rw [MonoidHom.id_apply, MonoidHom.id_apply, mul_assoc]
    exact hΦFS t (h * κ)
  have hF := hγ.integral_descend_eq_of_compactOpen (Φ := ΦF) (MonoidHom.id _)
    IsClosedEmbedding.id K' hK'o hK'c hT (Subgroup.map_id _).symm (by rfl) hγ
    hΦFm hΦFS (fun g _ => ⟨g, 1, K'.one_mem, by simp⟩) hintF ΨF (fun _ => rfl) hΨFT
  -- comparison of the averages
  have hΨ : ΨE = ΨF := by
    funext h
    simp only [ΨE, ΨF, ΦE, ΦF, MonoidHom.id_apply]
    set w := h⁻¹ * u * h with hw
    have eE : ∀ κ : GeneralLinear n E, (j h * κ)⁻¹ * baseChange F E n u *
        entrywiseAut σ n (j h * κ) = κ⁻¹ * baseChange F E n w * entrywiseAut σ n κ := by
      intro κ
      simp only [hw, j, map_mul, map_inv, entrywiseAut_baseChange, mul_inv_rev]
      group
    have eF : ∀ κ : GeneralLinear n F, (h * κ)⁻¹ * u ^ l * (h * κ) = κ⁻¹ * w ^ l * κ := by
      intro κ
      have hc := conj_pow (a := h⁻¹) (b := u) (i := l)
      rw [inv_inv] at hc
      rw [hw, hc]
      group
    simp_rw [eE, eF]
    by_cases hwK : baseChange F E n w ∈ K
    · exact (heq w hwK).symm
    · rw [setIntegral_eq_zero_of_forall_eq_zero, setIntegral_eq_zero_of_forall_eq_zero]
      · intro κ hκ
        by_contra h0
        obtain ⟨u', hu', e2⟩ := hf _ h0
        have e3 := hK.conj_of_conj_pow u u' hu hu' (h * κ) (by
          rw [← e2, ← eF κ])
        apply hwK
        have e4 : w = κ * u' * κ⁻¹ := by rw [← e3, hw]; group
        rw [e4, map_mul, map_mul, map_inv]
        exact K.mul_mem (K.mul_mem hκ hu') (K.inv_mem hκ)
      · intro κ hκ
        by_contra h0
        obtain ⟨κ', hκ', u', hu', e2⟩ := hφ _ h0
        apply hwK
        have h5 := K.mul_mem (K.mul_mem hκ (K.mul_mem (K.mul_mem (K.inv_mem hκ') hu')
          (hK.entrywiseAut_mem κ' hκ'))) (K.inv_mem (hK.entrywiseAut_mem κ hκ))
        rw [← e2, show κ * (κ⁻¹ * baseChange F E n w * entrywiseAut σ n κ) *
          (entrywiseAut σ n κ)⁻¹ = baseChange F E n w by group] at h5
        exact h5
  change ∫ q, descend _ ΦE hΦES q ∂νδ = ∫ q, descend _ ΦF hΦFS q ∂νγ
  rw [hE, hF, Subgroup.comap_id]
  congr 2
  funext q
  induction q using Quotient.inductionOn with
  | h x => exact congrFun hΨ x



end Core

section Main

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {E : Type v} [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E]

/-- **Matching through a descent subgroup** (source `nearCore`): let `K` be a compact open
subgroup of `GL_n(E)` with `IsTwistedDescentSubgroup F σ l K`, `φ` supported on the σ-conjugates
`κ⁻¹ u κ^σ` (`κ ∈ K`, `u ∈ K ∩ GL_n(F)`), `f` supported on the `l`-th powers of `K ∩ GL_n(F)`,
and suppose that for every `u ∈ K ∩ GL_n(F)`,
`∫_{K ∩ GL_n(F)} f (κ⁻¹ u^l κ) dμF(κ) = ∫_K φ (κ⁻¹ u κ^σ) dμE(κ)`. Then `φ` and `f` concord. -/
theorem areConcordant_of_integral_eq {σ : E ≃ₐ[F] E} {l n : ℕ} (hσ : IsCyclicAlgebra σ l)
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
    (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
    (μE : Measure (GeneralLinear n E)) [μE.IsHaarMeasure]
    (K : Subgroup (GeneralLinear n E)) (hKo : IsOpen (K : Set (GeneralLinear n E)))
    (hKc : IsCompact (K : Set (GeneralLinear n E))) (hK : IsTwistedDescentSubgroup F σ l K)
    (φ : SchwartzBruhat (GeneralLinear n E)) (f : SchwartzBruhat (GeneralLinear n F))
    (hφ : ∀ g, φ g ≠ 0 → ∃ κ ∈ K, ∃ u : GeneralLinear n F, baseChange F E n u ∈ K ∧
      g = κ⁻¹ * baseChange F E n u * entrywiseAut σ n κ)
    (hf : ∀ γ, f γ ≠ 0 → ∃ u : GeneralLinear n F, baseChange F E n u ∈ K ∧ γ = u ^ l)
    (heq : ∀ u : GeneralLinear n F, baseChange F E n u ∈ K →
      ∫ κ in (K.comap (baseChange F E n) : Set (GeneralLinear n F)), f (κ⁻¹ * u ^ l * κ) ∂μF =
        ∫ κ in (K : Set (GeneralLinear n E)),
          φ (κ⁻¹ * baseChange F E n u * entrywiseAut σ n κ) ∂μE) :
    AreConcordant σ l μF μE φ f := by
  let : T2Space F := LocalFieldTopology.t2Space F
  let : SecondCountableTopology F := LocalFieldTopology.secondCountableTopology F
  let : TotallyDisconnectedSpace F := LocalFieldTopology.totallyDisconnectedSpace F
  let : T2Space (GeneralLinear n F) := LocalFieldTopology.generalLinear_t2Space F n
  let : LocallyCompactSpace (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let : SecondCountableTopology (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_secondCountableTopology F n
  let : Module.Finite F E := hσ.1
  have hEp := generalLinear_isLocallyProfinite_of_finiteAlgebra (F := F) (E := E) n
  let : T2Space (GeneralLinear n E) := hEp.t2Space
  let : LocallyCompactSpace (GeneralLinear n E) := hEp.locallyCompactSpace
  let : SecondCountableTopology (GeneralLinear n E) :=
    generalLinear_secondCountable_of_finiteAlgebra (F := F) n
  let : T2Space E := (finiteAlgebraCoordinates (F := F) (E := E)).symm.t2Space
  have hj : IsClosedEmbedding (baseChange F E n) := hσ.isClosedEmbedding_baseChange n
  have hθ : Continuous fun g : GeneralLinear n E => entrywiseAut σ n g := continuous_entrywiseAut σ n
  have hbase : Measurable (baseChange F E n) := hj.continuous.measurable
  have hNL := cyclicNormLemma F E σ l n hσ
  refine ⟨?_, ?_⟩
  · intro γ _ hnorm μγ _ _ νγ _
    refine twistedOrbitalIntegral_eq_zero_of_forall _ _ _ fun y => ?_
    by_contra h0
    obtain ⟨u, -, e⟩ := hf _ h0
    apply hnorm
    have : IsNorm σ l (y⁻¹ * γ * y) := by
      rw [show y⁻¹ * γ * y = u ^ l from e]
      exact isNorm_pow σ l u
    exact (isNorm_conj_iff hσ.pow_eq_one y γ).mp this
  · intro δ γ hassoc hγ
    by_cases hex : ∃ u y : GeneralLinear n F, baseChange F E n u ∈ K ∧ γ = y * u ^ l * y⁻¹
    · obtain ⟨u, y, hu, hγu⟩ := hex
      have hy : y⁻¹ * γ * y = u ^ l := by rw [hγu]; group
      have hreg : IsRegularSemisimple (u ^ l) := by
        rw [← hy]; exact (isRegularSemisimple_conj_iff y γ).mpr hγ
      refine concordAt_of_conj_of_cyclicNorm_eq hσ.pow_eq_one hbase δ γ y fun δ' hδ' => ?_
      rw [hy] at hδ' ⊢
      obtain ⟨x, hx⟩ := hNL.2.2 (baseChange F E n u) δ'
        ⟨1, by rw [cyclicNorm_baseChange, hδ']; simp⟩
      have hc0 := concordAt_baseChange hσ hj hθ K hKo hKc hK φ.continuous φ.hasCompactSupport
        f.continuous f.hasCompactSupport hφ hf heq hu hreg
      refine ConcordAt.of_twistedConj hσ.pow_eq_one x⁻¹ ?_
      have e : twistedConj (entrywiseAut σ n) x⁻¹ δ' = baseChange F E n u := by
        rw [twistedConj_apply, ← hx, map_inv]
        group
      rw [e]
      exact hc0
    · intro μδ _ _ μγ _ _ νδ νγ _ _ _
      rw [sigmaOrbitalIntegral, orbitalIntegral, twistedOrbitalIntegral_eq_zero_of_forall,
        twistedOrbitalIntegral_eq_zero_of_forall]
      · intro y
        by_contra h0
        obtain ⟨u, hu, e⟩ := hf _ h0
        have e' : y⁻¹ * γ * y = u ^ l := e
        exact hex ⟨u, y, hu, by rw [← e']; group⟩
      · intro g
        by_contra h0
        obtain ⟨κ, -, u, hu, e⟩ := hφ _ h0
        have hN := congrArg (cyclicNorm σ l) e
        rw [cyclicNorm_twistedConj, cyclicNorm_twistedConj, hσ.pow_eq_one, entrywiseAut_one_apply,
          entrywiseAut_one_apply, cyclicNorm_baseChange] at hN
        have hassoc' : IsNormAssociated σ l δ (u ^ l) := ⟨g * κ⁻¹, by
          calc (g * κ⁻¹)⁻¹ * cyclicNorm σ l δ * (g * κ⁻¹)
              = κ * (g⁻¹ * cyclicNorm σ l δ * g) * κ⁻¹ := by group
            _ = baseChange F E n (u ^ l) := by rw [hN]; group⟩
        obtain ⟨y, hy⟩ := hNL.2.1 δ γ (u ^ l) hassoc hassoc'
        exact hex ⟨u, y, hu, by rw [← hy]; group⟩

end Main

end Langlands.BaseChange
