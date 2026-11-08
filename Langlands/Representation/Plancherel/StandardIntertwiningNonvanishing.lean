import Langlands.Representation.Plancherel.StandardInductionSelfComparison
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Analysis.Local.QuotientMass

/-! # Nonvanishing of the actual standard intertwining integral -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction

universe uH uG uI uV uX uW

section Indicator

variable {X : Type uX} [MeasurableSpace X]
  {G : Type uG} [Group G] [TopologicalSpace G]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A constant vector on a measurable set of finite measure has its mass
multiple as weak integral. -/
theorem hasIntegral_indicator_const (ρ : Representation ℂ G W) (μ : Measure X)
    {S : Set X} (hS : MeasurableSet S) (hμ : μ S ≠ ⊤) (w : W) :
    HarmonicAnalysis.SmoothWeakIntegral.HasIntegral ρ μ
      (S.indicator fun _ => w) (((μ S).toReal : ℂ) • w) := by
  intro ℓ
  have he : (fun x => ℓ.val (S.indicator (fun _ => w) x)) =
      S.indicator (fun _ => ℓ.val w) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, map_zero]
  rw [he]
  refine ⟨(MeasureTheory.integrable_indicator_iff hS).mpr (integrableOn_const hμ), ?_⟩
  rw [integral_indicator_const _ hS, map_smul, Measure.real, Complex.real_smul]
  rfl

end Indicator

section Local

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- Every point of `U'` lying in `P Q` is a product of a point of `U` and a
point of `Q ∩ U'`. -/
def HasSourceLocalProduct (P U U' : Subgroup G) (Q : OpenSubgroup G) : Prop :=
  ∀ x : G, x ∈ U' → (∃ p ∈ P, ∃ k ∈ Q, x = p * k) →
    ∃ a ∈ U, ∃ q ∈ Q, q ∈ U' ∧ x = a * q

/-- The open subgroup `Q ∩ U'` of `U'`. -/
abbrev targetCompactOpen (U' : Subgroup G) (Q : OpenSubgroup G) : OpenSubgroup U' :=
  Q.comap U'.subtype continuous_subtype_val

/-- The image of `Q ∩ U'` in the actual quotient `(U ∩ U') \ U'`. -/
abbrev sourceTestOrbit (U U' : Subgroup G) (Q : OpenSubgroup G) :
    Set (QuotientSpace (U := U) U') :=
  QuotientIntegration.compactOpenQuotientOrbit (U.subgroupOf U') (targetCompactOpen U' Q)

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- `Q ∩ U'` is compact in `U'` when `Q` is compact and `U'` is closed. -/
theorem targetCompactOpen_isCompact (U' : Subgroup G) (hU' : IsClosed (U' : Set G))
    (Q : OpenSubgroup G) (hQ : IsCompact (Q : Set G)) :
    IsCompact (targetCompactOpen U' Q : Set U') :=
  hU'.isClosedEmbedding_subtypeVal.isCompact_preimage hQ

variable {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (U' : Subgroup G)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  (Q : OpenSubgroup G) (hQ : IsCompact (Q : Set G)) (v : A)
  (hv : v ∈ fixedVectors (leviInflatedInducingRepresentation h hU A)
    (conjOpenSubgroup P Q 1).toSubgroup)

/-- The actual induced vector supported on `P Q` with value `v` at `1`. -/
def sourceTestVector : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A :=
  (compactDoubleCosetSection P (leviInflatedInducingRepresentation h hU A) Q hQ 1 v hv).val

/-- The test vector has the value `σ(p) v` at `p k`, for `p ∈ P` and `k ∈ Q`. -/
theorem sourceTestVector_eval_mul (p : P) (k : Q) :
    eval P (leviInflatedInducingRepresentation h hU A)
        (sourceTestVector h hU A Q hQ v hv) ((p : G) * (k : G)) =
      leviInflatedInducingRepresentation h hU A p v := by
  have he := compactDoubleCosetSection_apply P (leviInflatedInducingRepresentation h hU A)
    Q hQ 1 v hv p k
  unfold sourceTestVector
  simpa only [mul_one] using he

/-- The test vector vanishes off `P Q`. -/
theorem sourceTestVector_eval_eq_zero (x : G) (hx : ¬ ∃ p ∈ P, ∃ k ∈ Q, x = p * k) :
    eval P (leviInflatedInducingRepresentation h hU A)
      (sourceTestVector h hU A Q hQ v hv) x = 0 := by
  by_contra hne
  apply hx
  obtain ⟨k, hk, he⟩ := compactDoubleCosetSection_support_subset P
    (leviInflatedInducingRepresentation h hU A) Q hQ 1 v hv ⟨x, hne, rfl⟩
  have hp : x * (1 * k)⁻¹ ∈ P := QuotientGroup.rightRel_apply.mp (Quotient.exact he)
  refine ⟨x * k⁻¹, by simpa only [one_mul] using hp, k, hk, ?_⟩
  group

/-- On the target radical, the test vector is `v` on `(U ∩ U')(Q ∩ U')` and zero
elsewhere: its integrand at `1` is the indicator of the orbit of `Q ∩ U'`. -/
theorem integrand_sourceTestVector (hloc : HasSourceLocalProduct P U U' Q) :
    integrand h hU U' A 1 (sourceTestVector h hU A Q hQ v hv) =
      (sourceTestOrbit U U' Q).indicator (fun _ => v) := by
  funext q
  induction q using Quotient.inductionOn with
  | h x =>
    rw [integrand_mk, mul_one]
    by_cases hmem : (Quotient.mk _ x : QuotientSpace (U := U) U') ∈ sourceTestOrbit U U' Q
    · rw [Set.indicator_of_mem hmem]
      obtain ⟨k, hk, he⟩ := hmem
      have ha : x * k⁻¹ ∈ U.subgroupOf U' :=
        QuotientGroup.rightRel_apply.mp (Quotient.exact he)
      have hau : ((x : G) * (k : G)⁻¹) ∈ U := ha
      have hx : (x : G) = (((⟨(x : G) * (k : G)⁻¹, h.unipotent_le hau⟩ : P) : G) *
          ((⟨(k : G), hk⟩ : Q) : G)) := by
        simp only [inv_mul_cancel_right]
      rw [hx, sourceTestVector_eval_mul h hU A Q hQ v hv]
      have hproj := h.projection_unipotent ⟨(x : G) * (k : G)⁻¹, hau⟩
      simp only [leviInflatedInducingRepresentation, MonoidHom.coe_comp, Function.comp_apply,
        hproj, map_one, Module.End.one_apply]
    · rw [Set.indicator_of_notMem hmem]
      apply sourceTestVector_eval_eq_zero
      intro hPQ
      obtain ⟨a, ha, q', hq', hqU', hxa⟩ := hloc x x.property hPQ
      apply hmem
      refine ⟨⟨q', hqU'⟩, hq', ?_⟩
      apply Quotient.sound
      refine QuotientGroup.rightRel_apply.mpr ?_
      change (x : G) * q'⁻¹ ∈ U
      rw [hxa, mul_inv_cancel_right]
      exact ha

variable [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')]
  (ν : Measure (QuotientSpace (U := U) U'))

/-- The integrand of the test vector at `1` has weak integral the measure of the
orbit of `Q ∩ U'` times `v`. -/
theorem hasIntegral_sourceTestVector_one (hloc : HasSourceLocalProduct P U U' Q)
    (hν : ν (sourceTestOrbit U U' Q) ≠ ⊤) :
    HarmonicAnalysis.SmoothWeakIntegral.HasIntegral A.representation ν
      (integrand h hU U' A 1 (sourceTestVector h hU A Q hQ v hv))
      (((ν (sourceTestOrbit U U' Q)).toReal : ℂ) • v) := by
  rw [integrand_sourceTestVector h hU U' A Q hQ v hv hloc]
  exact hasIntegral_indicator_const A.representation ν
    (QuotientIntegration.isOpen_compactOpenQuotientOrbit _ _).measurableSet hν v

/-- Any representing function of the standard integral of the test vector has
value `ν(S) • v` at `1`, where `S` is the orbit of `Q ∩ U'`. -/
theorem HasIntegral.eval_one_sourceTestVector (hM : IsClosed (M : Set G))
    (hloc : HasSourceLocalProduct P U U' Q) (hν : ν (sourceTestOrbit U U' Q) ≠ ⊤)
    {Jf : G → A} (hJ : HasIntegral h hU U' A ν (sourceTestVector h hU A Q hQ v hv) Jf) :
    Jf 1 = ((ν (sourceTestOrbit U U' Q)).toReal : ℂ) • v :=
  (hJ 1).unique (compactCofinal hM) A.property
    (hasIntegral_sourceTestVector_one h hU U' A Q hQ v hv ν hloc hν)

variable [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  (μU' : Measure U') (μI : Measure (U.subgroupOf U')) [IsMulRightInvariant μI]

omit [BorelSpace U'] in
/-- With a compatible quotient measure and a nonzero vector, the standard
integral of the test vector is nonzero at `1`. -/
theorem HasIntegral.eval_one_sourceTestVector_ne_zero (hM : IsClosed (M : Set G))
    (hU' : IsClosed (U' : Set G)) (hloc : HasSourceLocalProduct P U U' Q)
    (hqν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν) (hv0 : v ≠ 0)
    {Jf : G → A} (hJ : HasIntegral h hU U' A ν (sourceTestVector h hU A Q hQ v hv) Jf) :
    Jf 1 ≠ 0 := by
  have hmass := hqν.compactOpenQuotientOrbit_mass (targetCompactOpen U' Q)
    (targetCompactOpen_isCompact U' hU' Q hQ)
  rw [hJ.eval_one_sourceTestVector h hU U' A Q hQ v hv ν hM hloc hmass.2.ne]
  refine smul_ne_zero ?_ hv0
  exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hmass.1.ne' hmass.2.ne).ne'

section FullSource

variable {P' : Subgroup G} (h' : IsSemidirectDecomposition P' M U')
  [T2Space G]
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular]
  (hqν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)
  (hM : IsClosed (M : Set G)) (hU' : IsClosed (U' : Set G))
  (hsq : SquaredModulusCompatibility h hU h' hU')

include hQ hv in
/-- The full-source standard intertwiner is nonzero when some nonzero vector
admits a test vector supported on `P Q` with the local product property. -/
theorem fullSourceIntertwiner_ne_zero (hloc : HasSourceLocalProduct P U U' Q)
    (hv0 : v ≠ 0) (hfull : domain h hU U' A ν = ⊤) :
    fullSourceIntertwiner h hU h' hU' A ν μU' μI hqν hM hsq hfull ≠ 0 := by
  intro hzero
  have hspec := fullSourceIntertwiner_spec h hU h' hU' A ν μU' μI hqν hM hsq hfull
    (sourceTestVector h hU A Q hQ v hv)
  apply HasIntegral.eval_one_sourceTestVector_ne_zero h hU U' A Q hQ v hv ν μU' μI
    hM hU' hloc hqν hv0 hspec
  rw [hzero]
  rfl

end FullSource

end Local

section Family

variable {H : Type uH} [Group H] [TopologicalSpace H]
  {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G] [T2Space G]
  {P P' M U U' : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (e : H ≃ₜ* M) {I : Type uI} (ν : I → (H →* ℝ≥0ˣ))
  [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')]
  (qν : Measure (QuotientSpace (U := U) U'))
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hqν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI qν)
  (hM : IsClosed (M : Set G))
  (hsq : SquaredModulusCompatibility h hU h' hU')
  (A : SmoothRep.{0, uG, uV} ℂ M)

/-- At every parameter of its full domain, the actual standard integral family
is nonzero, given a nonzero vector of the twisted inducing representation and a
compact open subgroup `Q` with the local product property whose intersection with
`P` fixes that vector. -/
theorem standardInductionIntertwinerFamily_ne_zero
    (χ : standardIntertwiningFullDomainRegion h hU U' e ν qν A)
    (Q : OpenSubgroup G) (hQ : IsCompact (Q : Set G))
    (v : A.twist (unramifiedCharactersHomeomorph e ν χ.val).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker
        (fun i => MonoidHom.comp (ν i) e.symm.toMulEquiv.toMonoidHom)
        (unramifiedCharactersHomeomorph e ν χ.val)))
    (hv : v ∈ fixedVectors (leviInflatedInducingRepresentation h hU
      (A.twist (unramifiedCharactersHomeomorph e ν χ.val).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker
          (fun i => MonoidHom.comp (ν i) e.symm.toMulEquiv.toMonoidHom)
          (unramifiedCharactersHomeomorph e ν χ.val))))
      (conjOpenSubgroup P Q 1).toSubgroup)
    (hloc : HasSourceLocalProduct P U U' Q) (hv0 : v ≠ 0) :
    standardInductionIntertwinerFamily h hU U' e ν qν h' hU' μU' μI hqν hM hsq A χ ≠ 0 :=
  fullSourceIntertwiner_ne_zero h hU U' _ Q hQ v hv qν μU' μI h' hqν hM hU' hsq
    hloc hv0 χ.property

end Family

end Langlands.Plancherel.StandardIntertwining
