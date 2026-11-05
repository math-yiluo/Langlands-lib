import Langlands.Representation.Plancherel.CompactIntertwiningFamilies
import Langlands.Representation.Twist.SmoothPartDefinitions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Group.CompactOpen

/-!
# Parameter continuity of actual compact standard integrals

Fixed-point compact extensions have one character-evaluation factor. Their
scalar integrands are continuous in the actual character topology. Local
integrable domination gives continuity of scalar standard integrals.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Topology
open scoped NNReal

namespace Langlands.Plancherel

open Aubert.General Induction StandardIntertwining

universe uG uI uV uX

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

/-- At each ambient point the actual covariance extension has one fixed
vector multiplied by one actual character evaluation. -/
theorem unramifiedCompactExtension_eval_factor
    (f : CompactInductionPicture h K A) (x : G) :
    ∃ (m : M) (v : A), ∀ χ : unramifiedCharacters ν,
      eval _ _
        ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f) x =
          (χ.val m : ℂ) • v := by
  obtain ⟨p, k, rfl⟩ := hPK x
  refine ⟨h.projection p, inducingRepresentation h hU A p (eval _ _ f k), ?_⟩
  intro χ
  rw [unramifiedLeviInductionCompactEquiv_symm_mul]
  change (HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂ) •
    ((χ.val (h.projection p) : ℂ) • A.representation (h.projection p) (eval _ _ f k)) =
      (χ.val (h.projection p) : ℂ) •
        ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂ) •
          A.representation (h.projection p) (eval _ _ f k))
  exact smul_comm _ _ _

/-- Each fixed ambient-point value is a finite regular vector family on any
subset of the full character space. -/
theorem unramifiedCompactExtension_eval_isPolynomialOn
    (Ω : Set (unramifiedCharacters ν)) (f : CompactInductionPicture h K A) (x : G) :
    UnramifiedOperatorFamily.IsPolynomialOn Ω (fun χ =>
      eval _ _
        ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ.val A).symm f) x) := by
  obtain ⟨m, v, hv⟩ := unramifiedCompactExtension_eval_factor h hU hδ K hP hK hPK ν hν hr A f x
  exact ⟨1, fun _ => unramifiedEvaluationRegular ν m, fun _ => v, by
    intro χ
    simp only [Fin.sum_univ_one, unramifiedEvaluationRegular_apply]
    exact hv χ.val⟩

/-- No topology on the inducing carrier or on its algebraic dual is needed
for scalar continuity of a fixed-point extension. -/
theorem continuous_unramifiedCompactExtension_scalar
    (f : CompactInductionPicture h K A) (x : G) (ℓ : Module.Dual ℂ A) :
    Continuous (fun χ : unramifiedCharacters ν =>
      ℓ (eval _ _
        ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f) x)) := by
  obtain ⟨m, v, hv⟩ := unramifiedCompactExtension_eval_factor h hU hδ K hP hK hPK ν hν hr A f x
  have he : (fun χ : unramifiedCharacters ν =>
      ℓ (eval _ _
        ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f) x)) =
      (fun χ : unramifiedCharacters ν => (χ.val m : ℂ) * ℓ v) := by
    funext χ
    exact (congrArg ℓ (hv χ)).trans (ℓ.map_smul _ _)
  rw [he]
  exact ((Units.continuous_val.comp (continuous_eval_const m)).comp
    continuous_subtype_val).mul continuous_const

variable (U' : Subgroup G)

/-- The actual quotient integrand of a fixed compact section, extended using
the actual normalized covariance at each character. -/
def unramifiedCompactIntegrand (f : CompactInductionPicture h K A) (g : G)
    (χ : unramifiedCharacters ν) : QuotientSpace (U := U) U' → A :=
  integrand h hU U'
    (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) g
    ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f)

/-- For every point of the actual, possibly nonnormal quotient, the scalar
integrand is continuous in the full compact-open character topology. -/
theorem continuous_unramifiedCompactIntegrand_scalar
    (f : CompactInductionPicture h K A) (g : G) (ℓ : Module.Dual ℂ A)
    (q : QuotientSpace (U := U) U') :
    Continuous (fun χ : unramifiedCharacters ν =>
      ℓ (unramifiedCompactIntegrand h hU hδ K hP hK hPK ν hν hr A U' f g χ q)) := by
  induction q using Quotient.inductionOn with
  | h u' =>
    exact continuous_unramifiedCompactExtension_scalar h hU hδ K hP hK hPK ν hν hr A
      f ((u' : G) * g) ℓ

section ScalarIntegral

variable [MeasurableSpace (QuotientSpace (U := U) U')]
  (qν : Measure (QuotientSpace (U := U) U'))

/-- The actual full-domain equality supplies scalar integrability for each
fixed smooth functional of the original, untwisted representation. -/
theorem unramifiedCompactIntegrand_scalar_integrable
    (χ : unramifiedCharacters ν)
    (hfull : domain h hU U'
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν = ⊤)
    (f : CompactInductionPicture h K A) (g : G) (ℓ : Langlands.SmoothDual A.representation) :
    Integrable (fun q =>
      ℓ.val (unramifiedCompactIntegrand h hU hδ K hP hK hPK ν hν hr A U' f g χ q)) qν := by
  let ℓχ := (Langlands.smoothContragredientTwistEquiv χ.val.toMonoidHom A.representation
    (unramifiedCharacter_isOpen_ker ν χ)).symm ℓ
  have hf : (unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f ∈
      domain h hU U'
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν := by
    rw [hfull]
    exact Submodule.mem_top
  obtain ⟨Jf, hJf⟩ := (mem_domain h hU U' _ qν _).mp hf
  exact (hJf g ℓχ).1

variable {X : Type uX} [TopologicalSpace X] [FirstCountableTopology X]

/-- Local integrable domination promotes pointwise parameter continuity to
continuity of the genuine scalar integral. The parameter may be a coordinate
space or a subset of the actual character space. -/
theorem continuousAt_unramifiedCompactScalarIntegral_of_dominated
    (c : X → unramifiedCharacters ν) {x₀ : X} (hc : ContinuousAt c x₀)
    (f : CompactInductionPicture h K A) (g : G) (ℓ : Module.Dual ℂ A)
    {bound : QuotientSpace (U := U) U' → ℝ}
    (h_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun q =>
      ℓ (unramifiedCompactIntegrand h hU hδ K hP hK hPK ν hν hr A U' f g (c x) q)) qν)
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ q ∂qν,
      ‖ℓ (unramifiedCompactIntegrand h hU hδ K hP hK hPK ν hν hr A U' f g (c x) q)‖ ≤ bound q)
    (h_integrable : Integrable bound qν) :
    ContinuousAt (fun x => ∫ q,
      ℓ (unramifiedCompactIntegrand h hU hδ K hP hK hPK ν hν hr A U' f g (c x) q) ∂qν) x₀ := by
  apply continuousAt_of_dominated h_meas h_bound h_integrable
  exact Filter.Eventually.of_forall fun q =>
    (continuous_unramifiedCompactIntegrand_scalar h hU hδ K hP hK hPK ν hν hr A U'
      f g ℓ q).continuousAt.comp hc

end ScalarIntegral

section StandardCompactOperator

variable {P' U' : Subgroup G}
  (h' : IsSemidirectDecomposition P' M U') (hU' : IsClosed (U' : Set G))
  (hδ' : IsUnimodularModulus U' hU') (hP' : IsClosed (P' : Set G))
  (hP'K : ∀ g : G, ∃ p : P', ∃ k : K, g = (p : G) * (k : G))
  (hr' : Continuous h'.projection)
  [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [MeasurableSpace (QuotientSpace (U := U) U')]
  [BorelSpace (QuotientSpace (U := U) U')] [T2Space G]
  (qν : Measure (QuotientSpace (U := U) U'))
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [Measure.IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [Measure.IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
  (hqν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI qν)
  (hM : IsClosed (M : Set G)) (hsq : SquaredModulusCompatibility h hU h' hU')

/-- A fixed smooth functional of the original carrier tests every twisted
compact operator by the same genuine scalar integral. -/
theorem standardCompactOperator_scalar_eval
    (χ : unramifiedCharacters ν)
    (hfull : domain h hU U'
      (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) qν = ⊤)
    (f : CompactInductionPicture h K A) (k : K) (ℓ : Langlands.SmoothDual A.representation) :
    ℓ.val (eval _ _ (standardCompactOperator h hU hδ K hP hK hPK ν hν hr
      h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq χ A hfull f) k) =
      ∫ q, ℓ.val
        (unramifiedCompactIntegrand h hU hδ K hP hK hPK ν hν hr A U' f k χ q) ∂qν := by
  let ℓχ := (Langlands.smoothContragredientTwistEquiv χ.val.toMonoidHom A.representation
    (unramifiedCharacter_isOpen_ker ν χ)).symm ℓ
  exact operator_eval h hU U' _ qν hM
    (sourceToDomain h hU _ qν hfull
      ((unramifiedLeviInductionCompactEquiv h hU hδ K hP hK hPK ν hν hr χ A).symm f))
    k ℓχ

variable {X : Type uX} [TopologicalSpace X] [FirstCountableTopology X]

/-- Along a continuous parameter map, locally uniform integrable domination
gives scalar continuity of the actual compact standard operator. Full-domain
convergence supplies measurability; the domination estimate remains explicit. -/
theorem continuousAt_standardCompactOperator_scalar_of_dominated
    (c : X → unramifiedCharacters ν) {x₀ : X} (hc : ContinuousAt c x₀)
    (hfull : ∀ x, domain h hU U'
      (A.twist (c x).val.toMonoidHom (unramifiedCharacter_isOpen_ker ν (c x))) qν = ⊤)
    (f : CompactInductionPicture h K A) (k : K) (ℓ : Langlands.SmoothDual A.representation)
    {bound : QuotientSpace (U := U) U' → ℝ}
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ q ∂qν,
      ‖ℓ.val (unramifiedCompactIntegrand h hU hδ K hP hK hPK ν hν hr A U' f k (c x) q)‖ ≤
        bound q)
    (h_integrable : Integrable bound qν) :
    ContinuousAt (fun x =>
      ℓ.val (eval _ _ (standardCompactOperator h hU hδ K hP hK hPK ν hν hr
        h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq (c x) A (hfull x) f) k)) x₀ := by
  have he : (fun x =>
      ℓ.val (eval _ _ (standardCompactOperator h hU hδ K hP hK hPK ν hν hr
        h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq (c x) A (hfull x) f) k)) =
      (fun x => ∫ q, ℓ.val
        (unramifiedCompactIntegrand h hU hδ K hP hK hPK ν hν hr A U' f k (c x) q) ∂qν) := by
    funext x
    exact standardCompactOperator_scalar_eval h hU hδ K hP hK hPK ν hν hr A
      h' hU' hδ' hP' hP'K hr' qν μU' μI hqν hM hsq (c x) (hfull x) f k ℓ
  rw [he]
  apply continuousAt_unramifiedCompactScalarIntegral_of_dominated h hU hδ K hP hK hPK
    ν hν hr A U' qν c hc f k ℓ.val _ h_bound h_integrable
  exact Filter.Eventually.of_forall fun x =>
    (unramifiedCompactIntegrand_scalar_integrable h hU hδ K hP hK hPK ν hν hr A U'
      qν (c x) (hfull x) f k ℓ).aestronglyMeasurable

end StandardCompactOperator

end Langlands.Plancherel
