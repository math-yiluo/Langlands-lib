import Langlands.Representation.Plancherel.LeviInflatedNormalization
import Langlands.HarmonicAnalysis.SmoothWeakIntegral
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Topology.CompactOpen.OpenSubgroup

/-! # The general standard intertwining integral on its actual domain -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction HarmonicAnalysis.SmoothWeakIntegral

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (U' : Subgroup G)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)

/-- The actual carrier `(U ∩ U') \ U'`, with no normality hypothesis. -/
abbrev QuotientSpace := Induction.LeftQuotient (U.subgroupOf U')

/-- Positive Levi-normalized functions are invariant under the source radical. -/
theorem source_unipotent_invariant
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (u : U) (x : G) :
    eval P (leviInflatedInducingRepresentation h hU A) f ((u : G) * x) =
      eval P (leviInflatedInducingRepresentation h hU A) f x := by
  have hc := (leviInflated_covariant_iff h hU A
    (eval P (leviInflatedInducingRepresentation h hU A) f)).mp f.1.2
  simpa using hc (1 : M) u x

/-- Descent of `u' ↦ f(u'g)` to the actual, possibly nonnormal left quotient. -/
def integrand (g : G) :
    (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A →ₗ[ℂ]
      (QuotientSpace (U := U) U' → A) where
  toFun f := QuotientIntegration.descend (U.subgroupOf U')
    (fun u' : U' => eval P (leviInflatedInducingRepresentation h hU A) f
      ((u' : G) * g)) (by
        intro a u'
        change eval P (leviInflatedInducingRepresentation h hU A) f
          (((a : U') : G) * (u' : G) * g) = _
        rw [mul_assoc]
        exact source_unipotent_invariant h hU A f
          ⟨((a : U') : G), a.property⟩ ((u' : G) * g))
  map_add' f k := by
    funext q
    induction q using Quotient.inductionOn with
    | h u' => rfl
  map_smul' c f := by
    funext q
    induction q using Quotient.inductionOn with
    | h u' => rfl

@[simp]
theorem integrand_mk (g : G)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) (u' : U') :
    integrand h hU U' A g f (Quotient.mk _ u') =
      eval P (leviInflatedInducingRepresentation h hU A) f ((u' : G) * g) := rfl

/-- The original right action translates the evaluation point. -/
theorem integrand_right_action (g t : G)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) :
    integrand h hU U' A g
        (((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation t f) =
      integrand h hU U' A (g * t) f := by
  funext q
  induction q using Quotient.inductionOn with
  | h u' => simp only [integrand_mk, leviInflatedInduction_right_translation, mul_assoc]

/-- Multiplication of the evaluation point by `U'` translates left cosets on
the right; normality of the intersection is not used. -/
theorem integrand_unipotent_mul (g : G) (u' : U')
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (q : QuotientSpace (U := U) U') :
    integrand h hU U' A ((u' : G) * g) f q =
      integrand h hU U' A g f
        (QuotientIntegration.rightTranslate (U.subgroupOf U') u' q) := by
  induction q using Quotient.inductionOn with
  | h v' => simp only [QuotientIntegration.rightTranslate_mk, integrand_mk,
      Subgroup.coe_mul, mul_assoc]

variable [MeasurableSpace (QuotientSpace (U := U) U')]
  (ν : Measure (QuotientSpace (U := U) U'))

/-- Scalar absolute convergence against every smooth functional, together with
a representing vector in the original inducing carrier, at every `g`. -/
def HasIntegral
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A)
    (Jf : G → A) : Prop :=
  ∀ g, HarmonicAnalysis.SmoothWeakIntegral.HasIntegral A.representation ν
    (integrand h hU U' A g f) (Jf g)

/-- The actual domain of the integral, inside the source normalized induction.
No convergence or representability conclusion is supplied as an input. -/
def domain :
    Submodule ℂ ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) :=
  ⨅ g, (integrableSubmodule A.representation ν).comap (integrand h hU U' A g)

theorem mem_domain
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) :
    f ∈ domain h hU U' A ν ↔ ∃ Jf, HasIntegral h hU U' A ν f Jf := by
  simp only [domain, Submodule.mem_iInf, Submodule.mem_comap, mem_integrableSubmodule]
  constructor
  · intro hf
    choose Jf hJf using hf
    exact ⟨Jf, hJf⟩
  · rintro ⟨Jf, hJf⟩ g
    exact ⟨Jf g, hJf g⟩

theorem HasIntegral.right_action
    {f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A} {Jf : G → A}
    (hf : HasIntegral h hU U' A ν f Jf) (t : G) :
    HasIntegral h hU U' A ν
      (((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation t f)
      (fun g => Jf (g * t)) := by
  intro g
  rw [integrand_right_action]
  exact hf (g * t)

/-- The domain is stable under the original ambient action. -/
def domainSubrepresentation :
    Subrepresentation
      ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation where
  toSubmodule := domain h hU U' A ν
  apply_mem_toSubmodule := by
    intro t f hf
    obtain ⟨Jf, hJf⟩ := (mem_domain h hU U' A ν f).mp hf
    exact (mem_domain h hU U' A ν _).mpr
      ⟨_, HasIntegral.right_action h hU U' A ν hJf t⟩

/-- Closedness of the actual Levi supplies compact-open cofinality for weak
integral uniqueness. -/
theorem compactCofinal (hM : IsClosed (M : Set G)) :
    ∀ K : OpenSubgroup M, ∃ L : OpenSubgroup M, IsCompact (L : Set M) ∧ L ≤ K := by
  let := hM.locallyCompactSpace
  exact openSubgroupContainsCompactOpen M

variable (hM : IsClosed (M : Set G))

/-- The linear standard integral is selected only on its actual domain. -/
def operator : domain h hU U' A ν →ₗ[ℂ] (G → A) :=
  LinearMap.pi fun g =>
    (integralLinear (compactCofinal hM) A.property).comp
      (LinearMap.codRestrict (integrableSubmodule A.representation ν)
        ((integrand h hU U' A g).comp (domain h hU U' A ν).subtype)
        (fun f => (Submodule.mem_iInf _).mp f.property g))

/-- The selected operator satisfies all original smooth scalar tests. -/
theorem operator_spec (f : domain h hU U' A ν) :
    HasIntegral h hU U' A ν f.val (operator h hU U' A ν hM f) :=
  fun g => integralLinear_spec (compactCofinal hM) A.property
    ⟨integrand h hU U' A g f.val, (Submodule.mem_iInf _).mp f.property g⟩

theorem operator_eq (f : domain h hU U' A ν) {Jf : G → A}
    (hf : HasIntegral h hU U' A ν f.val Jf) :
    operator h hU U' A ν hM f = Jf :=
  funext fun g => ((operator_spec h hU U' A ν hM f) g).unique
    (compactCofinal hM) A.property (hf g)

/-- Smooth-functional evaluation is the genuine complex scalar integral. -/
theorem operator_eval (f : domain h hU U' A ν) (g : G)
    (ℓ : SmoothDual A.representation) :
    ℓ.val (operator h hU U' A ν hM f g) =
      ∫ q, ℓ.val (integrand h hU U' A g f.val q) ∂ν :=
  (((operator_spec h hU U' A ν hM f) g) ℓ).2.symm

/-- The integral commutes with the actual source right action. -/
theorem operator_right_action (f : domain h hU U' A ν) (t : G) :
    operator h hU U' A ν hM
        ⟨((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation t f.val,
          (domainSubrepresentation h hU U' A ν).apply_mem_toSubmodule t f.property⟩ =
      fun g => operator h hU U' A ν hM f (g * t) :=
  operator_eq h hU U' A ν hM _
    (HasIntegral.right_action h hU U' A ν (operator_spec h hU U' A ν hM f) t)

/-- Every uniform open right stabilizer of the input also stabilizes the
entire output function. -/
theorem operator_preserves_stabilizer (f : domain h hU U' A ν)
    (K : OpenSubgroup G)
    (hK : ∀ k : K,
      ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation k f.val =
        f.val) :
    ∀ (k : K) (g : G),
      operator h hU U' A ν hM f (g * (k : G)) =
        operator h hU U' A ν hM f g := by
  intro k g
  have ht := congrFun (operator_right_action h hU U' A ν hM f (k : G)) g
  have he : (⟨((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).representation
      (k : G) f.val,
      (domainSubrepresentation h hU U' A ν).apply_mem_toSubmodule (k : G) f.property⟩ :
      domain h hU U' A ν) = f := Subtype.ext (hK k)
  rw [he] at ht
  exact ht.symm

theorem operator_uniformly_smooth (f : domain h hU U' A ν) :
    ∃ K : OpenSubgroup G, ∀ (k : K) (g : G),
      operator h hU U' A ν hM f (g * (k : G)) =
        operator h hU U' A ν hM f g := by
  obtain ⟨K, hK⟩ :=
    ((DynamicNormalization.leviTwistedInductionFunctor h hU).obj A).property f.val
  exact ⟨K, operator_preserves_stabilizer h hU U' A ν hM f K hK⟩

section CompatibleMeasure

variable [MeasurableSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [BorelSpace (QuotientSpace (U := U) U')]
  (μU' : Measure U') (μI : Measure (U.subgroupOf U')) [IsMulRightInvariant μI]
  (hν : QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν)

include hν

/-- Right invariance of the compatible quotient measure gives invariance of
the output under the entire target radical. -/
theorem operator_unipotent_mul (f : domain h hU U' A ν) (u' : U') (g : G) :
    operator h hU U' A ν hM f ((u' : G) * g) =
      operator h hU U' A ν hM f g := by
  apply HarmonicAnalysis.SmoothWeakIntegral.HasIntegral.unique
    (compactCofinal hM) A.property ((operator_spec h hU U' A ν hM f) _)
  intro ℓ
  have ht := (operator_spec h hU U' A ν hM f g) ℓ
  simp only [integrand_unipotent_mul]
  exact ⟨(hν.right_invariant u').integrable_comp_of_integrable ht.1,
    ((hν.right_invariant u').integral_comp
      (QuotientIntegration.rightTranslate (U.subgroupOf U') u').toMeasurableEquiv.measurableEmbedding
      _).trans ht.2⟩

end CompatibleMeasure

section MeasureExistence

variable [T2Space G] (hU' : IsClosed (U' : Set G))
  [MeasurableSpace U'] [BorelSpace U']
  [MeasurableSpace (U.subgroupOf U')] [BorelSpace (U.subgroupOf U')]
  [BorelSpace (QuotientSpace (U := U) U')]
  (μU' : Measure U') (μI : Measure (U.subgroupOf U'))
  [Measure.IsHaarMeasure μU'] [μU'.Regular] [IsMulRightInvariant μU']
  [Measure.IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]

include hU hU'

/-- For fixed regular two-sided Haar measures on `U'` and the actual
intersection, the published quotient-measure theorem provides a compatible
measure. No normality or quotient group structure is used. -/
theorem compatibleMeasure_exists :
    ∃ ν : Measure (QuotientSpace (U := U) U'),
      QuotientIntegration.IsCompatible (U.subgroupOf U') μU' μI ν := by
  let := hU'.locallyCompactSpace
  exact QuotientIntegration.compatibleMeasureExists (U.subgroupOf U')
    (hU.preimage continuous_subtype_val) μU' μI

end MeasureExistence

end Langlands.Plancherel.StandardIntertwining
