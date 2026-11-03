import Langlands.Representation.Induction.FiniteTwistTrace
import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Representation.Hecke.CommonInvarianceProof

/-! Finite character expansions and continuity for compact-quotient induction. -/

noncomputable section

namespace Langlands.Induction

open HarmonicAnalysis MeasureTheory

universe uG uV uA uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [Measure.IsMulLeftInvariant μ]

/-- Compact quotient and coefficient admissibility supply the transversal and
finite basis. The resulting coefficients precede every allowed character. -/
theorem exists_induced_distribution_twistCoefficients
    (P : Subgroup G) (hP : IsClosed (P : Set G))
    (σ : Representation ℂ P V) (hσ : IsAdmissible σ)
    [CompactSpace (LeftQuotient P)] (f : SchwartzBruhat G) :
    ∃ c : P →₀ ℂ, ∀ (χ : P →* ℂˣ),
      (∀ H : Subgroup P, IsCompact (H : Set P) → H ≤ χ.ker) →
      ∀ hAdm : IsAdmissible (smoothInduced P (twist χ σ)),
        Character.distribution μ (smoothInduced P (twist χ σ)) hAdm f =
          Finsupp.linearCombination ℂ (fun p : P => (χ p : ℂ)) c := by
  classical
  obtain ⟨K, _, hK, hKf⟩ :=
    Hecke.TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  have hf := hKf f (Finset.mem_singleton_self f)
  obtain ⟨t, hcover, hdistinct⟩ := exists_finset_doubleCoset_representatives P K
  have : ∀ i : t, Module.Finite ℂ
      (fixedVectors σ (conjOpenSubgroup P K i).toSubgroup) := fun i => hσ.2 _
  let b := Module.finBasis ℂ ((i : t) →
    fixedVectors σ (conjOpenSubgroup P K i).toSubgroup)
  refine ⟨inducedFixedTraceTwistCoefficients μ P σ K t b f hf.2, ?_⟩
  intro χ hχ hAdm
  exact induced_distribution_eq_twistCoefficients μ P σ K hK t hcover hdistinct
    b f hf χ (fun i => hχ _ (isCompact_conjOpenSubgroup P hP K hK i)) hAdm

/-- One chosen coefficient function for all compact-trivial character twists. -/
def compactQuotientTwistCoefficients
    (P : Subgroup G) (hP : IsClosed (P : Set G))
    (σ : Representation ℂ P V) (hσ : IsAdmissible σ)
    [CompactSpace (LeftQuotient P)] (f : SchwartzBruhat G) : P →₀ ℂ :=
  (exists_induced_distribution_twistCoefficients μ P hP σ hσ f).choose

/-- The chosen coefficient function evaluates to the actual distribution. -/
theorem compactQuotientTwistCoefficients_eval
    (P : Subgroup G) (hP : IsClosed (P : Set G))
    (σ : Representation ℂ P V) (hσ : IsAdmissible σ)
    [CompactSpace (LeftQuotient P)] (f : SchwartzBruhat G)
    (χ : P →* ℂˣ)
    (hχ : ∀ H : Subgroup P, IsCompact (H : Set P) → H ≤ χ.ker)
    (hAdm : IsAdmissible (smoothInduced P (twist χ σ))) :
    Character.distribution μ (smoothInduced P (twist χ σ)) hAdm f =
      Finsupp.linearCombination ℂ (fun p : P => (χ p : ℂ))
        (compactQuotientTwistCoefficients μ P hP σ hσ f) :=
  (exists_induced_distribution_twistCoefficients μ P hP σ hσ f).choose_spec χ hχ hAdm

variable {A : Type uA} [TopologicalSpace A]

/-- A finite character expansion makes every test-function value continuous in
any parameter family with continuous character evaluations. -/
theorem continuous_induced_distribution_twist
    (P : Subgroup G) (hP : IsClosed (P : Set G))
    (σ : Representation ℂ P V) (hσ : IsAdmissible σ)
    [CompactSpace (LeftQuotient P)]
    (χ : A → P →* ℂˣ)
    (hχ : ∀ a (H : Subgroup P), IsCompact (H : Set P) → H ≤ (χ a).ker)
    (hEval : ∀ p : P, Continuous (fun a => (χ a p : ℂ)))
    (hAdm : ∀ a, IsAdmissible (smoothInduced P (twist (χ a) σ)))
    (f : SchwartzBruhat G) :
    Continuous (fun a => Character.distribution μ
      (smoothInduced P (twist (χ a) σ)) (hAdm a) f) := by
  let c := compactQuotientTwistCoefficients μ P hP σ hσ f
  have he : (fun a => Character.distribution μ
      (smoothInduced P (twist (χ a) σ)) (hAdm a) f) =
      (fun a => ∑ p ∈ c.support, c p * (χ a p : ℂ)) := by
    funext a
    rw [compactQuotientTwistCoefficients_eval μ P hP σ hσ f (χ a) (hχ a) (hAdm a)]
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]
    rfl
  rw [he]
  exact continuous_finsetSum _ (fun p _ => continuous_const.mul (hEval p))

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Equality on a dense parameter set extends to every twist for two actual
compact-quotient inductions. The dense equality itself remains an input. -/
theorem induced_distribution_twist_eq_of_dense
    (P : Subgroup G) (hP : IsClosed (P : Set G))
    (σ : Representation ℂ P V) (hσ : IsAdmissible σ)
    [CompactSpace (LeftQuotient P)]
    (Q : Subgroup G) (hQ : IsClosed (Q : Set G))
    (τ : Representation ℂ Q W) (hτ : IsAdmissible τ)
    [CompactSpace (LeftQuotient Q)]
    (χ : A → P →* ℂˣ) (η : A → Q →* ℂˣ)
    (hχ : ∀ a (H : Subgroup P), IsCompact (H : Set P) → H ≤ (χ a).ker)
    (hη : ∀ a (H : Subgroup Q), IsCompact (H : Set Q) → H ≤ (η a).ker)
    (hEvalχ : ∀ p : P, Continuous (fun a => (χ a p : ℂ)))
    (hEvalη : ∀ q : Q, Continuous (fun a => (η a q : ℂ)))
    (hAdmσ : ∀ a, IsAdmissible (smoothInduced P (twist (χ a) σ)))
    (hAdmτ : ∀ a, IsAdmissible (smoothInduced Q (twist (η a) τ)))
    (S : Set A) (hS : Dense S)
    (hEq : ∀ a ∈ S, Character.distribution μ
      (smoothInduced P (twist (χ a) σ)) (hAdmσ a) =
        Character.distribution μ (smoothInduced Q (twist (η a) τ)) (hAdmτ a)) :
    ∀ a, Character.distribution μ (smoothInduced P (twist (χ a) σ)) (hAdmσ a) =
      Character.distribution μ (smoothInduced Q (twist (η a) τ)) (hAdmτ a) := by
  intro a
  ext f
  have hcσ := continuous_induced_distribution_twist μ P hP σ hσ χ hχ hEvalχ hAdmσ f
  have hcτ := continuous_induced_distribution_twist μ Q hQ τ hτ η hη hEvalη hAdmτ f
  have hclosed := isClosed_eq hcσ hcτ
  have hclosure : closure S ⊆ {a | Character.distribution μ
      (smoothInduced P (twist (χ a) σ)) (hAdmσ a) f =
        Character.distribution μ (smoothInduced Q (twist (η a) τ)) (hAdmτ a) f} :=
    hclosed.closure_subset_iff.mpr (fun a ha =>
      congrArg (fun D : HarmonicAnalysis.Distribution G => D f) (hEq a ha))
  exact hclosure (hS a)

end Langlands.Induction
