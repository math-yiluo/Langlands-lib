import Langlands.Algebra.FilteredSymmetricAlgebraSymmetrization
import Langlands.Global.ArchimedeanSymmetricAlgebraSymmetrization
import Langlands.Global.ArchimedeanCartanAveraging

/-! # Filtered symmetrization and actual compact invariant lifting -/

noncomputable section
universe u uX uV
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open MeasureTheory
open Langlands.Analysis.FiniteSpanIntegral
open Langlands.Representation.AlgebraicCompact

variable (K : Type u) [Field K] (n : ℕ)

/-- Span of actual Lie symmetric monomials of degree at most `d`. -/
abbrev lieSymmetricDegreeFiltration (d : ℕ) : Submodule ℂ (LieSymmetricAlgebra K n) :=
  Langlands.Algebra.UniversalEnveloping.symmetricDegreeFiltration ℂ
    (ComplexLieAlgebra K n) d

/-- Full-group conjugation preserves the actual bounded symmetric monomial span. -/
theorem lieSymmetricConjugation_mem_degreeFiltration (g : InfiniteAdelicGL K n)
    {d : ℕ} {P : LieSymmetricAlgebra K n} (hP : P ∈ lieSymmetricDegreeFiltration K n d) :
    lieSymmetricConjugation K n g P ∈ lieSymmetricDegreeFiltration K n d := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, rfl⟩ := hP
    have heq : lieSymmetricConjugation K n g ((l.map (SymmetricAlgebra.ι ℂ _)).prod) =
        ((l.map (complexLieConjugation K n g)).map (SymmetricAlgebra.ι ℂ _)).prod := by
      simp only [map_list_prod, List.map_map, Function.comp_def,
        lieSymmetricConjugation_ι]
    rw [heq]
    exact Langlands.Algebra.UniversalEnveloping.prod_mem_symmetricDegreeFiltration
      ℂ (ComplexLieAlgebra K n) _ (by simpa using hl)
  | zero => simp
  | add P Q hP hQ ihP ihQ =>
    simpa only [map_add] using (lieSymmetricDegreeFiltration K n d).add_mem ihP ihQ
  | smul z P hP ih =>
    simpa only [map_smul] using (lieSymmetricDegreeFiltration K n d).smul_mem z ih

/-- Restriction of the actual full-group action to a bounded symmetric span. -/
def lieSymmetricDegreeConjugation (d : ℕ) (g : InfiniteAdelicGL K n) :
    lieSymmetricDegreeFiltration K n d ≃ₗ[ℂ] lieSymmetricDegreeFiltration K n d where
  toFun P := ⟨lieSymmetricConjugation K n g P.val,
    lieSymmetricConjugation_mem_degreeFiltration K n g P.property⟩
  invFun P := ⟨lieSymmetricConjugation K n g⁻¹ P.val,
    lieSymmetricConjugation_mem_degreeFiltration K n g⁻¹ P.property⟩
  left_inv P := Subtype.ext (by simp)
  right_inv P := Subtype.ext (by simp)
  map_add' P Q := Subtype.ext (map_add (lieSymmetricConjugation K n g) P.val Q.val)
  map_smul' z P := Subtype.ext (map_smul (lieSymmetricConjugation K n g) z P.val)

@[simp] theorem lieSymmetricDegreeConjugation_coe (d : ℕ) (g : InfiniteAdelicGL K n)
    (P : lieSymmetricDegreeFiltration K n d) :
    (lieSymmetricDegreeConjugation K n d g P : LieSymmetricAlgebra K n) =
      lieSymmetricConjugation K n g P.val := rfl

/-- Actual whole symmetrization restricted to matching degree bounds. -/
abbrev lieSymmetricAlgebraSymmetrizeDegree (d : ℕ) :
    lieSymmetricDegreeFiltration K n d →ₗ[ℂ] envelopingDegreeFiltration K n d :=
  Langlands.Algebra.UniversalEnveloping.symmetricAlgebraSymmetrizeDegree ℂ
    (ComplexLieAlgebra K n) d

@[simp] theorem lieSymmetricAlgebraSymmetrizeDegree_coe (d : ℕ)
    (P : lieSymmetricDegreeFiltration K n d) :
    (lieSymmetricAlgebraSymmetrizeDegree K n d P : EnvelopingAlgebra K n) =
      lieSymmetricAlgebraSymmetrize K n P.val := rfl

theorem lieSymmetricAlgebraSymmetrizeDegree_surjective (d : ℕ) :
    Function.Surjective (lieSymmetricAlgebraSymmetrizeDegree K n d) :=
  Langlands.Algebra.UniversalEnveloping.symmetricAlgebraSymmetrizeDegree_surjective ℂ _ d

theorem lieSymmetricAlgebraSymmetrizeDegree_conjugation (d : ℕ)
    (g : InfiniteAdelicGL K n) (P : lieSymmetricDegreeFiltration K n d) :
    envelopingDegreeConjugation K n d g (lieSymmetricAlgebraSymmetrizeDegree K n d P) =
      lieSymmetricAlgebraSymmetrizeDegree K n d (lieSymmetricDegreeConjugation K n d g P) := by
  apply Subtype.ext
  exact lieSymmetricAlgebraSymmetrize_conjugation K n g P.val

/-- The actual full compact conjugation representation on the genuine enveloping algebra. -/
def envelopingCompactRepresentation :
    _root_.Representation ℂ (standardInfiniteCompact K n) (EnvelopingAlgebra K n) where
  toFun k := (envelopingConjugation K n k.val).toAlgHom.toLinearMap
  map_one' := by
    ext a
    exact AlgEquiv.congr_fun (envelopingConjugation_one K n) a
  map_mul' k l := by
    ext a
    exact AlgEquiv.congr_fun (envelopingConjugation_mul K n k.val l.val) a

variable [NumberField K]

/-- Surjective equivariant symmetrization transfers finite continuous full-group orbits. -/
theorem envelopingConjugation_hasFiniteContinuousSpan (a : EnvelopingAlgebra K n) :
    HasFiniteContinuousSpan (fun g : InfiniteAdelicGL K n => envelopingConjugation K n g a) := by
  obtain ⟨P, rfl⟩ :=
    Langlands.Algebra.UniversalEnveloping.symmetricAlgebraSymmetrize_surjective ℂ
      (ComplexLieAlgebra K n) a
  change HasFiniteContinuousSpan (fun g : InfiniteAdelicGL K n =>
    envelopingConjugation K n g (lieSymmetricAlgebraSymmetrize K n P))
  simpa only [lieSymmetricAlgebraSymmetrize_conjugation] using
    (lieSymmetricConjugation_hasFiniteContinuousSpan K n P).linearMap
      (lieSymmetricAlgebraSymmetrize K n)

/-- All genuine enveloping compact orbits satisfy the finite-span averaging hypotheses. -/
theorem envelopingCompact_hasFiniteContinuousOrbits :
    HasFiniteContinuousOrbits (envelopingCompactRepresentation K n) := by
  intro a
  exact (envelopingConjugation_hasFiniteContinuousSpan K n a).comp
    (fun k : standardInfiniteCompact K n => k.val) continuous_subtype_val

local instance symmetrizationMeasurableSpace : MeasurableSpace (standardInfiniteCompact K n) :=
  borel (standardInfiniteCompact K n)
local instance symmetrizationBorelSpace : BorelSpace (standardInfiniteCompact K n) := ⟨rfl⟩

private def symmetrizationAveragingMeasure : Measure (standardInfiniteCompact K n) :=
  Measure.haarMeasure ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
local instance symmetrizationProbabilityMeasure : IsProbabilityMeasure (symmetrizationAveragingMeasure K n) :=
  ⟨Measure.haarMeasure_self⟩
local instance symmetrizationLeftInvariant : (symmetrizationAveragingMeasure K n).IsMulLeftInvariant := by
  dsimp only [symmetrizationAveragingMeasure]
  infer_instance

/-- Normalized Haar average into the actual compact fixed enveloping subalgebra. -/
def envelopingCompactAverage :
    EnvelopingAlgebra K n →ₗ[ℂ] envelopingCompactInvariants K n :=
  (average (envelopingCompactRepresentation K n)
    (envelopingCompact_hasFiniteContinuousOrbits K n)
    (symmetrizationAveragingMeasure K n)).codRestrict
      (envelopingCompactInvariants K n).toSubmodule
      (average_mem_invariants (envelopingCompactRepresentation K n)
        (envelopingCompact_hasFiniteContinuousOrbits K n)
        (symmetrizationAveragingMeasure K n))

@[simp] theorem envelopingCompactAverage_fixed (a : envelopingCompactInvariants K n) :
    envelopingCompactAverage K n a.val = a := by
  apply Subtype.ext
  exact average_fixed (envelopingCompactRepresentation K n)
    (envelopingCompact_hasFiniteContinuousOrbits K n) (symmetrizationAveragingMeasure K n)
    a.val a.property

/-- Actual symmetric and enveloping Haar averages commute with symmetrization. -/
theorem envelopingCompactAverage_symmetrize (P : LieSymmetricAlgebra K n) :
    envelopingCompactAverage K n (lieSymmetricAlgebraSymmetrize K n P) =
      lieSymmetricCompactInvariantSymmetrize K n (lieSymmetricCompactAverage K n P) := by
  apply Subtype.ext
  exact average_natural (lieSymmetricCompactRepresentation K n)
    (lieSymmetricCompact_hasFiniteContinuousOrbits K n) (symmetrizationAveragingMeasure K n)
    (envelopingCompactRepresentation K n) (envelopingCompact_hasFiniteContinuousOrbits K n)
    (lieSymmetricAlgebraSymmetrize K n)
    (fun k Q => (lieSymmetricAlgebraSymmetrize_conjugation K n k.val Q).symm) P

private theorem finiteSpanIntegral_mem {X : Type uX} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (μ : Measure X) [IsFiniteMeasure μ] (F : X → V) (hF : HasFiniteContinuousSpan F)
    (M : Submodule ℂ V) (hM : ∀ x, F x ∈ M) :
    Langlands.Analysis.FiniteSpanIntegral.integral μ F hF ∈ M := by
  apply (Submodule.Quotient.mk_eq_zero M).mp
  apply eq_of_dual_eq
  intro l
  change (l.comp M.mkQ) (Langlands.Analysis.FiniteSpanIntegral.integral μ F hF) = l 0
  rw [dual_integral]
  have hz (x : X) : M.mkQ (F x) = 0 := (Submodule.Quotient.mk_eq_zero M).mpr (hM x)
  simp only [LinearMap.comp_apply, hz, map_zero, integral_zero]

/-- Symmetric averaging retains every actual monomial degree bound. -/
theorem lieSymmetricCompactAverage_mem_degreeFiltration {d : ℕ}
    {P : LieSymmetricAlgebra K n} (hP : P ∈ lieSymmetricDegreeFiltration K n d) :
    (lieSymmetricCompactAverage K n P : LieSymmetricAlgebra K n) ∈
      lieSymmetricDegreeFiltration K n d := by
  change Langlands.Analysis.FiniteSpanIntegral.integral (symmetrizationAveragingMeasure K n)
    (fun k => lieSymmetricCompactRepresentation K n k P)
    (lieSymmetricCompact_hasFiniteContinuousOrbits K n P) ∈ _
  exact finiteSpanIntegral_mem _ _ _ _
    (fun k => lieSymmetricConjugation_mem_degreeFiltration K n k.val hP)

/-- Enveloping averaging retains every genuine filtration bound. -/
theorem envelopingCompactAverage_mem_degreeFiltration {d : ℕ}
    {a : EnvelopingAlgebra K n} (ha : a ∈ envelopingDegreeFiltration K n d) :
    (envelopingCompactAverage K n a : EnvelopingAlgebra K n) ∈
      envelopingDegreeFiltration K n d := by
  change Langlands.Analysis.FiniteSpanIntegral.integral (symmetrizationAveragingMeasure K n)
    (fun k => envelopingCompactRepresentation K n k a)
    (envelopingCompact_hasFiniteContinuousOrbits K n a) ∈ _
  exact finiteSpanIntegral_mem _ _ _ _
    (fun k => envelopingConjugation_mem_degreeFiltration K n k.val ha)

/-- A compact invariant element of degree at most `d` has a compact invariant
symmetric preimage with the same bound. -/
theorem exists_compactInvariant_symmetrize_degree (d : ℕ)
    (a : envelopingCompactInvariants K n) (ha : a.val ∈ envelopingDegreeFiltration K n d) :
    ∃ P : lieSymmetricCompactInvariants K n,
      P.val ∈ lieSymmetricDegreeFiltration K n d ∧
      lieSymmetricCompactInvariantSymmetrize K n P = a := by
  obtain ⟨P, hP⟩ := lieSymmetricAlgebraSymmetrizeDegree_surjective K n d ⟨a.val, ha⟩
  have heq : lieSymmetricAlgebraSymmetrize K n P.val = a.val := congrArg Subtype.val hP
  refine ⟨lieSymmetricCompactAverage K n P.val,
    lieSymmetricCompactAverage_mem_degreeFiltration K n P.property, ?_⟩
  rw [← envelopingCompactAverage_symmetrize, heq, envelopingCompactAverage_fixed]

/-- Whole symmetrization is onto the actual full compact fixed enveloping algebra. -/
theorem lieSymmetricCompactInvariantSymmetrize_surjective :
    Function.Surjective (lieSymmetricCompactInvariantSymmetrize K n) := by
  intro a
  obtain ⟨d, hd⟩ := exists_mem_envelopingDegreeFiltration K n a.val
  obtain ⟨P, _, hP⟩ := exists_compactInvariant_symmetrize_degree K n d a hd
  exact ⟨P, hP⟩

end Langlands.Global.ArchimedeanGL
