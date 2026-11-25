import Langlands.TraceFormula.GroupSchemeCuspidalIsotypicTraceFactorizationStatement
import Langlands.TraceFormula.IsotypicTrace.OccurrenceReduction
import Langlands.TraceFormula.IsotypicTrace.PlaceProduct
import Langlands.TraceFormula.IsotypicTrace.TwistCovariance
import Langlands.TraceFormula.IsotypicTrace.RestrictAction

/-!
# Isotypic local trace factorization on a cuspidal summand from one local occurrence

For an irreducible closed invariant subspace `P` of the group-scheme cuspidal space, a finite
place `v`, and one irreducible admissible representation `ρ` of `G(F_v)` with a nonzero
`G(F_v)`-equivariant linear map `j₀` into `P`, the isotypy clause and the ordinary and twisted
trace factorization clauses of `GroupSchemeCuspidalIsotypicTraceFactorizationStatement` hold
for this `ρ` (`cuspidalIsotypicTraceFactorization_of_occurrence`). Consequently the statement
follows for every summand in which some irreducible admissible representation of `G(F_v)`
occurs (`cuspidalIsotypicTraceFactorization_of_exists_occurrence`).
-/

noncomputable section

universe u uV uW

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis.OperatorIdeals Langlands.QuotientIntegration
open Langlands.HarmonicAnalysis

namespace Langlands.TraceFormula.IsotypicTrace

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (v : Langlands.Global.FinitePlace F)
  [MeasurableSpace (PlaceGroupPoints F G (.inr v))]
  [BorelSpace (PlaceGroupPoints F G (.inr v))]
  [LocallyCompactSpace (PlaceGroupPoints F G (.inr v))]
  [TotallyDisconnectedSpace (PlaceGroupPoints F G (.inr v))]

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (π : AdelicGroupPoints F G →* (E →L[ℂ] E)) (hπnorm : ∀ a x, ‖π a x‖ = ‖x‖)
  (hπcont : ∀ x, Continuous fun a => π a x)
  (P : Submodule ℂ E) [CompleteSpace P] (hPinv : ∀ a, ∀ x ∈ P, π a x ∈ P)

include hπnorm in
omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [CompleteSpace E] [CompleteSpace P] in
theorem restrict_norm (a : AdelicGroupPoints F G) (x : P) :
    ‖restrictAction π P hPinv a x‖ = ‖x‖ :=
  hπnorm a x

include hπcont in
omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [CompleteSpace E] [CompleteSpace P] in
theorem restrict_continuous (x : P) : Continuous fun a => restrictAction π P hPinv a x :=
  (hπcont x).subtype_mk _

open Classical in
/-- The away integrated action on the summand, zero for a non-integrable away function. -/
def awayAction (νH : Measure (awaySubgroup F G v)) (fw : AdelicGroupPoints F G → ℂ) :
    P →L[ℂ] P :=
  if h : Integrable (fun h : awaySubgroup F G v => fw h) νH then
    Langlands.Analysis.integratedIsometricAction νH
      ((restrictAction π P hPinv).comp (awaySubgroup F G v).subtype)
      (fun h x => restrict_norm F G π hπnorm P hPinv h x)
      (fun x => ((restrict_continuous F G π hπcont P hPinv x).comp
        continuous_subtype_val).aestronglyMeasurable)
      (fun h : awaySubgroup F G v => fw h) h
  else 0

omit [MeasurableSpace (PlaceGroupPoints F G (.inr v))] [BorelSpace (PlaceGroupPoints F G (.inr v))]
  [LocallyCompactSpace (PlaceGroupPoints F G (.inr v))]
  [TotallyDisconnectedSpace (PlaceGroupPoints F G (.inr v))] [CompleteSpace E] in
theorem awayAction_apply (νH : Measure (awaySubgroup F G v)) (fw : AdelicGroupPoints F G → ℂ)
    (hfw : Integrable (fun h : awaySubgroup F G v => fw h) νH) (x : P) :
    awayAction F G v π hπnorm hπcont P hPinv νH fw x =
      ∫ h : awaySubgroup F G v, fw h • restrictAction π P hPinv h x ∂νH := by
  simp only [awayAction, hfw, ↓reduceDIte]
  rfl

omit [MeasurableSpace (PlaceGroupPoints F G (.inr v))] [BorelSpace (PlaceGroupPoints F G (.inr v))]
  [LocallyCompactSpace (PlaceGroupPoints F G (.inr v))]
  [TotallyDisconnectedSpace (PlaceGroupPoints F G (.inr v))] [CompleteSpace E] in
/-- The away action commutes with the local group. -/
theorem awayAction_commute (νH : Measure (awaySubgroup F G v)) (fw : AdelicGroupPoints F G → ℂ)
    (y : PlaceGroupPoints F G (.inr v)) (x : P) :
    awayAction F G v π hπnorm hπcont P hPinv νH fw
        (restrictAction π P hPinv (ofPlace F G (.inr v) y) x) =
      restrictAction π P hPinv (ofPlace F G (.inr v) y)
        (awayAction F G v π hπnorm hπcont P hPinv νH fw x) := by
  by_cases hfw : Integrable (fun h : awaySubgroup F G v => fw h) νH
  · have hintg : Integrable (fun h : awaySubgroup F G v => fw h • restrictAction π P hPinv h x)
        νH :=
      Langlands.Analysis.isometricActionIntegrand_integrable νH
        ((restrictAction π P hPinv).comp (awaySubgroup F G v).subtype)
        (fun h x => restrict_norm F G π hπnorm P hPinv h x)
        (fun x => ((restrict_continuous F G π hπcont P hPinv x).comp
          continuous_subtype_val).aestronglyMeasurable)
        (fun h : awaySubgroup F G v => fw h) hfw x
    rw [awayAction_apply F G v π hπnorm hπcont P hPinv νH fw hfw,
      awayAction_apply F G v π hπnorm hπcont P hPinv νH fw hfw,
      ← (restrictAction π P hPinv (ofPlace F G (.inr v) y)).integral_comp_comm hintg]
    congr 1
    funext h
    rw [map_smul]
    congr 1
    change (restrictAction π P hPinv h * restrictAction π P hPinv (ofPlace F G (.inr v) y)) x =
      (restrictAction π P hPinv (ofPlace F G (.inr v) y) * restrictAction π P hPinv h) x
    rw [← map_mul, ← map_mul, ofPlace_mul_comm F G v y h.2]
  · simp [awayAction, hfw]

include hπcont in
omit [LocallyCompactSpace (PlaceGroupPoints F G (.inr v))]
  [TotallyDisconnectedSpace (PlaceGroupPoints F G (.inr v))] in
/-- **Compression of a split test function.** -/
theorem compression_split_eq (μv : Measure (PlaceGroupPoints F G (.inr v))) [μv.IsHaarMeasure]
    (νH : Measure (awaySubgroup F G v)) [νH.IsHaarMeasure] (ν : Measure (AdelicGroupPoints F G))
    (hmap : Measure.map (placeSplitting F G v) (μv.prod νH) = ν)
    (fv : SchwartzBruhat (PlaceGroupPoints F G (.inr v))) (fw : AdelicGroupPoints F G → ℂ)
    (hfw : ∀ g x, fw (g * ofPlace F G (.inr v) x) = fw g)
    (hf : Integrable (fun g => fv (atPlace F G (.inr v) g) * fw g) ν) (hfv : fv ≠ 0)
    (R : E →L[ℂ] E) (hR : ∀ x, R x = ∫ a, (fv (atPlace F G (.inr v) a) * fw a) • π a x ∂ν) :
    ∃ X : P →L[ℂ] P,
      (∀ x, X x = ∫ y, fv y • restrictAction π P hPinv (ofPlace F G (.inr v) y) x ∂μv) ∧
      P.orthogonalProjectionOnto ∘L R ∘L P.subtypeL =
        X ∘L awayAction F G v π hπnorm hπcont P hPinv νH fw := by
  have hReq : R = Langlands.Analysis.integratedIsometricAction ν π hπnorm
      (fun x => (hπcont x).aestronglyMeasurable) _ hf := by
    ext1 x
    rw [hR, Langlands.Analysis.integratedIsometricAction_apply]
  subst hReq
  obtain ⟨hfwint, hint⟩ := integral_split_eq F G v (restrictAction π P hPinv)
    (restrict_norm F G π hπnorm P hPinv)
    (restrict_continuous F G π hπcont P hPinv) μv νH ν hmap fv fw hfw hf hfv
  have hfvint : Integrable (fv : PlaceGroupPoints F G (.inr v) → ℂ) μv :=
    fv.locallyConstant.continuous.integrable_of_hasCompactSupport fv.hasCompactSupport
  refine ⟨Langlands.Analysis.integratedIsometricAction μv
    ((restrictAction π P hPinv).comp (ofPlace F G (.inr v)))
    (fun y x => restrict_norm F G π hπnorm P hPinv _ x)
    (fun x => ((restrict_continuous F G π hπcont P hPinv x).comp
      (continuous_ofPlace F G _)).aestronglyMeasurable) fv hfvint, fun x => rfl, ?_⟩
  have h1 := compression_integratedIsometricAction π P hPinv ν hπnorm
    (fun x => (hπcont x).aestronglyMeasurable)
    (restrict_norm F G π hπnorm P hPinv)
    (fun x => (restrict_continuous F G π hπcont P hPinv x).aestronglyMeasurable)
    _ hf
  refine h1.trans ?_
  ext1 x
  rw [Langlands.Analysis.integratedIsometricAction_apply, hint x,
    ContinuousLinearMap.comp_apply, Langlands.Analysis.integratedIsometricAction_apply,
    awayAction_apply F G v π hπnorm hπcont P hPinv νH fw hfwint]
  rfl

include hπnorm hπcont in
/-- **Per-summand reduction, generic form.** For an inner-product-preserving continuous action
`π` of `G(𝔸_F)` on a Hilbert space, an irreducible complete invariant subspace `P` and one
local occurrence `j₀` of an irreducible admissible `ρ` in `P`, the isotypy clause and the
ordinary and twisted trace factorizations hold for `ρ`. -/
theorem isotypicTraceFactorization_of_occurrence_generic
    (hπinner : ∀ a x y, inner ℂ (π a x) (π a y) = inner ℂ x y)
    (hPirr : ∀ Q : Submodule ℂ E, Q ≤ P → IsClosed (Q : Set E) →
      (∀ a, ∀ x ∈ Q, π a x ∈ Q) → Q = ⊥ ∨ Q = P)
    (μv : Measure (PlaceGroupPoints F G (.inr v))) [μv.IsHaarMeasure]
    (ν : Measure (AdelicGroupPoints F G)) [ν.IsHaarMeasure]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (PlaceGroupPoints F G (.inr v)) V) (hρ : IsAdmissible ρ)
    (hρirr : Representation.IsIrreducible ρ)
    (j₀ : V →ₗ[ℂ] E) (hj₀0 : j₀ ≠ 0) (hj₀P : LinearMap.range j₀ ≤ P)
    (hj₀ : ∀ y x, j₀ (ρ y x) = π (ofPlace F G (.inr v) y) (j₀ x)) :
    (∀ (V' : Type uW) [AddCommGroup V'] [Module ℂ V']
        (ρ' : Representation ℂ (PlaceGroupPoints F G (.inr v)) V'),
        IsSmooth ρ' → Representation.IsIrreducible ρ' →
        ∀ j : V' →ₗ[ℂ] E, j ≠ 0 → LinearMap.range j ≤ P →
          (∀ y x, j (ρ' y x) = π (ofPlace F G (.inr v) y) (j x)) →
          ∃ E' : V' ≃ₗ[ℂ] V, ∀ y x, E' (ρ' y x) = ρ y (E' x)) ∧
    (∃ C : (AdelicGroupPoints F G → ℂ) → ℂ,
      ∀ (fv : SchwartzBruhat (PlaceGroupPoints F G (.inr v)))
        (fw : AdelicGroupPoints F G → ℂ),
        (∀ g x, fw (g * ofPlace F G (.inr v) x) = fw g) →
        Integrable (fun g => fv (atPlace F G (.inr v) g) * fw g) ν →
        ∀ R : E →L[ℂ] E, (∀ x, R x = ∫ a, (fv (atPlace F G (.inr v) a) * fw a) • π a x ∂ν) →
          IsTraceClass (P.orthogonalProjectionOnto ∘L R ∘L P.subtypeL) →
          operatorTrace (P.orthogonalProjectionOnto ∘L R ∘L P.subtypeL) =
            Character.distribution μv ρ hρ fv * C fw) ∧
    (∀ (Θ : AdelicGroupPoints F G →* AdelicGroupPoints F G)
        (θv : PlaceGroupPoints F G (.inr v) ≃ₜ* PlaceGroupPoints F G (.inr v)),
        (∀ x, Θ (ofPlace F G (.inr v) x) = ofPlace F G (.inr v) (θv x)) →
        ∀ IP : P →L[ℂ] P, Function.Injective IP →
          (∀ a x, IP (restrictAction π P hPinv a x) = restrictAction π P hPinv (Θ a) (IP x)) →
          ∃ Av : V →ₗ[ℂ] V, Function.Bijective Av ∧
            (∀ y w, Av (ρ y w) = ρ (θv y) (Av w)) ∧
            ∃ C : (AdelicGroupPoints F G → ℂ) → ℂ,
              ∀ (fv : SchwartzBruhat (PlaceGroupPoints F G (.inr v)))
                (fw : AdelicGroupPoints F G → ℂ),
                (∀ g x, fw (g * ofPlace F G (.inr v) x) = fw g) →
                Integrable (fun g => fv (atPlace F G (.inr v) g) * fw g) ν →
                ∀ R : E →L[ℂ] E,
                  (∀ x, R x = ∫ a, (fv (atPlace F G (.inr v) a) * fw a) • π a x ∂ν) →
                  IsTraceClass ((P.orthogonalProjectionOnto ∘L R ∘L P.subtypeL) ∘L IP) →
                  operatorTrace ((P.orthogonalProjectionOnto ∘L R ∘L P.subtypeL) ∘L IP) =
                    Langlands.BaseChange.twistedDistribution μv ρ hρ Av fv * C fw) := by
  classical
  let πP := restrictAction π P hPinv
  have hπPinner : ∀ a x y, inner ℂ (πP a x) (πP a y) = inner ℂ x y :=
    restrictAction_inner π P hPinv hπinner
  have hπPcont := restrict_continuous F G π hπcont P hPinv
  have hirrP := restrictAction_irreducible π P hPinv hPirr
  have hιcont : ∀ x : P, Continuous fun y => πP (ofPlace F G (.inr v) y) x :=
    fun x => (hπPcont x).comp (continuous_ofPlace F G _)
  have hsplit := exists_split F G v
  let j₀P : V →ₗ[ℂ] P := j₀.codRestrict P (fun x => hj₀P ⟨x, rfl⟩)
  have hj₀P' : ∀ y x, j₀P (ρ y x) = πP (ofPlace F G (.inr v) y) (j₀P x) :=
    fun y x => Subtype.ext (hj₀ y x)
  have hj₀P0 : j₀P ≠ 0 := by
    intro h
    apply hj₀0
    ext x
    exact congrArg (fun f : V →ₗ[ℂ] P => (f x : E)) h
  obtain ⟨νH, hνH, hmap⟩ := exists_awayHaar F G v μv ν
  -- The zero case of a split test function.
  have hzero : ∀ (fw : AdelicGroupPoints F G → ℂ) (R : E →L[ℂ] E),
      (∀ x, R x = ∫ a, ((0 : SchwartzBruhat (PlaceGroupPoints F G (.inr v)))
        (atPlace F G (.inr v) a) * fw a) • π a x ∂ν) → R = 0 := by
    intro fw R hR
    ext1 x
    rw [hR]
    simp
  refine ⟨?_, ?_, ?_⟩
  · intro V' _ _ ρ' hρ' hρ'irr j hj0 hjP hj
    let jP : V' →ₗ[ℂ] P := j.codRestrict P (fun x => hjP ⟨x, rfl⟩)
    have hjP0 : jP ≠ 0 := by
      intro h
      apply hj0
      ext x
      exact congrArg (fun f : V' →ₗ[ℂ] P => (f x : E)) h
    exact isotypic_of_occurrence πP (ofPlace F G (.inr v)) ρ μv hπPinner hιcont hsplit hirrP
      hρ hρirr j₀P hj₀P' hj₀P0 ρ' hρ' hρ'irr jP (fun y x => Subtype.ext (hj y x)) hjP0
  · obtain ⟨C, hC⟩ := exists_trace_factorization πP (ofPlace F G (.inr v)) ρ μv hπPinner hιcont
      hsplit hirrP hρ hρirr j₀P hj₀P' hj₀P0
    refine ⟨fun fw => C (awayAction F G v π hπnorm hπcont P hPinv νH fw), ?_⟩
    intro fv fw hfw hf R hR hTC
    by_cases hfv : fv = 0
    · subst hfv
      rw [hzero fw R hR, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero,
        operatorTrace_zero, map_zero, zero_mul]
    · obtain ⟨X, hX, hRP⟩ := compression_split_eq F G v π hπnorm hπcont P hPinv μv νH ν hmap
        fv fw hfw hf hfv R hR
      rw [hRP] at hTC ⊢
      exact hC fv X _ hX (awayAction_commute F G v π hπnorm hπcont P hPinv νH fw) hTC
  · intro Θ θv hΘι IP hIPinj hIPcov
    obtain ⟨Av, hAvbij, hAveq, C, hC⟩ := exists_twisted_trace_factorization πP
      (ofPlace F G (.inr v)) ρ μv hπPinner hιcont hsplit hirrP hρ hρirr j₀P hj₀P' hj₀P0
      Θ θv hΘι IP hIPinj hIPcov
    refine ⟨Av, hAvbij, hAveq, fun fw => C (awayAction F G v π hπnorm hπcont P hPinv νH fw), ?_⟩
    intro fv fw hfw hf R hR hTC
    by_cases hfv : fv = 0
    · subst hfv
      rw [hzero fw R hR, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero,
        ContinuousLinearMap.zero_comp, operatorTrace_zero, map_zero, zero_mul]
    · obtain ⟨X, hX, hRP⟩ := compression_split_eq F G v π hπnorm hπcont P hPinv μv νH ν hmap
        fv fw hfw hf hfv R hR
      rw [hRP, ContinuousLinearMap.comp_assoc] at hTC ⊢
      exact hC fv X _ hX (awayAction_commute F G v π hπnorm hπcont P hPinv νH fw) hTC

end Generic

section Cuspidal

variable (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

set_option maxHeartbeats 1000000 in
/-- **Per-summand reduction for the cuspidal space.** For an irreducible complete invariant
subspace `P` of the full almost-everywhere cuspidal space and one irreducible admissible
representation `ρ` of `G(F_v)` with a nonzero `G(F_v)`-equivariant linear map `j₀` into `P`,
clauses 0', 1 and 2 of `GroupSchemeCuspidalIsotypicTraceFactorizationStatement` hold for this
`ρ`. -/
theorem cuspidalIsotypicTraceFactorization_of_occurrence
    (μv : Measure (PlaceGroupPoints F G (.inr v))) [μv.IsHaarMeasure]
    (ν : Measure (AdelicGroupPoints F G)) [ν.IsHaarMeasure] :
    let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
    ∀ (P : Submodule ℂ S) [CompleteSpace P],
      (∀ (a : AdelicGroupPoints F G), ∀ x ∈ P, πc a x ∈ P) →
      (∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
        (∀ (a : AdelicGroupPoints F G), ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P) →
      ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (PlaceGroupPoints F G (.inr v)) V) (hρ : IsAdmissible ρ),
        ρ.IsIrreducible →
        ∀ j₀ : V →ₗ[ℂ] S, j₀ ≠ 0 → LinearMap.range j₀ ≤ P →
          (∀ y x, j₀ (ρ y x) = πc (ofPlace F G (.inr v) y) (j₀ x)) →
        (∀ (V' : Type u) [AddCommGroup V'] [Module ℂ V']
            (ρ' : Representation ℂ (PlaceGroupPoints F G (.inr v)) V'),
          IsSmooth ρ' → ρ'.IsIrreducible →
          ∀ j : V' →ₗ[ℂ] S, j ≠ 0 → LinearMap.range j ≤ P →
            (∀ y x, j (ρ' y x) = πc (ofPlace F G (.inr v) y) (j x)) →
            ∃ E : V' ≃ₗ[ℂ] V, ∀ y x, E (ρ' y x) = ρ y (E x)) ∧
        (∃ C : (AdelicGroupPoints F G → ℂ) → ℂ,
          ∀ (fv : SchwartzBruhat (PlaceGroupPoints F G (.inr v)))
            (fw : AdelicGroupPoints F G → ℂ),
            (∀ g x, fw (g * ofPlace F G (.inr v) x) = fw g) →
            ∀ hf : Integrable (fun g => fv (atPlace F G (.inr v) g) * fw g) ν,
              let RPf : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L
                fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν _ hf ∘L P.subtypeL
              IsTraceClass (E := (P : Submodule ℂ S)) RPf →
                operatorTrace (E := (P : Submodule ℂ S)) RPf =
                  Character.distribution μv ρ hρ fv * C fw) ∧
        ∀ (Θ : AdelicGroupPoints F G ≃ₜ* AdelicGroupPoints F G)
          (hΘ : ∀ x, Θ x ∈ positiveRationalSubgroup F G T i ↔
            x ∈ positiveRationalSubgroup F G T i)
          (hΘμ : MeasurePreserving
            (quotientAutomorphism (positiveRationalSubgroup F G T i) Θ hΘ).symm
            (positiveRationalQuotientHaarMeasure F G T i)
            (positiveRationalQuotientHaarMeasure F G T i))
          (θv : PlaceGroupPoints F G (.inr v) ≃ₜ* PlaceGroupPoints F G (.inr v)),
          (∀ g, atPlace F G (.inr v) (Θ g) = θv (atPlace F G (.inr v) g)) →
          (∀ x, Θ (ofPlace F G (.inr v) x) = ofPlace F G (.inr v) (θv x)) →
          let IΘ := twistOperator (positiveRationalSubgroup F G T i) Θ hΘ
            (positiveRationalQuotientHaarMeasure F G T i) hΘμ
          (∀ x ∈ P, ∃ y ∈ P, (y : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)) =
            IΘ (x : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i))) →
          ∃ Av : V →ₗ[ℂ] V, Function.Bijective Av ∧
            (∀ y w, Av (ρ y w) = ρ (θv y) (Av w)) ∧
            ∃ C : (AdelicGroupPoints F G → ℂ) → ℂ,
              ∀ (fv : SchwartzBruhat (PlaceGroupPoints F G (.inr v)))
                (fw : AdelicGroupPoints F G → ℂ),
                (∀ g x, fw (g * ofPlace F G (.inr v) x) = fw g) →
                ∀ hf : Integrable (fun g => fv (atPlace F G (.inr v) g) * fw g) ν,
                  let Rf := haarQuotientL2IntegratedAction F G T i hi I e hc ν _ hf
                  let BP : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L
                    (S.orthogonalProjectionOnto ∘L (Rf ∘L IΘ) ∘L S.subtypeL) ∘L P.subtypeL
                  IsTraceClass (E := (P : Submodule ℂ S)) BP →
                    operatorTrace (E := (P : Submodule ℂ S)) BP =
                      Langlands.BaseChange.twistedDistribution μv ρ hρ Av fv * C fw := by
  intro S πc P _ hPinv hPirr V _ _ ρ hρ hρirr j₀ hj₀0 hj₀P hj₀
  have hπinner : ∀ a x y, inner ℂ (πc a x) (πc a y) = inner ℂ x y := fun a x y =>
    (fullAEL2CuspidalRightTranslate F G hPD hG T i hi I e hc a).inner_map_map x y
  have hπnorm : ∀ a x, ‖πc a x‖ = ‖x‖ :=
    norm_fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
  have hπcont : ∀ x, Continuous fun a => πc a x :=
    fun x => (fullAEL2CuspidalOrbitMap F G hPD hG T i hi I e hc x).continuous
  obtain ⟨h0', h1, h2⟩ := isotypicTraceFactorization_of_occurrence_generic F G v πc hπnorm
    hπcont P hPinv hπinner hPirr μv ν ρ hρ hρirr j₀ hj₀0 hj₀P hj₀
  refine ⟨h0', ?_, ?_⟩
  · obtain ⟨C, hC⟩ := h1
    exact ⟨C, fun fv fw hfw hf hTC => hC fv fw hfw hf
      (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν _ hf)
      (fullAEL2CuspidalIntegratedAction_apply F G hPD hG T i hi I e hc ν _ hf) hTC⟩
  · intro Θ hΘ hΘμ θv _ hof IΘ hIP
    let μQ := positiveRationalQuotientHaarMeasure F G T i
    let hR := haarQuotientMeasureRightInvariant F G T i hi I e hc
    let IP : P →L[ℂ] P := nestedRestrict S P IΘ
    have hIPval : ∀ x : P, (((IP x : P) : S) : Lp ℂ 2 μQ) = IΘ ((x : S) : Lp ℂ 2 μQ) :=
      nestedRestrict_val S P IΘ hIP
    have hIinj : Function.Injective IΘ := by
      intro a b hab
      have h := norm_twistOperator_apply (positiveRationalSubgroup F G T i) Θ hΘ μQ hΘμ (a - b)
      change ‖IΘ (a - b)‖ = ‖a - b‖ at h
      rw [map_sub, hab, sub_self, norm_zero] at h
      exact sub_eq_zero.mp (norm_eq_zero.mp h.symm)
    have hIPinj : Function.Injective IP := by
      intro x x' h
      have h1 := congrArg (fun z : P => ((z : S) : Lp ℂ 2 μQ)) h
      simp only [hIPval] at h1
      exact Subtype.ext (Subtype.ext (hIinj h1))
    have hIPcov : ∀ a x, IP (restrictAction πc P hPinv a x) =
        restrictAction πc P hPinv (Θ.toMonoidHom a) (IP x) :=
      nestedRestrict_covariant S P IΘ hIP
        (fun a => (quotientL2RightTranslate F G T i μQ hR a).toContinuousLinearMap) πc
        (fun a x => rfl) hPinv Θ.toMonoidHom
        (fun a x => twistOperator_quotientL2RightTranslate F G T i μQ hR Θ hΘ hΘμ a x)
    obtain ⟨Av, hAvbij, hAveq, C, hC⟩ := h2 Θ.toMonoidHom θv hof IP hIPinj hIPcov
    refine ⟨Av, hAvbij, hAveq, C, ?_⟩
    intro fv fw hfw hf Rf BP hTC
    have hBP : BP = (P.orthogonalProjectionOnto ∘L
        fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν _ hf ∘L P.subtypeL) ∘L IP :=
      nested_compression_comp S P IΘ hIP Rf
        (fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν _ hf)
        (fullAEL2CuspidalIntegratedAction_val F G hPD hG T i hi I e hc ν _ hf)
    rw [hBP] at hTC ⊢
    exact hC fv fw hfw hf _ (fullAEL2CuspidalIntegratedAction_apply F G hPD hG T i hi I e hc ν _ hf) hTC

set_option maxHeartbeats 1000000 in
/-- **The isotypic trace factorization on a summand with a local occurrence.** If some
irreducible admissible representation of `G(F_v)` on a `Type u` carrier occurs in `P`, then the
conclusion of `GroupSchemeCuspidalIsotypicTraceFactorizationStatement` holds for `P`, with that
representation as `ρ`. -/
theorem cuspidalIsotypicTraceFactorization_of_exists_occurrence
    (μv : Measure (PlaceGroupPoints F G (.inr v))) [μv.IsHaarMeasure]
    (ν : Measure (AdelicGroupPoints F G)) [ν.IsHaarMeasure] :
    let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
    ∀ (P : Submodule ℂ S) [CompleteSpace P],
      (∀ (a : AdelicGroupPoints F G), ∀ x ∈ P, πc a x ∈ P) →
      (∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
        (∀ (a : AdelicGroupPoints F G), ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P) →
      (∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℂ V)
        (ρ : Representation ℂ (PlaceGroupPoints F G (.inr v)) V) (_ : IsAdmissible ρ),
        ρ.IsIrreducible ∧
        ∃ j₀ : V →ₗ[ℂ] S, j₀ ≠ 0 ∧ LinearMap.range j₀ ≤ P ∧
          ∀ y x, j₀ (ρ y x) = πc (ofPlace F G (.inr v) y) (j₀ x)) →
      ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℂ V)
        (ρ : Representation ℂ (PlaceGroupPoints F G (.inr v)) V) (hρ : IsAdmissible ρ),
        ρ.IsIrreducible ∧
        (∃ j₀ : V →ₗ[ℂ] S, j₀ ≠ 0 ∧ LinearMap.range j₀ ≤ P ∧
          ∀ y x, j₀ (ρ y x) = πc (ofPlace F G (.inr v) y) (j₀ x)) ∧
        (∀ (V' : Type u) [AddCommGroup V'] [Module ℂ V']
            (ρ' : Representation ℂ (PlaceGroupPoints F G (.inr v)) V'),
          IsSmooth ρ' → ρ'.IsIrreducible →
          ∀ j : V' →ₗ[ℂ] S, j ≠ 0 → LinearMap.range j ≤ P →
            (∀ y x, j (ρ' y x) = πc (ofPlace F G (.inr v) y) (j x)) →
            ∃ E : V' ≃ₗ[ℂ] V, ∀ y x, E (ρ' y x) = ρ y (E x)) ∧
        (∃ C : (AdelicGroupPoints F G → ℂ) → ℂ,
          ∀ (fv : SchwartzBruhat (PlaceGroupPoints F G (.inr v)))
            (fw : AdelicGroupPoints F G → ℂ),
            (∀ g x, fw (g * ofPlace F G (.inr v) x) = fw g) →
            ∀ hf : Integrable (fun g => fv (atPlace F G (.inr v) g) * fw g) ν,
              let RPf : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L
                fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν _ hf ∘L P.subtypeL
              IsTraceClass (E := (P : Submodule ℂ S)) RPf →
                operatorTrace (E := (P : Submodule ℂ S)) RPf =
                  Character.distribution μv ρ hρ fv * C fw) ∧
        ∀ (Θ : AdelicGroupPoints F G ≃ₜ* AdelicGroupPoints F G)
          (hΘ : ∀ x, Θ x ∈ positiveRationalSubgroup F G T i ↔
            x ∈ positiveRationalSubgroup F G T i)
          (hΘμ : MeasurePreserving
            (quotientAutomorphism (positiveRationalSubgroup F G T i) Θ hΘ).symm
            (positiveRationalQuotientHaarMeasure F G T i)
            (positiveRationalQuotientHaarMeasure F G T i))
          (θv : PlaceGroupPoints F G (.inr v) ≃ₜ* PlaceGroupPoints F G (.inr v)),
          (∀ g, atPlace F G (.inr v) (Θ g) = θv (atPlace F G (.inr v) g)) →
          (∀ x, Θ (ofPlace F G (.inr v) x) = ofPlace F G (.inr v) (θv x)) →
          let IΘ := twistOperator (positiveRationalSubgroup F G T i) Θ hΘ
            (positiveRationalQuotientHaarMeasure F G T i) hΘμ
          (∀ x ∈ P, ∃ y ∈ P, (y : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)) =
            IΘ (x : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i))) →
          ∃ Av : V →ₗ[ℂ] V, Function.Bijective Av ∧
            (∀ y w, Av (ρ y w) = ρ (θv y) (Av w)) ∧
            ∃ C : (AdelicGroupPoints F G → ℂ) → ℂ,
              ∀ (fv : SchwartzBruhat (PlaceGroupPoints F G (.inr v)))
                (fw : AdelicGroupPoints F G → ℂ),
                (∀ g x, fw (g * ofPlace F G (.inr v) x) = fw g) →
                ∀ hf : Integrable (fun g => fv (atPlace F G (.inr v) g) * fw g) ν,
                  let Rf := haarQuotientL2IntegratedAction F G T i hi I e hc ν _ hf
                  let BP : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L
                    (S.orthogonalProjectionOnto ∘L (Rf ∘L IΘ) ∘L S.subtypeL) ∘L P.subtypeL
                  IsTraceClass (E := (P : Submodule ℂ S)) BP →
                    operatorTrace (E := (P : Submodule ℂ S)) BP =
                      Langlands.BaseChange.twistedDistribution μv ρ hρ Av fv * C fw := by
  intro S πc P _ hPinv hPirr hocc
  obtain ⟨V, _, _, ρ, hρ, hρirr, j₀, hj₀0, hj₀P, hj₀⟩ := hocc
  obtain ⟨h0', h1, h2⟩ := cuspidalIsotypicTraceFactorization_of_occurrence F G v hPD hG T i hi I
    e hc μv ν P hPinv hPirr ρ hρ hρirr j₀ hj₀0 hj₀P hj₀
  exact ⟨V, _, _, ρ, hρ, hρirr, ⟨j₀, hj₀0, hj₀P, hj₀⟩, h0', h1, h2⟩

end Cuspidal

end Langlands.TraceFormula.IsotypicTrace
