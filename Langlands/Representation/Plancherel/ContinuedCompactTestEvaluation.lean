import Langlands.Representation.Plancherel.ContinuedIntertwiningCompactTest
import Langlands.Representation.Plancherel.UnramifiedCharacterTransport
import Langlands.HarmonicAnalysis.SmoothWeakIntegral

/-! # Integral normalization at every regular parameter -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.HarmonicAnalysis

namespace Langlands.Plancherel

open Aubert.General Induction UnramifiedOperatorFamily

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F))) [TopologicalSpace (rationalPoints L)]
  {G : Type*} [Group G] [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (hδ : IsUnimodularModulus U hU)
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hr : Continuous h.projection)
  (e : rationalPoints L ≃ₜ* M) (hν : ∀ ψ, Continuous (rationalNormCharacters L ψ).toMul)
  (A : SmoothRep ℂ M) (f : CompactInductionPicture h K A)
  {Y : Type*} [TopologicalSpace Y] (j : Y → G)

local notation "ν" => (fun ψ => Additive.toMul (rationalNormCharacters L ψ))
local notation "CharL" => unramifiedCharacters (G := rationalPoints L) ν
set_option quotPrecheck false in
local notation "νM" => (fun ψ => (ν ψ).comp e.symm.toMulEquiv.toMonoidHom)
local notation "ξ" => unramifiedCharactersHomeomorph e ν
set_option quotPrecheck false in
local notation "sectionValues" =>
  compactSectionFamily h hU hδ K hP hK hPK νM
    (fun ψ => (hν ψ).comp e.symm.continuous) hr A f

/-- The extensions of one compact section, restricted to a test space and
parameterized by the actual rational character group. -/
def compactTestSectionValues (y : Y) (z : CharL) : A :=
  sectionValues (j y) (ξ z)

local notation "B" => compactTestSectionValues L h hU hδ K hP hK hPK hr e hν A f j

private theorem compactTestSectionValues_locallyConstant (hj : Continuous j) :
    IsLocallyConstant B :=
  ((compactSectionFamily_isLocallyConstant h hU hδ K hP hK hPK νM
    (fun ψ => (hν ψ).comp e.symm.continuous) hr A f).comp
      (fun v => v ∘ ξ)).comp_continuous hj

private theorem compactTestSectionValues_hasCompactSupport
    (z₀ : CharL) (hc : HasCompactSupport (fun y => B y z₀)) :
    HasCompactSupport B :=
  (compactSectionFamily_hasCompactSupport h hU hδ K hP hK hPK νM
    (fun ψ => (hν ψ).comp e.symm.continuous) hr A f j (ξ z₀) hc).comp_left
      (g := fun v => v ∘ ξ) rfl

omit [TopologicalSpace Y] in
private theorem compactTestSectionValues_polynomial (y : Y) :
    IsPolynomialOn Set.univ (fun z => B y z.val) := by
  obtain ⟨m, v, he⟩ := unramifiedCompactExtension_eval_factor h hU hδ K hP hK hPK νM
    (fun ψ => (hν ψ).comp e.symm.continuous) hr A f (j y)
  refine ⟨1, fun _ => unramifiedEvaluationRegular ν (e.symm m), fun _ => v, ?_⟩
  intro z
  simp only [Fin.sum_univ_one, unramifiedEvaluationRegular_apply]
  exact he (ξ z.val)

section GeneralEvaluation

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {V W X : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ H X)
  [MeasurableSpace Y] [OpensMeasurableSpace Y] (qMeasure : Measure Y)
  [IsFiniteMeasureOnCompacts qMeasure]
  {Ω D : Set (unramifiedCharacters (G := rationalPoints L)
    (fun ψ => (rationalNormCharacters L ψ).toMul))} {T : Ω → V →ₗ[ℂ] W}

private theorem continuedOperator_integral_of_polynomialValues
    (hp : Continuous (rationalValuationImageProjection L)) (hL : IsConnectedReductive L)
    (p : RationalOperatorContinuationData Ω T) (E : W →ₗ[ℂ] X) (v : V)
    (b : Y → CharL → X)
    (hlc : IsLocallyConstant b) (hc : HasCompactSupport b)
    (hb : ∀ y, IsPolynomialOn Set.univ (fun w => b y w.val))
    (hρ : IsSmooth ρ) (hcofinal : ∀ J : OpenSubgroup H, ∃ J' : OpenSubgroup H,
      IsCompact (J' : Set H) ∧ J' ≤ J)
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)
    (hStart : ∀ w : D,
      SmoothWeakIntegral.HasIntegral ρ qMeasure (fun y => b y w.val)
        (E (T ⟨w.val, hDΩ w.property⟩ v)))
    (z : p.regularRegion) (ℓ : X →ₗ[ℂ] ℂ) :
    Integrable (fun y => ℓ (b y z.val)) qMeasure ∧
      ℓ (E (p.continuedOperator z v)) = (∫ y, ℓ (b y z.val) ∂qMeasure) := by
  let restrict (a : CharL → X) (w : (Set.univ : Set CharL)) := a w.val
  let b' (y : Y) := restrict (b y)
  have hlc' : IsLocallyConstant b' := hlc.comp restrict
  have hc' : HasCompactSupport b' := hc.comp_left (g := restrict) rfl
  let C (w : CharL) := compactParametricIntegral qMeasure b' hlc' hc' ⟨w, Set.mem_univ w⟩
  have hC : IsPolynomialOn (Set.univ : Set CharL) (fun w => C w.val) :=
    isPolynomialOn_compactParametricIntegral qMeasure b' hlc' hc' hb
  have hE (w : CharL) (hw : w ∈ D) : E (T ⟨w, hDΩ hw⟩ v) = C w :=
    SmoothWeakIntegral.HasIntegral.unique hcofinal hρ (hStart ⟨w, hw⟩) (fun φ =>
      let ht := compactParametricIntegral_spec qMeasure b' hlc' hc' ⟨w, Set.mem_univ w⟩ φ.val
      ⟨ht.1, ht.2.symm⟩)
  rw [continuedOperator_map_eq_polynomial_of_eqOn L hp hL p hD hne hDΩ E v C hC hE z]
  exact compactParametricIntegral_spec qMeasure b' hlc' hc' ⟨z.val, Set.mem_univ z.val⟩ ℓ

end GeneralEvaluation

variable [MeasurableSpace Y] [OpensMeasurableSpace Y] (qMeasure : Measure Y)
  [IsFiniteMeasureOnCompacts qMeasure]
  {W : Type*} [AddCommGroup W] [Module ℂ W]
  {Ω D : Set (unramifiedCharacters (G := rationalPoints L)
    (fun ψ => (rationalNormCharacters L ψ).toMul))} {T : Ω → CompactInductionPicture h K A →ₗ[ℂ] W}

/-- A compact-section normalization on an open part of the original domain
persists at all regular parameters, for every algebraic linear test. -/
theorem continuedOperator_compactTest_integral
    (hp : Continuous (rationalValuationImageProjection L)) (hL : IsConnectedReductive L)
    (p : RationalOperatorContinuationData Ω T) (E : W →ₗ[ℂ] A)
    (hj : Continuous j) (z₀ : CharL)
    (hc : HasCompactSupport (fun y => B y z₀))
    (hcofinal : ∀ J : OpenSubgroup M, ∃ J' : OpenSubgroup M,
      IsCompact (J' : Set M) ∧ J' ≤ J)
    (hD : IsOpen D) (hne : D.Nonempty) (hDΩ : D ⊆ Ω)
    (hStart : ∀ w : D,
      SmoothWeakIntegral.HasIntegral A.representation qMeasure (fun y => B y w.val)
        (E (T ⟨w.val, hDΩ w.property⟩ f)))
    (z : p.regularRegion) (ℓ : A →ₗ[ℂ] ℂ) :
    Integrable (fun y => ℓ (B y z.val)) qMeasure ∧
      ℓ (E (p.continuedOperator z f)) = (∫ y, ℓ (B y z.val) ∂qMeasure) :=
  continuedOperator_integral_of_polynomialValues L A.representation qMeasure hp hL p E f B
    (compactTestSectionValues_locallyConstant L h hU hδ K hP hK hPK hr e hν A f j hj)
    (compactTestSectionValues_hasCompactSupport L h hU hδ K hP hK hPK hr e hν A f j z₀ hc)
    (compactTestSectionValues_polynomial L h hU hδ K hP hK hPK hr e hν A f j)
    A.property hcofinal hD hne hDΩ hStart z ℓ

end Langlands.Plancherel
