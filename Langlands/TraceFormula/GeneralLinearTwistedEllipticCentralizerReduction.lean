import Langlands.TraceFormula.GeneralLinearTwistedEllipticCentralizerStatement
import Langlands.TraceFormula.GeneralLinearWeilTwistedGeometry
import Langlands.TraceFormula.TwistedOrbitHomeomorph
import Langlands.BaseChange.RegularOrbitParameters
import Mathlib.Algebra.Polynomial.Eval.Irreducible

/-! # Geometric inputs for the twisted elliptic centralizer theorem -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.GroupScheme Langlands.QuotientIntegration Langlands.JacquetLanglands
open Langlands.TraceFormula.AdelicGroupAutomorphism Langlands.BaseChange

namespace Langlands.TraceFormula

local instance twistedEllipticReductionGLAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance twistedEllipticReductionGLSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "Wₙ" => weilGroup K L GLₙ

set_option hygiene false in
local notation "Θₙ" => normOneAut K (unitGaloisAut K L GLₙ σ)

section Analytic

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
  (Γ : Subgroup G) (θ : G ≃ₜ* G) (r : G)

/-- The two measure conclusions associated with a twisted orbit and a principal subgroup. -/
def TwistedCentralizerAnalyticConditions : Prop :=
  (∀ [MeasurableSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ r)))]
      [BorelSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ r)))]
      (μC : Measure (twistedCentralizer θ r))
      [μC.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
      (νΓC : Measure (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ r)))),
      IsCompatible (Γ.subgroupOf (twistedCentralizer θ r)) μC Measure.count νΓC →
        νΓC Set.univ ≠ ⊤) ∧
  ∀ [MeasurableSpace (LeftQuotient (twistedCentralizer θ r))]
    [BorelSpace (LeftQuotient (twistedCentralizer θ r))]
    (μC : Measure (twistedCentralizer θ r))
    [μC.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
    (νC : Measure (LeftQuotient (twistedCentralizer θ r))),
    IsCompatible (twistedCentralizer θ r) (Measure.haar : Measure G) μC νC →
      ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
        Integrable (twistedOrbitFunction θ r φ) νC

/-- Compactness gives finite mass for the regular quotient measure. A closed
orbit gives integrability of each continuous compactly supported test function. -/
theorem twistedCentralizerAnalyticConditions_of_compact_closed
    [SigmaCompactSpace G] [T2Space G]
    (hcompact : IsCompactTwistedCentralizerQuotient Γ θ r)
    (hclosed : IsClosed (TwistedOrbit θ r)) : TwistedCentralizerAnalyticConditions Γ θ r := by
  constructor
  · intro _ _ μC _ _ _ νΓC hν
    let : CompactSpace (LeftQuotient (Γ.subgroupOf (twistedCentralizer θ r))) := hcompact
    let : νΓC.Regular := hν.regular
    exact isCompact_univ.measure_lt_top.ne
  · intro _ _ μC _ _ _ νC hν φ hφ hs
    let : νC.Regular := hν.regular
    exact twistedOrbitFunction_integrable_of_isClosed θ r hclosed νC φ hφ hs

end Analytic

section Transfer

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] {n l : ℕ} {σ : L ≃ₐ[K] L}

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 2000 in
/-- The two geometric facts give the analytic clauses at the rational
sigma-elliptic scope. -/
theorem generalLinearWeilTwistedAnalytic_of_compact_closed
    (hcompact : GeneralLinearWeilTwistedCompactQuotientStatement.{u})
    (hclosed : GeneralLinearWeilTwistedClosedOrbitStatement.{u})
    (hcyc : IsCyclicAlgebra σ l) (r : rationalNormOneSubgroup K Wₙ)
    (δ : GeneralLinear n L)
    (hr : cyclicWeilAdelicMap K L n r.val.val = AdelicGL.rational L n δ)
    (hδ : IsSigmaElliptic σ l δ) :
    TwistedCentralizerAnalyticConditions (rationalNormOneSubgroup K Wₙ) Θₙ
      (r : normOneSubgroup K Wₙ) := by
  let : SecondCountableTopology (normOneSubgroup K Wₙ) :=
    AdelicGroupPoints.normOneSecondCountableTopology K Wₙ
  let : LocallyCompactSpace (normOneSubgroup K Wₙ) :=
    AdelicGroupPoints.normOneLocallyCompactSpace K Wₙ
  let : SigmaCompactSpace (normOneSubgroup K Wₙ) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  let Γ := rationalNormOneSubgroup K Wₙ
  let φ := Θₙ
  let x : normOneSubgroup K Wₙ := r.val
  change TwistedCentralizerAnalyticConditions Γ φ x
  have hc : IsCompactTwistedCentralizerQuotient Γ φ x :=
    hcompact K L σ l hcyc n r δ hr hδ
  have ho : IsClosed (TwistedOrbit φ x) := hclosed K L σ l hcyc n r δ hr hδ
  exact twistedCentralizerAnalyticConditions_of_compact_closed Γ φ x hc ho

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
private theorem sigmaElliptic_of_mapped_norm {M : Type*} [Field M]
    (hcyc : IsCyclicAlgebra σ l) (δ : GeneralLinear n L) (f : L →+* M)
    (h : IsRegularElliptic (Matrix.GeneralLinearGroup.map f (cyclicNorm σ l δ))) :
    IsSigmaElliptic σ l δ := by
  obtain ⟨gbase, hassoc⟩ := (cyclicNormLemma K L σ l n hcyc).1 δ
  refine ⟨gbase, hassoc, ?_⟩
  have hpoly := charpoly_norm_of_associated hassoc
  have hp : ((Matrix.GeneralLinearGroup.map f (cyclicNorm σ l δ)).val).charpoly =
      gbase.val.charpoly.map (f.comp (algebraMap K L)) := by
    change ((cyclicNorm σ l δ).val.map f).charpoly = _
    rw [Matrix.charpoly_map, hpoly, Polynomial.map_map]
  have hsep := h.1
  change ((Matrix.GeneralLinearGroup.map f (cyclicNorm σ l δ)).val).charpoly.Separable at hsep
  have hirr := h.2
  rw [hp] at hsep hirr
  exact ⟨(Polynomial.separable_map _).mp hsep,
    Polynomial.Monic.irreducible_of_irreducible_map _ _ gbase.val.charpoly_monic hirr⟩

private theorem localProjection_rational (w : Global.FinitePlace L) (x : GeneralLinear n L) :
    FiniteAdelicGL.localProjection L n w (AdelicGL.finite L n (AdelicGL.rational L n x)) =
      Matrix.GeneralLinearGroup.map (algebraMap L (FiniteCompletion L w)) x := by
  ext i j
  rfl

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2000 in
private theorem generalLinearWeilAdelicMap_norm_rational
    (hcoords : GeneralLinearWeilAdelicTwistStatement.{u}) (x : AdelicGroupPoints K Wₙ)
    (δ : GeneralLinear n L)
    (hx : cyclicWeilAdelicMap K L n x = AdelicGL.rational L n δ) :
    cyclicWeilAdelicMap K L n
      ((List.range l).map fun k => adelicAut K (unitGaloisAut K L GLₙ σ ^ k) x).prod =
      AdelicGL.rational L n (cyclicNorm σ l δ) := by
  obtain ⟨⟨e, he⟩, htwist, _⟩ := hcoords K L n
  let terms := (List.range l).map fun k => adelicAut K (unitGaloisAut K L GLₙ σ ^ k) x
  have hterms : terms.map e = (List.range l).map
      (fun k => AdelicGL.rational L n (entrywiseAut (σ ^ k) n δ)) := by
    rw [show terms = _ from rfl, List.map_map]
    apply List.map_congr_left
    intro k _
    change e (adelicAut K (unitGaloisAut K L GLₙ σ ^ k) x) = _
    rw [show unitGaloisAut K L GLₙ σ ^ k = unitGaloisAut K L GLₙ (σ ^ k) from
      (map_pow (unitGaloisAutHom K L GLₙ) σ k).symm]
    calc
      _ = cyclicWeilAdelicMap K L n (adelicAut K (unitGaloisAut K L GLₙ (σ ^ k)) x) :=
        congrFun he _
      _ = AdelicGLTransport.adelicEquiv n ((σ ^ k : L ≃ₐ[K] L) : L ≃+* L)
          (cyclicWeilAdelicMap K L n x) := htwist _ _
      _ = _ := by rw [hx, AdelicGLTransport.adelicEquiv_rational]; rfl
  calc
    _ = e terms.prod := (congrFun he _).symm
    _ = (terms.map e).prod := map_list_prod e terms
    _ = _ := by
      rw [hterms, cyclicNorm, map_list_prod, List.map_map]
      rfl

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2000 in
/-- The finite-place ellipticity hypothesis on the actual adelic norm gives
a principal matrix whose rational cyclic norm is sigma-elliptic. -/
theorem exists_sigmaElliptic_rational_matrix_of_isRegularElliptic_localNorm
    (hcoords : GeneralLinearWeilAdelicTwistStatement.{u}) (hcyc : IsCyclicAlgebra σ l)
    (r : rationalNormOneSubgroup K Wₙ) (w : Global.FinitePlace L)
    (hw : IsRegularElliptic (FiniteAdelicGL.localProjection L n w (AdelicGL.finite L n
      (cyclicWeilAdelicMap K L n ((List.range l).map fun k =>
        adelicAut K (unitGaloisAut K L GLₙ σ ^ k) r.val.val).prod)))) :
    ∃ δ : GeneralLinear n L,
      cyclicWeilAdelicMap K L n r.val.val = AdelicGL.rational L n δ ∧
      IsSigmaElliptic σ l δ := by
  let x : AdelicGroupPoints K Wₙ := r.val.val
  have hr : x ∈ AdelicGroupPoints.rationalSubgroup K Wₙ :=
    (rationalNormOneSubgroupInclusion K Wₙ r).property
  obtain ⟨δ, hδ⟩ := ((hcoords K L n).2.2 x).mp hr
  change AdelicGL.rational L n δ = cyclicWeilAdelicMap K L n x at hδ
  change IsRegularElliptic (FiniteAdelicGL.localProjection L n w (AdelicGL.finite L n
    (cyclicWeilAdelicMap K L n
      ((List.range l).map fun k => adelicAut K (unitGaloisAut K L GLₙ σ ^ k) x).prod))) at hw
  rw [generalLinearWeilAdelicMap_norm_rational (σ := σ) hcoords x δ hδ.symm,
    localProjection_rational] at hw
  exact ⟨δ, hδ.symm, sigmaElliptic_of_mapped_norm hcyc δ _ hw⟩

end Transfer

end Langlands.TraceFormula
