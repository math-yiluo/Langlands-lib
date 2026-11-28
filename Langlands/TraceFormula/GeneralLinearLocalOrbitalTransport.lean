import Langlands.TraceFormula.NormOneThreePlaceOrbital
import Langlands.TraceFormula.GeneralLinearBaseChangeLocal
import Langlands.BaseChange.TwistedOrbitalEquiv
import Langlands.BaseChange.OrbitalMeasureExistence
import Langlands.Global.CompletionPadic
import Langlands.Group.GL.LocalFieldTopology

/-!
# Local orbital nonvanishing from the matrix model of `GL_n(K_v)`

See `GeneralLinearLocalOrbitalTransport.md`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
open Langlands.QuotientIntegration Langlands.BaseChange Langlands.JacquetLanglands

universe u

attribute [local instance high] BaseChange.leftQuotientMeasurableSpace
attribute [local instance] BaseChange.leftQuotient_borelSpace

local instance generalLinearOrbitalTransportIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The local twist of the identity automorphism is the identity. -/
theorem placeOne_apply (v : Langlands.Global.FinitePlace K)
    (x : PlaceGroupPoints K GLₙ (.inr v)) : placeOne K GLₙ v x = x := by
  rw [placeOne, GroupScheme.affinePointsTarget_apply]
  exact Category.comp_id x

/-- The Library's identification of the group-scheme local points with the matrix group
`GL_n(K_v)` of the completion `v.adicCompletion K`. -/
def localMatrixHomeomorph (v : Langlands.Global.FinitePlace K) :
    PlaceGroupPoints K GLₙ (.inr v) ≃ₜ* GeneralLinear n (v.adicCompletion K) :=
  localGLHomeomorph K n (.inr v)

set_option maxHeartbeats 1600000 in
/-- **Transport of local orbital nonvanishing.** Let `x` be a point of the group-scheme local
group `GLₙ(K_v)` whose image `γ` in the matrix group `GL_n(K_v)` is regular semisimple. If the
orbital integral of `φ` at `γ` is nonzero for every compatible choice of measures on the matrix
side, then compatible measures on the group-scheme side give a nonzero orbital integral of
`φ ∘ localGLHomeomorph` at `x`. -/
theorem localOrbitalNonvanishingAt_of_matrix (v : Langlands.Global.FinitePlace K)
    [MeasurableSpace (PlaceGroupPoints K GLₙ (.inr v))]
    [BorelSpace (PlaceGroupPoints K GLₙ (.inr v))]
    (φ : GeneralLinear n (v.adicCompletion K) → ℂ) (x : PlaceGroupPoints K GLₙ (.inr v))
    (hreg : IsRegularSemisimple (localMatrixHomeomorph K n v x))
    (hU :
      letI : ValuativeRel (v.adicCompletion K) :=
        (CompletionPadic.topologicalData v).valuativeRel;
      haveI : IsNonarchimedeanLocalField (v.adicCompletion K) :=
        (CompletionPadic.topologicalData v).localField;
      letI : MeasurableSpace (GeneralLinear n (v.adicCompletion K)) := borel _;
      haveI : BorelSpace (GeneralLinear n (v.adicCompletion K)) := ⟨rfl⟩;
      haveI := LocalFieldTopology.generalLinear_t2Space (v.adicCompletion K) n;
      haveI := LocalFieldTopology.generalLinear_locallyCompactSpace (v.adicCompletion K) n;
      ∀ (μF : Measure (GeneralLinear n (v.adicCompletion K))) [μF.IsHaarMeasure]
        (μγ : Measure (glCentralizer (localMatrixHomeomorph K n v x))) [μγ.IsHaarMeasure]
        [μγ.IsMulRightInvariant]
        (νγ : Measure (LeftQuotient (glCentralizer (localMatrixHomeomorph K n v x)))),
        IsCompatible (glCentralizer (localMatrixHomeomorph K n v x)) μF μγ νγ →
        orbitalIntegral (localMatrixHomeomorph K n v x) νγ φ ≠ 0) :
    LocalOrbitalNonvanishingAt K GLₙ v x (φ ∘ localMatrixHomeomorph K n v) := by
  let : ValuativeRel (v.adicCompletion K) := (CompletionPadic.topologicalData v).valuativeRel
  have : IsNonarchimedeanLocalField (v.adicCompletion K) :=
    (CompletionPadic.topologicalData v).localField
  let : MeasurableSpace (GeneralLinear n (v.adicCompletion K)) := borel _
  have : BorelSpace (GeneralLinear n (v.adicCompletion K)) := ⟨rfl⟩
  have := LocalFieldTopology.generalLinear_t2Space (v.adicCompletion K) n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace (v.adicCompletion K) n
  let a := localMatrixHomeomorph K n v
  let μF : Measure (GeneralLinear n (v.adicCompletion K)) := Measure.haar
  obtain ⟨⟨μγ, hH, hR⟩, hν⟩ := (orbitalMeasureExistence (v.adicCompletion K) (v.adicCompletion K)
    1 1 n isCyclicAlgebra_one μF μF).1 (a x) hreg
  obtain ⟨νγ, hc⟩ := hν μγ
  have hne : orbitalIntegral (a x) νγ φ ≠ 0 := hU μF μγ νγ hc
  let e := a.symm
  have he : ∀ y : GeneralLinear n (v.adicCompletion K),
      e (MonoidHom.id _ y) = placeOne K GLₙ v (e y) := fun y => (placeOne_apply K n v (e y)).symm
  have hcomp := isCompatible_map_twistedOrbit e (MonoidHom.id _) (placeOne K GLₙ v) he (a x)
    μF μγ νγ hc
  obtain ⟨-, horb⟩ := integrable_and_twistedOrbitalIntegral_map_equiv e (MonoidHom.id _)
    (placeOne K GLₙ v) he (a x) νγ (φ ∘ a)
  have hex : e (a x) = x := a.symm_apply_apply x
  let eH := twistedCentralizerEquiv e (MonoidHom.id _) (placeOne K GLₙ v) he (a x)
  have : (μF.map e).IsHaarMeasure := e.isHaarMeasure_map μF
  have : (μγ.map eH).IsHaarMeasure := eH.isHaarMeasure_map μγ
  have : (μγ.map eH).IsMulRightInvariant := isMulRightInvariant_map eH μγ
  have hfun : (φ ∘ a) ∘ e = φ := by
    funext y
    simp only [Function.comp_apply, e, ContinuousMulEquiv.apply_symm_apply]
  have key : LocalOrbitalNonvanishingAt K GLₙ v (e (a x)) (φ ∘ a) := by
    refine ⟨μF.map e, inferInstance, μγ.map eH, inferInstance, inferInstance, inferInstance, _,
      hcomp, ?_⟩
    rw [horb, hfun]
    exact hne
  rw [hex] at key
  exact key

end Langlands.TraceFormula
