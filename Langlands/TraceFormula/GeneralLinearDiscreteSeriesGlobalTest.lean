import Langlands.TraceFormula.GlobalizationFiniteTest
import Langlands.TraceFormula.GeneralLinearOrdinaryOrbitIsolation
import Langlands.TraceFormula.GeneralLinearTensorSingleOrbitTrace
import Langlands.TraceFormula.GeneralLinearTensorCuspidalHilbertSchmidtPositiveRank
import Langlands.TraceFormula.GlobalizationQuotientConvolution
import Langlands.TraceFormula.GeneralLinearEllipticCentralizerProof
import Langlands.TraceFormula.AdelicRegularCentralizer
import Langlands.TraceFormula.GroupSchemeCuspidalImageProof
import Langlands.Global.RationalGLWeakApproximation
import Langlands.Global.ArchimedeanNormalizedKernelProof
import Langlands.Global.GlobalPlaceTopologyFacts
import Langlands.BaseChange.RegularEllipticOpen
import Langlands.BaseChange.SplitEllipticAuxiliary

/-!
# A global test with prescribed local factors and nonzero cuspidal trace

See `GeneralLinearDiscreteSeriesGlobalTest.md`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme Langlands.QuotientIntegration Langlands.JacquetLanglands
open Langlands.HarmonicAnalysis Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis.OperatorIdeals

universe u

section Helpers

/-- In a locally compact Hausdorff totally disconnected space every neighbourhood of a point
contains a compact clopen neighbourhood. -/
theorem exists_isCompact_isClopen_mem_subset {X : Type*} [TopologicalSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [LocallyCompactSpace X] {x : X} {V : Set X} (hV : IsOpen V)
    (hx : x ∈ V) : ∃ W : Set X, IsCompact W ∧ IsClopen W ∧ x ∈ W ∧ W ⊆ V := by
  obtain ⟨s, hs, hxs, hsV⟩ := exists_compact_subset hV hx
  obtain ⟨W, hW, hxW, hWs⟩ := exists_isClopen_mem_of_isOpen isOpen_interior hxs
  exact ⟨W, hs.of_isClosed_subset hW.isClosed (hWs.trans interior_subset), hW, hxW,
    (hWs.trans interior_subset).trans hsV⟩

/-- A complex number that is a nonnegative real. -/
def IsNonnegReal (z : ℂ) : Prop := 0 ≤ z.re ∧ z.im = 0

theorem IsNonnegReal.mul {z w : ℂ} (hz : IsNonnegReal z) (hw : IsNonnegReal w) :
    IsNonnegReal (z * w) := by
  refine ⟨?_, ?_⟩
  · rw [Complex.mul_re, hz.2, zero_mul, sub_zero]
    exact mul_nonneg hz.1 hw.1
  · rw [Complex.mul_im, hz.2, hw.2, mul_zero, zero_mul, add_zero]

theorem IsNonnegReal.mul_pos {z w : ℂ} (hz : IsNonnegReal z) (_hw : IsNonnegReal w)
    (hz' : 0 < z.re) (hw' : 0 < w.re) : 0 < (z * w).re := by
  rw [Complex.mul_re, hz.2, zero_mul, sub_zero]
  exact _root_.mul_pos hz' hw'

theorem isNonnegReal_prod {Idx : Type*} (s : Finset Idx) (f : Idx → ℂ)
    (hf : ∀ i ∈ s, IsNonnegReal (f i)) : IsNonnegReal (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact ⟨zero_le_one, Complex.one_im⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).mul (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem isNonnegReal_indicator {X : Type*} (U : Set X) (x : X) :
    IsNonnegReal (U.indicator (fun _ => (1 : ℂ)) x) := by
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx]
    exact ⟨zero_le_one, Complex.one_im⟩
  · rw [Set.indicator_of_notMem hx]
    exact ⟨le_refl _, Complex.zero_im⟩

end Helpers

section Kernel

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- A smooth compactly supported archimedean kernel with nonnegative real values that is positive
at a prescribed point. -/
theorem exists_nonneg_kernel_pos (g₀ : InfiniteAdelicGL K n) :
    ∃ a : ArchimedeanGL.SmoothCompactKernel K n,
      (∀ g, IsNonnegReal (ArchimedeanGL.kernelToContinuousMap K n a g)) ∧
        0 < (ArchimedeanGL.kernelToContinuousMap K n a g₀).re := by
  let := ArchimedeanGL.borelMeasurableSpace K n
  have := ArchimedeanGL.borelMeasurableSpace_borelSpace K n
  obtain ⟨κ, -, hnn, hpos, -⟩ := ArchimedeanGL.normalizedCompactKernel K n
    (Measure.haar : Measure (InfiniteAdelicGL K n)) Set.univ Filter.univ_mem
  refine ⟨⟨ArchimedeanGL.smoothRightAction K n g₀⁻¹ κ.val, ?_⟩, fun g => hnn (g * g₀⁻¹), ?_⟩
  · change HasCompactSupport (fun x => κ.val.val (x * g₀⁻¹))
    exact κ.property.comp_homeomorph (Homeomorph.mulRight g₀⁻¹)
  · change 0 < (κ.val.val (g₀ * g₀⁻¹)).re
    rw [mul_inv_cancel]
    exact hpos

end Kernel

section Regular

variable {K : Type u} [Field K] {n : ℕ}

theorem isRegularSemisimple_of_map {L : Type*} [Field L] [Algebra K L] (g : GeneralLinear n K)
    (h : IsRegularSemisimple (Matrix.GeneralLinearGroup.map (algebraMap K L) g)) :
    IsRegularSemisimple g := by
  change (g.val.map (algebraMap K L)).charpoly.Separable at h
  rw [Matrix.charpoly_map] at h
  exact (Polynomial.separable_map _).mp h

theorem isRegularSemisimple_map {L : Type*} [Field L] [Algebra K L] (g : GeneralLinear n K)
    (h : IsRegularSemisimple g) :
    IsRegularSemisimple (Matrix.GeneralLinearGroup.map (algebraMap K L) g) := by
  change (g.val.map (algebraMap K L)).charpoly.Separable
  rw [Matrix.charpoly_map]
  exact (Polynomial.separable_map _).mpr h

end Regular

/-- The regular elliptic elements of `GL_{r+1}(K_v)` form a nonempty open set. -/
theorem regularEllipticSet_isOpen_nonempty {K : Type u} [Field K] [NumberField K]
    (v : Langlands.Global.FinitePlace K) (r : ℕ) :
    IsOpen {g : GeneralLinear (r + 1) (FiniteCompletion K v) | IsRegularElliptic g} ∧
      {g : GeneralLinear (r + 1) (FiniteCompletion K v) | IsRegularElliptic g}.Nonempty := by
  let : ValuativeRel (v.adicCompletion K) := (CompletionPadic.topologicalData v).valuativeRel
  have : IsNonarchimedeanLocalField (v.adicCompletion K) :=
    (CompletionPadic.topologicalData v).localField
  have : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  obtain ⟨g, hg, -⟩ := BaseChange.exists_regularElliptic_trace_ne_zero (v.adicCompletion K) r
  exact ⟨BaseChange.isOpen_regularElliptic (v.adicCompletion K) (r + 1), g, hg⟩

section Characteristic

variable {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsClopen s) (hc : IsCompact s)

theorem characteristic_ne_zero_iff (x : X) :
    Hecke.TestFunction.characteristic hs hc x ≠ 0 ↔ x ∈ s := by
  rw [Hecke.TestFunction.characteristic_apply]
  by_cases hx : x ∈ s
  · simp [hx]
  · simp [hx]

theorem characteristic_eq_one {x : X} (hx : x ∈ s) :
    Hecke.TestFunction.characteristic hs hc x = 1 := by
  rw [Hecke.TestFunction.characteristic_apply, Set.indicator_of_mem hx]

theorem tsupport_characteristic_subset :
    tsupport (Hecke.TestFunction.characteristic hs hc : X → ℂ) ⊆ s :=
  closure_minimal (fun x hx => (characteristic_ne_zero_iff hs hc x).mp hx) hs.isClosed

theorem isNonnegReal_characteristic (x : X) :
    IsNonnegReal (Hecke.TestFunction.characteristic hs hc x) := by
  rw [Hecke.TestFunction.characteristic_apply]
  exact isNonnegReal_indicator s x

end Characteristic

section NormOne

variable (K : Type u) [Field K] [NumberField K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
  (hc : IsCentral i)

attribute [local instance high] BaseChange.leftQuotientMeasurableSpace
attribute [local instance] BaseChange.leftQuotient_borelSpace

/-- The norm-one orbital integral of the positive average of a nonnegative compactly supported
continuous function that is positive at `δ` is nonzero, when continuous compactly supported
functions have integrable orbit functions. -/
theorem normOnePositiveAverage_orbitalIntegral_ne_zero
    (f : C_c(AdelicGroupPoints K G, ℂ)) (hnn : ∀ g, 0 ≤ (f g).re) (δ : normOneSubgroup K G)
    (hδ : 0 < (f (δ : AdelicGroupPoints K G)).re)
    (μC : Measure (twistedCentralizer (MonoidHom.id (normOneSubgroup K G)) δ))
    [μC.IsMulRightInvariant]
    (ν : Measure (LeftQuotient (twistedCentralizer (MonoidHom.id (normOneSubgroup K G)) δ)))
    (hν : IsCompatible _ (Measure.haar : Measure (normOneSubgroup K G)) μC ν)
    (hint : ∀ φ : normOneSubgroup K G → ℂ, Continuous φ → HasCompactSupport φ →
      Integrable (twistedOrbitFunction (MonoidHom.id (normOneSubgroup K G)) δ φ) ν) :
    twistedOrbitalIntegral (MonoidHom.id (normOneSubgroup K G)) δ ν
      (normOnePositiveAverage K G T i (normalizedPositiveHaarMeasure K G T i hi I e hc) f) ≠ 0 := by
  let fOne := globalizationNormOneAverage K G T i hi I e hc f
  have heq : normOnePositiveAverage K G T i (normalizedPositiveHaarMeasure K G T i hi I e hc) f =
      fOne := rfl
  rw [heq]
  exact twistedOrbitalIntegral_ne_zero_of_re_nonneg (MonoidHom.id (normOneSubgroup K G)) δ
    Measure.haar μC ν hν fOne fOne.continuous continuous_id
    (fun z => normOnePositiveAverage_re_nonneg K G T i _ f hnn z)
    (normOnePositiveAverage_re_pos K G T i hi I e hc f hnn δ hδ)
    (hint fOne fOne.continuous fOne.hasCompactSupport)

end NormOne

section Global

local instance globalTestIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance globalTestSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of K)

attribute [local instance high] BaseChange.leftQuotientMeasurableSpace
attribute [local instance] BaseChange.leftQuotient_borelSpace

set_option maxRecDepth 4000 in
set_option maxHeartbeats 16000000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- **A global test with prescribed local factors and nonzero cuspidal trace.** Let
`v₀, v₁, v₂` be distinct finite places and `Φ` a family of local tests such that `Φ_{v₁}` has
vanishing constant terms and, at each `vᵢ`, there is a nonempty open set of `GL_{r+1}(K_{vᵢ})` on
which all orbital integrals of `Φ_{vᵢ}` are nonzero. There is a finite set `S ∋ v₀, v₁, v₂`, local
tests `F` agreeing with `Φ` at those three places, and an archimedean kernel `a`, such that the operator of
`a ⊗ ⨂_{v ∈ S} F_v ⊗ 1_{∏_{v ∉ S} GL_{r+1}(𝒪_v)}` on `L²` is trace class with nonzero trace and
maps into the cuspidal subspace. -/
theorem exists_globalTest_trace_ne_zero
    (K : Type u) [Field K] [NumberField K] (r : ℕ)
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive GLₙ)
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ GLₙ)
    (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
    (hc : IsCentral i) [(Measure.haar : Measure (normOneSubgroup K GLₙ)).IsMulRightInvariant]
    [∀ v : Langlands.Global.FinitePlace K, T2Space (GeneralLinear (r + 1) (FiniteCompletion K v))]
    [∀ v : Langlands.Global.FinitePlace K,
      LocallyCompactSpace (GeneralLinear (r + 1) (FiniteCompletion K v))]
    [∀ v : Langlands.Global.FinitePlace K,
      TotallyDisconnectedSpace (GeneralLinear (r + 1) (FiniteCompletion K v))]
    (v₀ v₁ v₂ : Langlands.Global.FinitePlace K) (h01 : v₀ ≠ v₁) (h02 : v₀ ≠ v₂) (h12 : v₁ ≠ v₂)
    (Φ : ∀ v : Langlands.Global.FinitePlace K, SchwartzBruhat (FiniteLocalGL K (r + 1) v))
    (hcusp : BaseChange.HasVanishingConstantTerms (Φ v₁ : FiniteLocalGL K (r + 1) v₁ → ℂ))
    (hU : ∀ v : Langlands.Global.FinitePlace K, v = v₀ ∨ v = v₁ ∨ v = v₂ →
      ∃ U : Set (GeneralLinear (r + 1) (v.adicCompletion K)), IsOpen U ∧ U.Nonempty ∧
        ∀ g ∈ U,
          letI : ValuativeRel (v.adicCompletion K) :=
            (CompletionPadic.topologicalData v).valuativeRel;
          haveI : IsNonarchimedeanLocalField (v.adicCompletion K) :=
            (CompletionPadic.topologicalData v).localField;
          letI : MeasurableSpace (GeneralLinear (r + 1) (v.adicCompletion K)) := borel _;
          haveI : BorelSpace (GeneralLinear (r + 1) (v.adicCompletion K)) := ⟨rfl⟩;
          haveI := LocalFieldTopology.generalLinear_t2Space (v.adicCompletion K) (r + 1);
          haveI := LocalFieldTopology.generalLinear_locallyCompactSpace (v.adicCompletion K) (r + 1);
          ∀ (μF : Measure (GeneralLinear (r + 1) (v.adicCompletion K))) [μF.IsHaarMeasure]
            (μγ : Measure (BaseChange.glCentralizer g)) [μγ.IsHaarMeasure] [μγ.IsMulRightInvariant]
            (νγ : Measure (LeftQuotient (BaseChange.glCentralizer g))),
            IsCompatible (BaseChange.glCentralizer g) μF μγ νγ → orbitalIntegral g νγ (Φ v) ≠ 0) :
    ∃ (S : Finset (Langlands.Global.FinitePlace K))
      (F : ∀ v : Langlands.Global.FinitePlace K, SchwartzBruhat (FiniteLocalGL K (r + 1) v))
      (a : ArchimedeanGL.SmoothCompactKernel K (r + 1)),
      v₀ ∈ S ∧ v₁ ∈ S ∧ v₂ ∈ S ∧ F v₀ = Φ v₀ ∧ F v₁ = Φ v₁ ∧ F v₂ = Φ v₂ ∧
      ∃ h : Integrable (GlobalizationTensor.fullTest K (r + 1) S F a)
          (Measure.haar : Measure (AdelicGroupPoints K GLₙ)),
        IsTraceClass (haarQuotientL2IntegratedAction K GLₙ T i hi I e hc Measure.haar _ h) ∧
        (∀ φ, haarQuotientL2IntegratedAction K GLₙ T i hi I e hc Measure.haar _ h φ ∈
          fullAEL2CuspidalSubmodule K GLₙ hPD hG T i hi I e hc) ∧
        operatorTrace (haarQuotientL2IntegratedAction K GLₙ T i hi I e hc Measure.haar _ h) ≠ 0 := by
  classical
  let E := GeneralLinearGroupPoints.adelicHomeomorph K (r + 1)
  let H := normOneSubgroup K GLₙ
  let RG := rationalNormOneSubgroup K GLₙ
  let ρA := normalizedPositiveHaarMeasure K GLₙ T i hi I e hc
  let gmap (v : Langlands.Global.FinitePlace K) :
      GeneralLinear (r + 1) K →* GeneralLinear (r + 1) (FiniteCompletion K v) :=
    Matrix.GeneralLinearGroup.map (algebraMap K (FiniteCompletion K v))
  -- the auxiliary place and the open sets
  have : Infinite (Langlands.Global.FinitePlace K) := numberField_finitePlaces_infinite K
  let T₀ : Finset (Langlands.Global.FinitePlace K) := {v₀, v₁, v₂}
  have hT₀ (v : Langlands.Global.FinitePlace K) : v ∈ T₀ ↔ v = v₀ ∨ v = v₁ ∨ v = v₂ := by
    simp [T₀]
  have h0T : v₀ ∈ T₀ := (hT₀ v₀).mpr (Or.inl rfl)
  have h1T : v₁ ∈ T₀ := (hT₀ v₁).mpr (Or.inr (Or.inl rfl))
  have h2T : v₂ ∈ T₀ := (hT₀ v₂).mpr (Or.inr (Or.inr rfl))
  obtain ⟨v₃, hv₃⟩ := Infinite.exists_notMem_finset T₀
  have hUT (v : Langlands.Global.FinitePlace K) (hv : v ∈ T₀) := hU v ((hT₀ v).mp hv)
  choose Uloc hUo hUne hUorb using hUT
  let W (v : Langlands.Global.FinitePlace K) : Set (GeneralLinear (r + 1) (FiniteCompletion K v)) :=
    if h : v ∈ T₀ then Uloc v h else {g | IsRegularElliptic g}
  have hWo (v : Langlands.Global.FinitePlace K) : IsOpen (W v) := by
    by_cases h : v ∈ T₀
    · simp only [W, h, ↓reduceDIte]
      exact hUo v h
    · simp only [W, h, ↓reduceDIte]
      exact (regularEllipticSet_isOpen_nonempty v r).1
  have hWne (v : Langlands.Global.FinitePlace K) : (W v).Nonempty := by
    by_cases h : v ∈ T₀
    · simp only [W, h, ↓reduceDIte]
      exact hUne v h
    · simp only [W, h, ↓reduceDIte]
      exact (regularEllipticSet_isOpen_nonempty v r).2
  let S₀ : Finset (Langlands.Global.FinitePlace K) := insert v₃ T₀
  obtain ⟨x₀, hx₀⟩ := (rationalGLWeakApproximation K (r + 1) S₀).exists_mem_open
    (isOpen_set_pi Set.finite_univ fun v _ => hWo v.val)
    (Set.univ_pi_nonempty_iff.mpr fun v => hWne v.val)
  have hxW (v : Langlands.Global.FinitePlace K) (hv : v ∈ S₀) : gmap v x₀ ∈ W v :=
    hx₀ ⟨v, hv⟩ (Set.mem_univ _)
  have hv₃S₀ : v₃ ∈ S₀ := Finset.mem_insert_self _ _
  have hRE₃ : IsRegularElliptic (gmap v₃ x₀) := by
    have h := hxW v₃ hv₃S₀
    simp only [W, hv₃, ↓reduceDIte] at h
    exact h
  have hmemU (v : Langlands.Global.FinitePlace K) (hv : v ∈ T₀) : gmap v x₀ ∈ Uloc v hv := by
    have h := hxW v (Finset.mem_insert_of_mem hv)
    simp only [W, hv, ↓reduceDIte] at h
    exact h
  have hRS : IsRegularSemisimple x₀ := isRegularSemisimple_of_map x₀ hRE₃.isRegularSemisimple
  -- the rational point
  let q₀ : RationalGroupPoints K GLₙ := (GeneralLinearGroupPoints.rationalEquiv K (r + 1)).symm x₀
  have hq₀ : GeneralLinearGroupPoints.rationalEquiv K (r + 1) q₀ = x₀ :=
    MulEquiv.apply_symm_apply _ _
  let r₀ : RG := ⟨rationalNormOne K GLₙ q₀, q₀, rfl⟩
  have hEr₀ : E ((r₀ : H) : AdelicGroupPoints K GLₙ) = AdelicGL.rational K (r + 1) x₀ := by
    change E (AdelicGroupPoints.rational K GLₙ q₀) = _
    rw [GeneralLinearGroupPoints.adelicHomeomorph_rational, hq₀]
  have hcomp (v : Langlands.Global.FinitePlace K) :
      FiniteAdelicGL.localProjection K (r + 1) v
        (AdelicGL.finite K (r + 1) (E ((r₀ : H) : AdelicGroupPoints K GLₙ))) = gmap v x₀ := by
    rw [hEr₀]
    exact localProjection_finite_rational K (r + 1) v x₀
  have hproj (v : Langlands.Global.FinitePlace K) :
      localMatrixHomeomorph K (r + 1) v (normOneFinitePlaceProjection K GLₙ v (r₀ : H)) =
        gmap v x₀ :=
    (GlobalizationTensor.finiteComponent_adelicHomeomorph K (r + 1) v _).symm.trans (hcomp v)
  -- integrality away from a finite set
  have hev := FiniteAdelicGL.eventually_localIntegral K (r + 1)
    (AdelicGL.finite K (r + 1) (AdelicGL.rational K (r + 1) x₀))
  let Sbad : Finset (Langlands.Global.FinitePlace K) := (Filter.eventually_cofinite.mp hev).toFinset
  let S : Finset (Langlands.Global.FinitePlace K) := S₀ ∪ Sbad
  have hint (v : Langlands.Global.FinitePlace K) (hv : v ∉ S) :
      gmap v x₀ ∈ FiniteAdelicGL.localIntegral K (r + 1) v := by
    have h : v ∉ Sbad := fun h => hv (Finset.mem_union_right _ h)
    simp only [Sbad, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at h
    rwa [localProjection_finite_rational] at h
  have hS₀S : S₀ ⊆ S := Finset.subset_union_left
  have h0S : v₀ ∈ S := hS₀S (Finset.mem_insert_of_mem h0T)
  have h1S : v₁ ∈ S := hS₀S (Finset.mem_insert_of_mem h1T)
  have h2S : v₂ ∈ S := hS₀S (Finset.mem_insert_of_mem h2T)
  have h3S : v₃ ∈ S := hS₀S hv₃S₀
  -- compact open neighbourhoods
  have hB (v : Langlands.Global.FinitePlace K) :
      ∃ B : Set (GeneralLinear (r + 1) (FiniteCompletion K v)), IsCompact B ∧ IsClopen B ∧
        gmap v x₀ ∈ B ∧ (v = v₃ → B ⊆ {g | IsRegularElliptic g}) := by
    by_cases hv : v = v₃
    · subst hv
      obtain ⟨B, h1, h2, h3, h4⟩ := exists_isCompact_isClopen_mem_subset
        (regularEllipticSet_isOpen_nonempty v r).1 hRE₃
      exact ⟨B, h1, h2, h3, fun _ => h4⟩
    · obtain ⟨B, h1, h2, h3, -⟩ := exists_isCompact_isClopen_mem_subset isOpen_univ
        (Set.mem_univ (gmap v x₀))
      exact ⟨B, h1, h2, h3, fun h => absurd h hv⟩
  choose B hBc hBcl hBx hBRE using hB
  let bump (v : Langlands.Global.FinitePlace K) : SchwartzBruhat (FiniteLocalGL K (r + 1) v) :=
    Hecke.TestFunction.characteristic (hBcl v) (hBc v)
  -- the archimedean kernel
  obtain ⟨a, ha_nn, ha_pos⟩ := exists_nonneg_kernel_pos K (r + 1)
    (AdelicGL.infinite K (r + 1) (AdelicGL.rational K (r + 1) x₀))
  -- the support bound
  let F₀ (v : Langlands.Global.FinitePlace K) : SchwartzBruhat (FiniteLocalGL K (r + 1) v) :=
    if v ∈ T₀ then Φ v else bump v
  have hF₀v₃ : F₀ v₃ = bump v₃ := by simp only [F₀, hv₃, ↓reduceIte]
  have hf₀c : HasCompactSupport
      (adelicTestTensor K (r + 1) a (GlobalizationTensor.finiteTest K (r + 1) S F₀)) :=
    CompactSmoothAdelicGLTest.hasCompactSupport K (r + 1) (CompactSmoothAdelicGLTest.tensor K (r + 1) a _)
  have hf₀Gc : HasCompactSupport (fun g : AdelicGroupPoints K GLₙ =>
      adelicTestTensor K (r + 1) a (GlobalizationTensor.finiteTest K (r + 1) S F₀) (E g)) :=
    hf₀c.comp_homeomorph E.toHomeomorph
  obtain ⟨C, hCc, hCcoord, hCavg⟩ := positiveAverageOrbitSupport K GLₙ T i hi I e _ hf₀Gc
  have hcoordE (y z : AdelicGroupPoints K GLₙ)
      (h : ∀ v : Langlands.Global.FinitePlace K, atPlace K GLₙ (.inr v) y = atPlace K GLₙ (.inr v) z)
      (v : Langlands.Global.FinitePlace K) :
      FiniteAdelicGL.localProjection K (r + 1) v (AdelicGL.finite K (r + 1) (E z)) =
        FiniteAdelicGL.localProjection K (r + 1) v (AdelicGL.finite K (r + 1) (E y)) := by
    change GlobalizationTensor.finiteComponent K (r + 1) v (E z) =
      GlobalizationTensor.finiteComponent K (r + 1) v (E y)
    rw [GlobalizationTensor.finiteComponent_adelicHomeomorph,
      GlobalizationTensor.finiteComponent_adelicHomeomorph, h v]
  have hEll : ∀ z ∈ C, IsRegularElliptic (FiniteAdelicGL.localProjection K (r + 1) v₃
      (AdelicGL.finite K (r + 1) (E z))) := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hCcoord z hz
    rw [hcoordE y z hyz v₃]
    have hsub : tsupport (fun g : AdelicGroupPoints K GLₙ =>
        adelicTestTensor K (r + 1) a (GlobalizationTensor.finiteTest K (r + 1) S F₀) (E g)) ⊆
        E ⁻¹' tsupport
          (adelicTestTensor K (r + 1) a (GlobalizationTensor.finiteTest K (r + 1) S F₀)) :=
      closure_minimal (fun w hw => subset_tsupport
          (adelicTestTensor K (r + 1) a (GlobalizationTensor.finiteTest K (r + 1) S F₀)) hw)
        ((isClosed_tsupport _).preimage E.continuous)
    have hy' := hsub hy
    have h1 := GlobalizationTensor.finiteComponent_mem_tsupport K (r + 1) S F₀ a v₃ h3S (E y) hy'
    rw [hF₀v₃] at h1
    exact hBRE v₃ rfl (tsupport_characteristic_subset (hBcl v₃) (hBc v₃) h1)
  -- isolation of the rational class
  have hreg₀ : IsRegularSemisimple (GeneralLinearGroupPoints.rationalEquiv K (r + 1) q₀) := by
    rw [hq₀]
    exact hRS
  obtain ⟨Ui, hUic, hUicl, hxUi, hUiB, hiso⟩ := ordinaryOrbitIsolation K (r + 1) v₃ C hCc hEll q₀
    hreg₀ (B v₃) (hBcl v₃).isOpen (by rw [hq₀]; exact hBx v₃)
  rw [hq₀] at hxUi
  let cut : SchwartzBruhat (FiniteLocalGL K (r + 1) v₃) :=
    Hecke.TestFunction.characteristic hUicl hUic
  let F := Function.update F₀ v₃ cut
  have hFv₃ : F v₃ = cut := Function.update_self _ _ _
  have hFne (v : Langlands.Global.FinitePlace K) (hv : v ≠ v₃) : F v = F₀ v :=
    Function.update_of_ne hv _ _
  have hFT₀ (v : Langlands.Global.FinitePlace K) (hv : v ∈ T₀) : F v = Φ v := by
    rw [hFne v (fun h => hv₃ (h ▸ hv))]
    simp only [F₀, hv, ↓reduceIte]
  have hfac (F' : ∀ v : Langlands.Global.FinitePlace K, SchwartzBruhat (FiniteLocalGL K (r + 1) v))
      (g : AdelicGL K (r + 1))
      (hg : adelicTestTensor K (r + 1) a (GlobalizationTensor.finiteTest K (r + 1) S F') g ≠ 0)
      (v : Langlands.Global.FinitePlace K) (hv : v ∈ S) :
      F' v (GlobalizationTensor.finiteComponent K (r + 1) v g) ≠ 0 := by
    rw [GlobalizationTensor.adelicTestTensor_finiteTest] at hg
    have h2 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hg).2).1
    exact (Finset.prod_ne_zero_iff.mp h2) ⟨v, hv⟩ (Finset.mem_univ _)
  have hsuppΩ : Function.support (GlobalizationTensor.fullTest K (r + 1) S F a) ⊆
      tsupport (fun g : AdelicGroupPoints K GLₙ =>
        adelicTestTensor K (r + 1) a (GlobalizationTensor.finiteTest K (r + 1) S F₀) (E g)) := by
    intro y hy
    apply subset_tsupport
    change adelicTestTensor K (r + 1) a (GlobalizationTensor.finiteTest K (r + 1) S F₀) (E y) ≠ 0
    have hy' : adelicTestTensor K (r + 1) a (GlobalizationTensor.finiteTest K (r + 1) S F)
        (E y) ≠ 0 := hy
    rw [GlobalizationTensor.adelicTestTensor_finiteTest] at hy' ⊢
    obtain ⟨hk, hrest⟩ := mul_ne_zero_iff.mp hy'
    obtain ⟨hprod, haway⟩ := mul_ne_zero_iff.mp hrest
    refine mul_ne_zero hk (mul_ne_zero ?_ haway)
    rw [Finset.prod_ne_zero_iff] at hprod ⊢
    rintro ⟨w, hwS⟩ -
    have hw := hprod ⟨w, hwS⟩ (Finset.mem_univ _)
    by_cases hw3 : w = v₃
    · subst hw3
      rw [hFv₃] at hw
      have hmem := (characteristic_ne_zero_iff hUicl hUic _).mp hw
      change F₀ w _ ≠ 0
      rw [hF₀v₃]
      exact (characteristic_ne_zero_iff (hBcl w) (hBc w) _).mpr (hUiB hmem)
    · change F w _ ≠ 0 at hw
      rw [hFne w hw3] at hw
      exact hw
  -- the positive average
  let fOne := normOnePositiveAverage K GLₙ T i ρA (GlobalizationTensor.fullTest K (r + 1) S F a)
  obtain ⟨hvalue, -⟩ := hCavg ρA (GlobalizationTensor.fullTest K (r + 1) S F a) hsuppΩ
  have hsuppC : Function.support fOne ⊆ C := fun z hz => (hvalue z hz).1
  have hlocU : ∀ z, fOne z ≠ 0 → FiniteAdelicGL.localProjection K (r + 1) v₃
      (AdelicGL.finite K (r + 1) (E z)) ∈ Ui := by
    intro z hz
    obtain ⟨-, y, hy, hyz⟩ := hvalue z hz
    rw [hcoordE y z hyz v₃]
    have h1 := hfac F (E y) hy v₃ h3S
    rw [hFv₃] at h1
    exact (characteristic_ne_zero_iff hUicl hUic _).mp h1
  have hIso := hiso fOne hsuppC hlocU
  -- the single-orbit trace formula
  have hell : ∀ g ∈ tsupport (adelicTestTensor K (r + 1) a (GlobalizationTensor.finiteTest K (r + 1) S F)),
      IsRegularElliptic (FiniteAdelicGL.localProjection K (r + 1) v₃ (AdelicGL.finite K (r + 1) g)) := by
    intro g hg
    have h1 := GlobalizationTensor.finiteComponent_mem_tsupport K (r + 1) S F a v₃ h3S g hg
    rw [hFv₃] at h1
    exact hBRE v₃ rfl (hUiB (tsupport_characteristic_subset hUicl hUic h1))
  have hcuspF : BaseChange.HasVanishingConstantTerms (F v₁ : FiniteLocalGL K (r + 1) v₁ → ℂ) := by
    rw [hFT₀ v₁ h1T]
    exact hcusp
  have hREr₀ : IsRegularElliptic (FiniteAdelicGL.localProjection K (r + 1) v₃
      (AdelicGL.finite K (r + 1) (E ((r₀ : H) : AdelicGroupPoints K GLₙ)))) := by
    rw [hcomp v₃]
    exact hRE₃
  have hcommr₀ := generalLinearRegularCentralizerCommutative K (r + 1) v₃ r₀ hREr₀
  obtain ⟨d₀⟩ := nonempty_twistedGeometricMeasures_of_commutative (Γ := RG)
    (θ := MonoidHom.id H) (δ := (r₀ : H)) (μG := (Measure.haar : Measure H))
    (isDiscrete_rationalNormOneSubgroup K GLₙ) continuous_id hcommr₀
  obtain ⟨h, hTC, hfin, htr⟩ := generalLinearTensorSingleOrbitTrace K (r + 1) hPD hG T i hi I e
    hc (generalLinearTensorCuspidalHilbertSchmidt_of_pos K (r + 1) (Nat.succ_pos r) hPD hG T i hi I
      e hc) a (GlobalizationTensor.finiteTest K (r + 1) S F) v₁
    (fun p q hpq hp hq => GlobalizationTensor.finiteTest_twoBlock_vanishing K (r + 1) S F v₁ h1S
      hcuspF p q hpq hp hq) v₃ hell r₀ d₀ hIso
  -- local data at the three places
  let instM (v : Langlands.Global.FinitePlace K) : MeasurableSpace (PlaceGroupPoints K GLₙ (.inr v)) :=
    borel _
  have instB (v : Langlands.Global.FinitePlace K) : BorelSpace (PlaceGroupPoints K GLₙ (.inr v)) :=
    ⟨rfl⟩
  have := d₀.rightInvariant
  have := d₀.finiteOnCompacts
  have := d₀.openPos
  have hlocv (v : Langlands.Global.FinitePlace K) (hv : v ∈ T₀) :
      LocalOrbitalNonvanishingAt K GLₙ v (normOneFinitePlaceProjection K GLₙ v (r₀ : H))
        (fun y => F v (localMatrixHomeomorph K (r + 1) v y)) := by
    have hm : localMatrixHomeomorph K (r + 1) v (normOneFinitePlaceProjection K GLₙ v (r₀ : H)) ∈
        Uloc v hv := by
      rw [hproj v]
      exact hmemU v hv
    have key := localOrbitalNonvanishingAt_of_matrix K (r + 1) v (F v)
      (normOneFinitePlaceProjection K GLₙ v (r₀ : H))
      (by rw [hproj v]; exact isRegularSemisimple_map x₀ hRS)
      (by rw [hFT₀ v hv]; exact hUorb v hv _ hm)
    exact key
  -- the all-bump test
  let F' : ∀ v : Langlands.Global.FinitePlace K, SchwartzBruhat (FiniteLocalGL K (r + 1) v) :=
    fun v => if v ∈ T₀ then bump v else F v
  have hF'T₀ (v : Langlands.Global.FinitePlace K) (hv : v ∈ T₀) : F' v = bump v := by
    simp only [F', hv, ↓reduceIte]
  have hF'n (v : Langlands.Global.FinitePlace K) (hv : v ∉ T₀) : F' v = F v := by
    simp only [F', hv, ↓reduceIte]
  have hext : GlobalizationTensor.fullTestExterior K (r + 1) S F' a v₀ v₁ v₂ =
      GlobalizationTensor.fullTestExterior K (r + 1) S F a v₀ v₁ v₂ := by
    funext x
    dsimp only [GlobalizationTensor.fullTestExterior]
    congr 2
    apply Finset.prod_congr rfl
    intro v hv
    have hv' : v ∉ T₀ := by
      simp only [Finset.mem_erase] at hv
      rw [hT₀]
      tauto
    rw [hF'n v hv']
  have hallbump : threePlaceTensor K GLₙ v₀ v₁ v₂
      (fun y => bump v₀ (localMatrixHomeomorph K (r + 1) v₀ y))
      (fun y => bump v₁ (localMatrixHomeomorph K (r + 1) v₁ y))
      (fun y => bump v₂ (localMatrixHomeomorph K (r + 1) v₂ y))
      (GlobalizationTensor.fullTestExterior K (r + 1) S F a v₀ v₁ v₂) =
        GlobalizationTensor.fullTest K (r + 1) S F' a := by
    rw [GlobalizationTensor.fullTest_eq_threePlaceTensor K (r + 1) S F' a v₀ v₁ v₂ h0S h1S h2S
      h01 h02 h12, hext, hF'T₀ v₀ h0T, hF'T₀ v₁ h1T, hF'T₀ v₂ h2T]
  have hF'nn (v : Langlands.Global.FinitePlace K) (x : FiniteLocalGL K (r + 1) v) :
      IsNonnegReal (F' v x) := by
    by_cases hv : v ∈ T₀
    · rw [hF'T₀ v hv]
      exact isNonnegReal_characteristic _ _ _
    · rw [hF'n v hv]
      by_cases hv3 : v = v₃
      · subst hv3
        rw [hFv₃]
        exact isNonnegReal_characteristic _ _ _
      · rw [hFne v hv3]
        change IsNonnegReal ((if v ∈ T₀ then Φ v else bump v) x)
        simp only [hv, ↓reduceIte]
        exact isNonnegReal_characteristic _ _ _
  have hawaynn (z : FiniteAdelicGL.AwayRestrictedProduct K (r + 1) (· ∈ S)) :
      IsNonnegReal (GlobalizationTensor.awayCharacteristic K (r + 1) S z) := by
    change IsNonnegReal (Set.indicator (↑(FiniteAdelicGL.awayIntegral K (r + 1) (· ∈ S)))
      (fun _ => (1 : ℂ)) z)
    exact isNonnegReal_indicator _ _
  have hfullnn (x : AdelicGroupPoints K GLₙ) :
      IsNonnegReal (GlobalizationTensor.fullTest K (r + 1) S F' a x) := by
    unfold GlobalizationTensor.fullTest
    rw [GlobalizationTensor.adelicTestTensor_finiteTest]
    exact (ha_nn _).mul ((isNonnegReal_prod _ _ fun v _ => hF'nn v.val _).mul (hawaynn _))
  have hF'one (v : Langlands.Global.FinitePlace K) :
      F' v (GlobalizationTensor.finiteComponent K (r + 1) v (AdelicGL.rational K (r + 1) x₀)) = 1 := by
    change F' v (FiniteAdelicGL.localProjection K (r + 1) v
      (AdelicGL.finite K (r + 1) (AdelicGL.rational K (r + 1) x₀))) = 1
    rw [localProjection_finite_rational]
    by_cases hv : v ∈ T₀
    · rw [hF'T₀ v hv]
      exact characteristic_eq_one _ _ (hBx v)
    · rw [hF'n v hv]
      by_cases hv3 : v = v₃
      · subst hv3
        rw [hFv₃]
        exact characteristic_eq_one _ _ hxUi
      · rw [hFne v hv3]
        change (if v ∈ T₀ then Φ v else bump v) (gmap v x₀) = 1
        simp only [hv, ↓reduceIte]
        exact characteristic_eq_one _ _ (hBx v)
  have haway : GlobalizationTensor.awayComponent K (r + 1) S (AdelicGL.rational K (r + 1) x₀) ∈
      FiniteAdelicGL.awayIntegral K (r + 1) (· ∈ S) := by
    rw [FiniteAdelicGL.mem_awayIntegral]
    intro v
    rw [GlobalizationTensor.awayComponent_apply]
    change FiniteAdelicGL.localProjection K (r + 1) v.val
      (AdelicGL.finite K (r + 1) (AdelicGL.rational K (r + 1) x₀)) ∈ _
    rw [localProjection_finite_rational]
    exact hint v.val v.property
  have hval : GlobalizationTensor.fullTest K (r + 1) S F' a ((r₀ : H) : AdelicGroupPoints K GLₙ) =
      ArchimedeanGL.kernelToContinuousMap K (r + 1) a
        (AdelicGL.infinite K (r + 1) (AdelicGL.rational K (r + 1) x₀)) := by
    unfold GlobalizationTensor.fullTest
    rw [hEr₀, GlobalizationTensor.adelicTestTensor_finiteTest,
      Finset.prod_eq_one (fun v _ => hF'one v.val),
      GlobalizationTensor.awayCharacteristic_of_mem K (r + 1) S haway, mul_one, mul_one]
  have hF'cont : Continuous (adelicTestTensor K (r + 1) a (GlobalizationTensor.finiteTest K (r + 1) S F')) :=
    CompactSmoothAdelicGLTest.continuous K (r + 1) (CompactSmoothAdelicGLTest.tensor K (r + 1) a _)
  have hF'cpt : HasCompactSupport
      (adelicTestTensor K (r + 1) a (GlobalizationTensor.finiteTest K (r + 1) S F')) :=
    CompactSmoothAdelicGLTest.hasCompactSupport K (r + 1) (CompactSmoothAdelicGLTest.tensor K (r + 1) a _)
  let fC' : C_c(AdelicGroupPoints K GLₙ, ℂ) :=
    ⟨⟨GlobalizationTensor.fullTest K (r + 1) S F' a, hF'cont.comp E.continuous⟩,
      hF'cpt.comp_homeomorph E.toHomeomorph⟩
  have hδpos : 0 < (fC' ((r₀ : H) : AdelicGroupPoints K GLₙ)).re := by
    change 0 < (GlobalizationTensor.fullTest K (r + 1) S F' a ((r₀ : H) : AdelicGroupPoints K GLₙ)).re
    rw [hval]
    exact ha_pos
  have hint₀ := (generalLinearEllipticCentralizer K (r + 1) v₃ r₀ hREr₀ d₀.centralizer d₀.orbital
    d₀.rational d₀.orbital_compatible d₀.rational_compatible).2
  have hpos : ∀ (μC : Measure (twistedCentralizer (MonoidHom.id H) (r₀ : H)))
      [μC.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μC] [μC.IsOpenPosMeasure]
      (ν : Measure (LeftQuotient (twistedCentralizer (MonoidHom.id H) (r₀ : H)))),
      IsCompatible _ (Measure.haar : Measure H) μC ν →
      twistedOrbitalIntegral (MonoidHom.id H) (r₀ : H) ν
        (normOnePositiveAverage K GLₙ T i ρA (threePlaceTensor K GLₙ v₀ v₁ v₂
          (fun y => bump v₀ (localMatrixHomeomorph K (r + 1) v₀ y))
          (fun y => bump v₁ (localMatrixHomeomorph K (r + 1) v₁ y))
          (fun y => bump v₂ (localMatrixHomeomorph K (r + 1) v₂ y))
          (GlobalizationTensor.fullTestExterior K (r + 1) S F a v₀ v₁ v₂))) ≠ 0 := by
    intro μC _ _ _ ν hν
    rw [hallbump]
    refine (twistedOrbitalIntegral_ne_zero_iff_of_isCompatible (MonoidHom.id H) continuous_id
      (r₀ : H) Measure.haar d₀.orbital_compatible hν _).mp ?_
    exact normOnePositiveAverage_orbitalIntegral_ne_zero K GLₙ T i hi I e hc fC'
      (fun g => (hfullnn g).1) (r₀ : H) hδpos d₀.centralizer d₀.orbital d₀.orbital_compatible hint₀
  -- nonvanishing of the orbital integral
  have hO : twistedOrbitalIntegral (MonoidHom.id H) (r₀ : H) d₀.orbital fOne ≠ 0 := by
    change twistedOrbitalIntegral (MonoidHom.id H) (r₀ : H) d₀.orbital
      (normOnePositiveAverage K GLₙ T i ρA (GlobalizationTensor.fullTest K (r + 1) S F a)) ≠ 0
    rw [GlobalizationTensor.fullTest_eq_threePlaceTensor K (r + 1) S F a v₀ v₁ v₂ h0S h1S h2S
      h01 h02 h12]
    exact threePlaceTensor_orbitalIntegral_ne_zero K GLₙ T i hi I e hc v₀ v₁ v₂ h01 h02 h12
      (r₀ : H) (MonoidHom.id H) rfl hcommr₀ _ _ _ _ _ _ _
      (fun z x => GlobalizationTensor.fullTestExterior_mul_finitePlacePointInclusion K (r + 1) S F a
        v₀ v₁ v₂ v₀ h0S (Or.inl rfl) z x)
      (fun z x => GlobalizationTensor.fullTestExterior_mul_finitePlacePointInclusion K (r + 1) S F a
        v₀ v₁ v₂ v₁ h1S (Or.inr (Or.inl rfl)) z x)
      (fun z x => GlobalizationTensor.fullTestExterior_mul_finitePlacePointInclusion K (r + 1) S F a
        v₀ v₁ v₂ v₂ h2S (Or.inr (Or.inr rfl)) z x)
      (hlocv v₀ h0T) (hlocv v₁ h1T) (hlocv v₂ h2T) hpos d₀.centralizer d₀.orbital
      d₀.orbital_compatible
  have hrat0 : d₀.rational Set.univ ≠ 0 :=
    Measure.measure_univ_ne_zero.mpr d₀.rational_compatible.nonzero
  have hratT : d₀.rational Set.univ ≠ ⊤ := hfin hO
  have htr_ne : operatorTrace (haarQuotientL2IntegratedAction K GLₙ T i hi I e hc Measure.haar _ h)
      ≠ 0 := by
    rw [htr]
    unfold TwistedGeometricMeasures.term
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨hrat0, hratT⟩)) hO
  -- cuspidality of the image
  have hfcont : Continuous (adelicTestTensor K (r + 1) a (GlobalizationTensor.finiteTest K (r + 1) S F)) :=
    CompactSmoothAdelicGLTest.continuous K (r + 1) (CompactSmoothAdelicGLTest.tensor K (r + 1) a _)
  have hfcpt : HasCompactSupport
      (adelicTestTensor K (r + 1) a (GlobalizationTensor.finiteTest K (r + 1) S F)) :=
    CompactSmoothAdelicGLTest.hasCompactSupport K (r + 1) (CompactSmoothAdelicGLTest.tensor K (r + 1) a _)
  let fC : C_c(AdelicGroupPoints K GLₙ, ℂ) :=
    ⟨⟨GlobalizationTensor.fullTest K (r + 1) S F a, hfcont.comp E.continuous⟩,
      hfcpt.comp_homeomorph E.toHomeomorph⟩
  have hrad := generalLinearRadicalIntegralVanishing K (r + 1) hPD hG v₁
    (adelicTestTensor K (r + 1) a (GlobalizationTensor.finiteTest K (r + 1) S F)) hfcont hfcpt
    (fun p q hpq hp hq => GlobalizationTensor.adelicTestTensor_finiteTest_twoBlock_vanishing K (r + 1)
      S F a v₁ h1S hcuspF p q hpq hp hq)
  have hcuspImg : ∀ φ, haarQuotientL2IntegratedAction K GLₙ T i hi I e hc Measure.haar _ h φ ∈
      fullAEL2CuspidalSubmodule K GLₙ hPD hG T i hi I e hc :=
    fun φ => groupSchemeCuspidalImage K GLₙ hPD hG T i hi I e hc fC h hrad φ
  exact ⟨S, F, a, h0S, h1S, h2S, hFT₀ v₀ h0T, hFT₀ v₁ h1T, hFT₀ v₂ h2T, h, hTC, hcuspImg, htr_ne⟩

end Global

end Langlands.TraceFormula
