import Langlands.TraceFormula.RationalRegularOrbitCutoff
import Langlands.TraceFormula.SplitOrbitCutoff

/-! # Split matching test functions that isolate rational classes -/

noncomputable section

open MeasureTheory Topology
open scoped ComplexOrder

namespace Langlands.TraceFormula

open BaseChange HarmonicAnalysis JacquetLanglands

universe u v w

set_option hygiene false in
local notation "G" => GeneralLinear n F

set_option hygiene false in
local notation "E" => GeneralLinear n (Fin (m + 1) → F)

set_option hygiene false in
local notation "κ" => splitGLCoordinates F n (m + 1)

set_option hygiene false in
local notation "τ" => splitCyclicShift F (m + 1)

local instance {A : Type v} [CommRing A] [TopologicalSpace A] (n : ℕ) :
    MeasurableSpace (GeneralLinear n A) := borel _
local instance {A : Type v} [CommRing A] [TopologicalSpace A] (n : ℕ) :
    BorelSpace (GeneralLinear n A) := ⟨rfl⟩

/-- Match a split tensor with its convolution while retaining only a given
ordinary rational class and a given twisted rational class in the supplied
lists. The localizations are required to preserve norm association. -/
def SplitRationalOrbitIsolationStatement : Prop :=
  ∀ (K : Type u) [Field K] (L : Type w) [Field L] [Algebra K L]
    (F : Type v) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n m : ℕ) (σ : L ≃ₐ[K] L), IsCyclicAlgebra σ (m + 1) →
    ∀ (ι : K →+* F) (s : GeneralLinear n L →* E),
      (∀ δ γ, IsNormAssociated σ (m + 1) δ γ →
        IsNormAssociated τ (m + 1) (s δ) (Matrix.GeneralLinearGroup.map ι γ)) →
      ∀ (R : Finset (GeneralLinear n K)) (T : Finset (GeneralLinear n L))
        (δ : GeneralLinear n L) (γ : GeneralLinear n K),
        IsRegularSemisimple γ → IsNormAssociated σ (m + 1) δ γ →
        ∀ (μF : Measure G) [μF.IsHaarMeasure] (μE : Measure E) [μE.IsHaarMeasure],
          IsSplitProductHaar μF μE → ∀ (A : Set (Fin (m + 1) → G)) (V : Set G),
          IsOpen A → κ (s δ) ∈ A → IsOpen V → (List.ofFn (κ (s δ))).prod ∈ V →
          ∃ ψ : Fin (m + 1) → SchwartzBruhat G,
            let φ := splitTensor fun i ↦ (ψ i : G → ℂ)
            let f := convolutionProduct μF ψ
            AreConcordant τ (m + 1) μF μE φ (f : G → ℂ) ∧
            φ (s δ) = 1 ∧ tsupport φ ⊆ κ ⁻¹' A ∧ tsupport (f : G → ℂ) ⊆ V ∧
            (∀ g, 0 ≤ f g) ∧ 0 < f (List.ofFn (κ (s δ))).prod ∧
            (∀ q ∈ R, (∃ x : G, f (x⁻¹ * Matrix.GeneralLinearGroup.map ι q * x) ≠ 0) →
              ∃ a : GeneralLinear n K, a⁻¹ * q * a = γ) ∧
            (∀ t ∈ T, (∃ y : E, φ (y⁻¹ * s t * entrywiseAut τ n y) ≠ 0) →
              ∃ a : GeneralLinear n L, a⁻¹ * t * entrywiseAut σ n a = δ)

theorem splitRationalOrbitIsolation : SplitRationalOrbitIsolationStatement.{u, v, w} := by
  intro K _ L _ _ F _ _ _ _ n m σ hσ ι s hs R T δ γ hγ hδ μF _ μE _ hμ A V hA hδA hV hδV
  let := LocalFieldTopology.t2Space F
  let := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  let i := Matrix.GeneralLinearGroup.map (n := Fin n) ι
  choose a ha using (cyclicNormLemma K L σ (m + 1) n hσ).1
  obtain ⟨U, _, hU, hγU, _, hOrd, hTw⟩ :=
    rationalRegularOrbitCutoff K L F n σ (m + 1) hσ ι R T γ δ a hγ hδ
      (fun t _ ↦ ha t) Set.univ isOpen_univ (Set.mem_univ _)
  obtain ⟨b, hb⟩ := hs δ γ hδ
  let c := κ b 0
  have hβ : c⁻¹ * (List.ofFn (κ (s δ))).prod * c = i γ :=
    splitAssociatedNorm_coordinate (s δ) (i γ) b hb
  let p : (Fin (m + 1) → G) → G := fun x ↦ (List.ofFn x).prod
  let V' := V ∩ (fun x : G ↦ c⁻¹ * x * c) ⁻¹' U
  let A' := A ∩ p ⁻¹' V'
  have hV' : IsOpen V' := hV.inter (hU.isOpen.preimage
    ((continuous_const.mul continuous_id).mul continuous_const))
  have hA' : IsOpen A' :=
    hA.inter (hV'.preimage (@splitProductFiberChart G _ _ _ m).symm.continuous.fst)
  have hβV' : p (κ (s δ)) ∈ V' := by
    refine ⟨hδV, ?_⟩
    change c⁻¹ * p (κ (s δ)) * c ∈ U
    rwa [hβ]
  have hδA' : κ (s δ) ∈ A' := ⟨hδA, hβV'⟩
  obtain ⟨ψ, hmatch, hone, hφsupp, hfsupp, hfnonneg, hfpos⟩ :=
    splitOrbitCutoff F n m μF μE hμ (s δ) A' V' hA' hδA' hV' hβV'
  refine ⟨ψ, hmatch, hone, hφsupp.trans (Set.preimage_mono Set.inter_subset_left),
    hfsupp.trans Set.inter_subset_left, hfnonneg, hfpos, ?_, ?_⟩
  · rintro q hq ⟨x, hx⟩
    have hxV' := hfsupp (subset_tsupport _ hx)
    have hxU : c⁻¹ * (x⁻¹ * i q * x) * c ∈ U := hxV'.2
    apply hOrd q hq
    refine ⟨x * c, ?_⟩
    simpa only [i, mul_inv_rev, mul_assoc] using hxU
  · rintro t ht ⟨y, hy⟩
    let z := y⁻¹ * s t * entrywiseAut τ n y
    have hzV' : p (κ z) ∈ V' := (hφsupp (subset_tsupport _ hy)).2
    have hzt : IsNormAssociated τ (m + 1) z (i (a t)) := by
      have h := (hs t (a t) (ha t)).twistedConj
        (isCyclicAlgebra_splitCyclicShift F m).pow_eq_one y 1
      simpa only [z, inv_one, one_mul, mul_one] using h
    obtain ⟨b', hb'⟩ := hzt
    let d := κ b' 0
    have hd : d⁻¹ * p (κ z) * d = i (a t) :=
      splitAssociatedNorm_coordinate z (i (a t)) b' hb'
    apply hTw t ht
    refine ⟨d⁻¹ * c, ?_⟩
    have hcalc : (d⁻¹ * c)⁻¹ * i (a t) * (d⁻¹ * c) = c⁻¹ * p (κ z) * c := by
      rw [← hd]
      group
    rw [← show i (a t) = Matrix.GeneralLinearGroup.map ι (a t) from rfl, hcalc]
    exact hzV'.2

end Langlands.TraceFormula
