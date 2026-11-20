import Langlands.Global.RankinSelberg.EqualInfiniteWhittakerReduction
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Equal-rank test integrals at individual infinite places -/

noncomputable section
open NumberField Filter
open scoped Classical CategoryTheory.MonObj Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Automorphic Langlands.LocalFactor.Archimedean
open Langlands.Global.HeckeFunctionalEquation
open ArchimedeanLocal

attribute [local instance] archimedeanRealQMeasurable archimedeanRealQBorel
  archimedeanComplexQMeasurable archimedeanComplexQBorel
  archimedeanRealGLMeasurable archimedeanRealGLBorel archimedeanComplexGLMeasurable
  archimedeanComplexGLBorel archimedeanRealNMeasurable archimedeanRealNBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel

/-- The same right half-plane supports holomorphy and one nonzero value. -/
def HolomorphicNonzeroOnRightHalfPlane (f : ℂ → ℂ) : Prop :=
  ∃ σ : ℝ, DifferentiableOn ℂ f {s : ℂ | σ < s.re} ∧ ∃ z : ℂ, σ < z.re ∧ f z ≠ 0

namespace HolomorphicNonzeroOnRightHalfPlane

private theorem isOpen_rightHalfPlane (a : ℝ) : IsOpen {s : ℂ | a < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- The holomorphic function has a nonzero value on any right half-plane. -/
theorem exists_ne_zero_above {f : ℂ → ℂ} (hf : HolomorphicNonzeroOnRightHalfPlane f)
    (a : ℝ) : ∃ s : ℂ, a < s.re ∧ f s ≠ 0 := by
  obtain ⟨σ, hd, z, hz, hne⟩ := hf
  by_contra! hzero
  let w : ℂ := ((max a σ + 1 : ℝ) : ℂ)
  have hw (b : ℝ) (hb : b ≤ max a σ) : b < w.re := by
    simp only [w, Complex.ofReal_re]
    linarith
  have hevent : f =ᶠ[𝓝 w] 0 := by
    have ha : ∀ᶠ s : ℂ in 𝓝 w, a < s.re :=
      (isOpen_rightHalfPlane a).mem_nhds (hw a (le_max_left _ _))
    exact ha.mono fun s hs => hzero s hs
  have han := hd.analyticOnNhd (isOpen_rightHalfPlane σ)
  exact hne (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_re_gt σ).isPreconnected (hw σ (le_max_right _ _)) hevent hz)

private theorem one : HolomorphicNonzeroOnRightHalfPlane (fun _ => 1) := by
  exact ⟨0, differentiableOn_const _, 1, by simp, one_ne_zero⟩

private theorem mul {f g : ℂ → ℂ} (hf : HolomorphicNonzeroOnRightHalfPlane f)
    (hg : HolomorphicNonzeroOnRightHalfPlane g) : HolomorphicNonzeroOnRightHalfPlane (f * g) := by
  have hfn := hf.exists_ne_zero_above
  obtain ⟨σ, hd, _⟩ := hf
  obtain ⟨τ, he, z, hz, hz'⟩ := hg
  let a := max σ τ
  have hσ : {s : ℂ | a < s.re} ⊆ {s : ℂ | σ < s.re} := by
    intro s (hs : a < s.re)
    exact (le_max_left σ τ).trans_lt hs
  have hτ : {s : ℂ | a < s.re} ⊆ {s : ℂ | τ < s.re} := by
    intro s (hs : a < s.re)
    exact (le_max_right σ τ).trans_lt hs
  refine ⟨a, (hd.mono hσ).mul (he.mono hτ), ?_⟩
  obtain ⟨w, hw, hne⟩ := hfn a
  by_contra! hzero
  have hnhds := (isOpen_rightHalfPlane a).mem_nhds hw
  have hfcont := hd.continuousOn.continuousAt ((isOpen_rightHalfPlane σ).mem_nhds (hσ hw))
  have hfne := hfcont.eventually_ne hne
  have hgz : g =ᶠ[𝓝 w] 0 := by
    filter_upwards [hnhds, hfne] with s hs hfs
    have hmul : f s * g s = 0 := hzero s hs
    exact (mul_eq_zero.mp hmul).resolve_left hfs
  have han := he.analyticOnNhd (isOpen_rightHalfPlane τ)
  exact hz' (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_re_gt τ).isPreconnected (hτ hw) hgz hz)

private theorem finsetProd {I : Type*} (s : Finset I) (f : I → ℂ → ℂ)
    (hf : ∀ i, HolomorphicNonzeroOnRightHalfPlane (f i)) :
    HolomorphicNonzeroOnRightHalfPlane (fun z => ∏ i ∈ s, f i z) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using one
  | @insert i s hi ih =>
    rw [show (fun z => ∏ j ∈ insert i s, f j z) = f i * (fun z => ∏ j ∈ s, f j z) from
      funext fun z => Finset.prod_insert hi]
    exact (hf i).mul ih

end HolomorphicNonzeroOnRightHalfPlane

/-- The real local input chooses actual restrictions with test integrals holomorphic and
nonzero at one point on their respective right half-planes. -/
def RealEqualPlaceTestsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T Td T' Td' : CuspidalOperatorRealization F r),
    OperatorRealization.IsContragredientOf Td.realization T.realization →
    OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (v : {v : InfinitePlace F // v.IsReal}) (a : ℝˣ),
    IsRealAdditiveComponent ψ v.1 v.2 a →
  ∀ (d d' dd dd' : List RealBlock),
    T.realization.HasRealPlaceParameter v d →
    T'.realization.HasRealPlaceParameter v d' →
    Td.realization.HasRealPlaceParameter v dd →
    Td'.realization.HasRealPlaceParameter v dd' →
    ∃ (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
      (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ) (D : RealQuotientMeasureData r),
      IsRealPlaceWhittaker F T ψ.complex v W ∧ IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' ∧
      HolomorphicNonzeroOnRightHalfPlane (realEqualIntegral D W W' Φ) ∧
      HolomorphicNonzeroOnRightHalfPlane (realEqualDualIntegral a D W W' Φ)

/-- The corresponding local input at a complex place. -/
def ComplexEqualPlaceTestsStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T Td T' Td' : CuspidalOperatorRealization F r),
    OperatorRealization.IsContragredientOf Td.realization T.realization →
    OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (w : {w : InfinitePlace F // w.IsComplex}) (a : ℂˣ),
    IsComplexAdditiveComponent ψ w.1 w.2 a →
  ∀ (d d' dd dd' : List ComplexCharacterData),
    T.realization.HasComplexPlaceParameter w d →
    T'.realization.HasComplexPlaceParameter w d' →
    Td.realization.HasComplexPlaceParameter w dd →
    Td'.realization.HasComplexPlaceParameter w dd' →
    ∃ (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
      (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ) (D : ComplexQuotientMeasureData r),
      IsComplexPlaceWhittaker F T ψ.complex w W ∧ IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' ∧
      HolomorphicNonzeroOnRightHalfPlane (complexEqualIntegral D W W' Φ) ∧
      HolomorphicNonzeroOnRightHalfPlane (complexEqualDualIntegral a D W W' Φ)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T T' : CuspidalOperatorRealization F r}
  {ψ : Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
  {aR : {v : InfinitePlace F // v.IsReal} → ℝˣ}
  {aC : {w : InfinitePlace F // w.IsComplex} → ℂˣ}

/-- Independently supplied test data at each infinite place give both nonvanishing
products of archimedean integrals. The scalar here is a placeholder of value one. -/
theorem infiniteTestData_of_local
    (hR : ∀ v : {v : InfinitePlace F // v.IsReal},
      ∃ (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
        (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ) (D : RealQuotientMeasureData r),
        IsRealPlaceWhittaker F T ψ.complex v W ∧ IsRealPlaceWhittaker F T' ψ.complex⁻¹ v W' ∧
        HolomorphicNonzeroOnRightHalfPlane (realEqualIntegral D W W' Φ) ∧
        HolomorphicNonzeroOnRightHalfPlane (realEqualDualIntegral (aR v) D W W' Φ))
    (hC : ∀ w : {w : InfinitePlace F // w.IsComplex},
      ∃ (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
        (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ) (D : ComplexQuotientMeasureData r),
        IsComplexPlaceWhittaker F T ψ.complex w W ∧ IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w W' ∧
        HolomorphicNonzeroOnRightHalfPlane (complexEqualIntegral D W W' Φ) ∧
        HolomorphicNonzeroOnRightHalfPlane (complexEqualDualIntegral (aC w) D W W' Φ)) :
    Nonempty (EqualInfiniteTestData T T' ψ aR aC) := by
  choose WR WR' ΦR DR hWR hWR' hoR hdR using hR
  choose WC WC' ΦC DC hWC hWC' hoC hdC using hC
  refine ⟨⟨1, one_ne_zero, WR, WR', WC, WC', hWR, hWR', hWC, hWC', ΦR, ΦC, DR, DC, ?_, ?_⟩⟩
  · exact ((HolomorphicNonzeroOnRightHalfPlane.finsetProd Finset.univ _ hoR).mul
      (HolomorphicNonzeroOnRightHalfPlane.finsetProd Finset.univ _ hoC)).exists_ne_zero_above
  · exact ((HolomorphicNonzeroOnRightHalfPlane.finsetProd Finset.univ _ hdR).mul
      (HolomorphicNonzeroOnRightHalfPlane.finsetProd Finset.univ _ hdC)).exists_ne_zero_above

end Langlands.Global.RankinSelbergGlobal
