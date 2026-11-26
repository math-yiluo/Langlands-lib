import Langlands.BaseChange.CommonShintaniLiftNonvanishing
import Langlands.HarmonicAnalysis.Distribution.TopologicalSupport

/-! # Proportional traces on regular norms in a common Shintani fibre -/

noncomputable section

universe uF uE uV uV' uW

set_option autoImplicit false

namespace Langlands.BaseChange

open HarmonicAnalysis JacquetLanglands MeasureTheory

theorem distribution_eq_zero_of_localValues_zero
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [T2Space X]
    [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
    {μ : Measure X} {D : Distribution X} {f : SchwartzBruhat X}
    (h : ∀ x, f x ≠ 0 → HasLocalValue μ D x 0) : D f = 0 := by
  apply Distribution.mem_supportedOn_support D f
  intro x hx
  by_contra hfx
  obtain ⟨U, hU, hxU, hval⟩ := h x hfx
  have hzero : Distribution.restrictOpen hU D = 0 := by
    apply LinearMap.ext
    intro g
    change D (SchwartzBruhat.extendZero hU g) = 0
    have hsupp : Function.support (SchwartzBruhat.extendZero hU g : X → ℂ) ⊆ U :=
      subset_closure.trans (SchwartzBruhat.tsupport_extendZero_subset hU g)
    rw [hval _ hsupp, zero_mul]
  exact ((Distribution.not_mem_support_iff D x).mpr ⟨U, hU, hxU, hzero⟩) hx

/-- The ordinary traces of two actions sharing an irreducible Shintani lift
are proportional on all tests supported on associated regular norms. -/
def CommonShintaniLiftTraceOnNormsStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    (E : Type uE) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    (σ : E ≃ₐ[F] E) (l n : ℕ)
    [T2Space (GeneralLinear n F)] [LocallyCompactSpace (GeneralLinear n F)]
    [TotallyDisconnectedSpace (GeneralLinear n F)]
    [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
    [TotallyDisconnectedSpace (GeneralLinear n E)]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (V' : Type uV') [AddCommGroup V'] [Module ℂ V']
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π)
    (π' : Representation ℂ (GeneralLinear n F) V') (hπ' : IsAdmissible π')
    (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ),
    τ.IsIrreducible →
    ∀ (A A' : SigmaIntertwiner σ n τ) (c c' : ℂ),
      IsShintaniLift σ l π hπ τ hτ A c → IsShintaniLift σ l π' hπ' τ hτ A' c' →
      ∃ a : ℂ, a ≠ 0 ∧
        let := borel (GeneralLinear n F)
        have : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
        ∀ (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure]
          (f : SchwartzBruhat (GeneralLinear n F)),
          (∀ g, f g ≠ 0 → IsRegularSemisimple g ∧ IsNorm σ l g) →
          Character.distribution μ π' hπ' f = a * Character.distribution μ π hπ f

/-- Schur comparison fixes a single ratio for all regular norm values.
Distribution support extends the local equality to every supported test. -/
theorem commonShintaniLiftTraceOnNorms :
    CommonShintaniLiftTraceOnNormsStatement.{uF, uE, uV, uV', uW} := by
  intro F _ _ _ E _ _ _ _ σ l n _ _ _ _ _ _ V _ _ V' _ _ W _ _
    π hπ π' hπ' τ hτ hI A A' c c' hLift hLift'
  obtain ⟨s, hs, hA⟩ := A.exists_smul_toLinearMap A' hτ hI
  let a := s * c / c'
  have ha : a ≠ 0 := div_ne_zero (mul_ne_zero hs hLift.1) hLift'.1
  have hac : c' * a = s * c := by
    change c' * (s * c / c') = s * c
    rw [mul_comm c', div_mul_cancel₀ _ hLift'.1]
  refine ⟨a, ha, ?_⟩
  let := borel (GeneralLinear n F)
  have : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  dsimp only
  intro μ _ f hf
  let D := Character.distribution μ π' hπ' - a • Character.distribution μ π hπ
  have hD : D f = 0 := by
    apply distribution_eq_zero_of_localValues_zero (μ := μ)
    intro γ hγ
    obtain ⟨hreg, δ, hassoc⟩ := hf γ hγ
    obtain ⟨b, hb, hT⟩ := hLift.2 δ γ hassoc hreg
    obtain ⟨b', hb', hT'⟩ := hLift'.2 δ γ hassoc hreg
    have hScaled := hT.smul s
    rw [← hA] at hScaled
    have heq : b' = a * b := mul_left_cancel₀ hLift'.1 (calc
      c' * b' = s * (c * b) := (hScaled.unique hT').symm
      _ = c' * (a * b) := by rw [← mul_assoc s, ← mul_assoc c', hac])
    obtain ⟨U, hU, hγU, hval⟩ := hb μ
    obtain ⟨U', hU', hγU', hval'⟩ := hb' μ
    refine ⟨U ∩ U', hU.inter hU', ⟨hγU, hγU'⟩, ?_⟩
    intro g hg
    change Character.distribution μ π' hπ' g - a * Character.distribution μ π hπ g =
      0 * ∫ x, g x ∂μ
    rw [hval g (hg.trans Set.inter_subset_left), hval' g (hg.trans Set.inter_subset_right),
      heq, mul_assoc, sub_self, zero_mul]
  exact sub_eq_zero.mp hD

end Langlands.BaseChange
