import Langlands.Analysis.Local.QuotientAutomorphismProof
import Langlands.Analysis.Local.QuotientTranslation

/-! # Continuity of Haar modulus in a family of automorphisms -/

noncomputable section

universe u v

open MeasureTheory MeasureTheory.Measure Set Topology
open scoped CompactlySupported NNReal

set_option autoImplicit false

namespace Langlands.Haar

open Langlands.QuotientIntegration

variable {X : Type u} [TopologicalSpace X]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (α : X → G ≃ₜ* G)

/-- Joint continuity of the automorphisms and their inverses implies
continuity of the real Haar modulus along the parameter space. -/
def AutomorphismHaarModulusContinuityStatement : Prop :=
  ∀ [LocallyCompactSpace X] [T2Space G] (ν : Measure G) [IsHaarMeasure ν] [ν.Regular],
    Continuous (fun p : X × G => α p.1 p.2) →
      Continuous (fun p : X × G => (α p.1).symm p.2) →
        Continuous (fun x : X => (mulEquivHaarChar (α x) : ℝ))

theorem automorphismHaarModulusContinuity :
    AutomorphismHaarModulusContinuityStatement α := by
  intro _ _ ν _ _ hα hInv
  obtain ⟨f, hf⟩ := exists_compact_integral_ne_zero ν (NeZero.ne ν)
  let I := fun x : X => ∫ y, f (α x y) ∂ν
  have hI : Continuous I := by
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨S, hSc, hS⟩ := exists_compact_mem_nhds x
    let T := (fun p : X × G => (α p.1).symm p.2) '' (S ×ˢ tsupport f)
    have hTc : IsCompact T := (hSc.prod f.hasCompactSupport).image hInv
    have hFc : ContinuousOn (fun p : X × G => f (α p.1 p.2)) (S ×ˢ univ) :=
      (f.continuous.comp hα).continuousOn
    have hzero (s : X) (g : G) (hs : s ∈ S) (hg : g ∉ T) : f (α s g) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hfg
      exact hg ⟨(s, α s g), ⟨hs, hfg⟩, (α s).symm_apply_apply g⟩
    exact (continuousOn_integral_of_compact_support (μ := ν) hTc hFc hzero).continuousAt hS
  have hscale (x : X) : (mulEquivHaarChar (α x) : ℝ) * I x = ∫ y, f y ∂ν :=
    mulEquivHaarChar_mul_integral_comp ν (α x) f
  have hIne (x : X) : I x ≠ 0 := by
    intro hx
    have h := hscale x
    rw [hx, mul_zero] at h
    exact hf h.symm
  have heq (x : X) : (mulEquivHaarChar (α x) : ℝ) = (∫ y, f y ∂ν) / I x :=
    (eq_div_iff (hIne x)).mpr (hscale x)
  exact (continuous_const.div hI hIne).congr fun x => (heq x).symm

end Langlands.Haar
