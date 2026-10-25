import Langlands.Representation.Whittaker.GeneralizedCoefficientSeparation
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Descent between full-transpose smoothing maps -/

noncomputable section

namespace Langlands.Whittaker

open HarmonicAnalysis MeasureTheory MeasureTheory.Measure

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsMulRightInvariant μ]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable (ℓ₁ ℓ₂ : Module.Dual ℂ V)
variable (hsurj : Function.Surjective (smoothFunctional μ ρ hρ ℓ₁))
variable (hker : LinearMap.ker (smoothFunctional μ ρ hρ ℓ₁) ≤
  LinearMap.ker (smoothFunctional μ ρ hρ ℓ₂))

/-- The linear map obtained by descending the second smoothing map through the
first, using kernel inclusion and surjectivity. -/
def smoothFunctionalDescentLinear : Module.End ℂ (SmoothDual ρ) :=
  ((LinearMap.ker (smoothFunctional μ ρ hρ ℓ₁)).liftQ
      (smoothFunctional μ ρ hρ ℓ₂) hker).comp
    ((smoothFunctional μ ρ hρ ℓ₁).quotKerEquivOfSurjective hsurj).symm.toLinearMap

@[simp]
theorem smoothFunctionalDescentLinear_apply (f : SchwartzBruhat G) :
    smoothFunctionalDescentLinear μ ρ hρ ℓ₁ ℓ₂ hsurj hker
      (smoothFunctional μ ρ hρ ℓ₁ f) = smoothFunctional μ ρ hρ ℓ₂ f := by
  simp only [smoothFunctionalDescentLinear, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.liftQ_apply]

/-- Right-translation covariance makes smoothing descent an endomorphism of the
actual smooth contragredient representation. -/
def smoothFunctionalDescent :
    (smoothContragredient ρ).IntertwiningMap (smoothContragredient ρ) where
  toLinearMap := smoothFunctionalDescentLinear μ ρ hρ ℓ₁ ℓ₂ hsurj hker
  isIntertwining' a := by
    apply LinearMap.ext
    intro φ
    obtain ⟨f, rfl⟩ := hsurj φ
    change smoothFunctionalDescentLinear μ ρ hρ ℓ₁ ℓ₂ hsurj hker
      (smoothContragredient ρ a (smoothFunctional μ ρ hρ ℓ₁ f)) =
      smoothContragredient ρ a
        (smoothFunctionalDescentLinear μ ρ hρ ℓ₁ ℓ₂ hsurj hker
          (smoothFunctional μ ρ hρ ℓ₁ f))
    rw [← smoothFunctional_rightTranslate, smoothFunctionalDescentLinear_apply,
      smoothFunctionalDescentLinear_apply, smoothFunctional_rightTranslate]

@[simp]
theorem smoothFunctionalDescent_apply (f : SchwartzBruhat G) :
    smoothFunctionalDescent μ ρ hρ ℓ₁ ℓ₂ hsurj hker
      (smoothFunctional μ ρ hρ ℓ₁ f) = smoothFunctional μ ρ hρ ℓ₂ f :=
  smoothFunctionalDescentLinear_apply μ ρ hρ ℓ₁ ℓ₂ hsurj hker f

/-- The interpolation identity determines the descent uniquely. -/
theorem smoothFunctionalDescent_unique
    (A : (smoothContragredient ρ).IntertwiningMap (smoothContragredient ρ))
    (hA : ∀ f, A (smoothFunctional μ ρ hρ ℓ₁ f) =
      smoothFunctional μ ρ hρ ℓ₂ f) :
    A = smoothFunctionalDescent μ ρ hρ ℓ₁ ℓ₂ hsurj hker := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro φ
  obtain ⟨f, rfl⟩ := hsurj φ
  change A (smoothFunctional μ ρ hρ ℓ₁ f) =
    smoothFunctionalDescent μ ρ hρ ℓ₁ ℓ₂ hsurj hker (smoothFunctional μ ρ hρ ℓ₁ f)
  rw [hA, smoothFunctionalDescent_apply]

omit [MeasurableSpace G] [BorelSpace G] in
private theorem compactOpenCofinal :
    ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K := by
  intro K
  obtain ⟨L, hLK, hL, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ K
  exact ⟨L, hL, hLK⟩

variable [IsMulLeftInvariant μ] [IsOpenPosMeasure μ]

include hker in
/-- Kernel inclusion between smoothing maps forces scalar proportionality for
an admissible irreducible representation and a nonzero first functional. -/
theorem existsUnique_smul_of_smoothFunctional_ker_le
    (hAdm : IsAdmissible ρ) (hIrr : ρ.IsIrreducible) (hℓ₁ : ℓ₁ ≠ 0) :
    ∃! c : ℂ, ℓ₂ = c • ℓ₁ := by
  have hs := smoothFunctional_surjective μ ρ hρ hAdm hIrr ℓ₁ hℓ₁
  have ha := isAdmissible_smoothContragredient_of_compact_cofinal
    (compactOpenCofinal (G := G)) ρ hAdm
  have hi := CompactSplitting.isIrreducible_smoothContragredient
    (compactOpenCofinal (G := G)) ρ hAdm hIrr
  obtain ⟨c, hc, _⟩ := admissibleSchur_scalarEndomorphism
    (smoothContragredient ρ) ha hi
      (smoothFunctionalDescent μ ρ hρ ℓ₁ ℓ₂ hs hker)
  have heq : smoothFunctional μ ρ hρ ℓ₂ = c • smoothFunctional μ ρ hρ ℓ₁ := by
    apply LinearMap.ext
    intro f
    have hf := congrArg
      (fun A : (smoothContragredient ρ).IntertwiningMap (smoothContragredient ρ) =>
        A (smoothFunctional μ ρ hρ ℓ₁ f)) hc
    simpa only [smoothFunctionalDescent_apply, Representation.IntertwiningMap.smul_apply,
      Representation.IntertwiningMap.id_apply, LinearMap.smul_apply] using hf
  have hrel : ℓ₂ = c • ℓ₁ := by
    apply sub_eq_zero.mp
    apply (smoothFunctional_eq_zero_iff μ ρ hρ (ℓ₂ - c • ℓ₁)).1
    rw [map_sub, map_smul, heq, sub_self]
  refine ⟨c, hrel, ?_⟩
  intro d hd
  exact (smul_left_injective ℂ hℓ₁) (hd.symm.trans hrel)

end Langlands.Whittaker
