import Langlands.Representation.Archimedean.JacquetNonvanishing

/-!
# The largest proper submodule of a strictly dominant principal series
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace StrictPrincipalSeriesQuotient

open PartialJacquet JacquetDual JacquetKernel JacquetNonvanishing Langlands.GeneralLinear

variable {n : ℕ} {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}

/-- `W` is a `(𝔤, K)`-stable subspace of the `O(n)`-finite principal series of `χ`. -/
def IsGKStable (n : ℕ) (χ : ℕ → ℝˣ → ℂ) (W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)) :
    Prop :=
  W ≤ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) ∧
    (∀ k ∈ unitaryCompact ℝ n, ∀ w ∈ W,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k w ∈ W) ∧
    ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ w ∈ W, rightDerivative (matrixModel ℝ n) X w ∈ W

/-- `W` is a proper `(𝔤, K)`-stable subspace. -/
def IsProperGKStable (n : ℕ) (χ : ℕ → ℝˣ → ℂ)
    (W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)) : Prop :=
  IsGKStable n χ W ∧ ∃ f ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n), f ∉ W

/-- The sum of all proper `(𝔤, K)`-stable subspaces. -/
def largestProper (n : ℕ) (χ : ℕ → ℝˣ → ℂ) : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) :=
  ⨆ W : {W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) // IsProperGKStable n χ W},
    (W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))

theorem le_largestProper {W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)}
    (hW : IsProperGKStable n χ W) : W ≤ largestProper n χ :=
  le_iSup (fun W : {W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) //
    IsProperGKStable n χ W} => (W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))) ⟨W, hW⟩

theorem largestProper_le :
    largestProper n χ ≤ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) :=
  iSup_le fun W => W.2.1.1

theorem rightDerivative_zero (X : Matrix (Fin n) (Fin n) ℝ) :
    rightDerivative (matrixModel ℝ n) X (0 : Langlands.GeneralLinear n ℝ → ℂ) = 0 := by
  have h := rightDerivative_smul (contMDiff_const (c := (0 : ℂ))) 0 X
  rw [zero_smul, zero_smul] at h
  exact h

theorem isGKStable_largestProper : IsGKStable n χ (largestProper n χ) := by
  refine ⟨largestProper_le, fun k hk w hw => ?_, fun X w hw => ?_⟩
  · refine Submodule.iSup_induction (fun W : {W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) //
      IsProperGKStable n χ W} => (W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)))
      (motive := fun w => Whittaker.rightTranslation ℂ
        (Langlands.GeneralLinear n ℝ) k w ∈ largestProper n χ) hw (fun W x hx => ?_) ?_
      (fun x y hx hy => ?_)
    · exact le_largestProper W.2 (W.2.1.2.1 k hk x hx)
    · rw [map_zero]
      exact Submodule.zero_mem _
    · rw [map_add]
      exact add_mem hx hy
  · have key : w ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) ∧
        rightDerivative (matrixModel ℝ n) X w ∈ largestProper n χ := by
      refine Submodule.iSup_induction (fun W : {W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) //
        IsProperGKStable n χ W} => (W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)))
        (motive := fun w =>
        w ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n) ∧
          rightDerivative (matrixModel ℝ n) X w ∈ largestProper n χ) hw
        (fun W x hx => ⟨W.2.1.1 hx, le_largestProper W.2 (W.2.1.2.2 X x hx)⟩) ?_
        (fun x y hx hy => ?_)
      · exact ⟨Submodule.zero_mem _, by rw [rightDerivative_zero]; exact Submodule.zero_mem _⟩
      · refine ⟨add_mem hx.1 hy.1, ?_⟩
        rw [rightDerivative_add hx.1.1.1 hy.1.1.1]
        exact add_mem hx.2 hy.2
    exact key.2

/-- **The largest proper submodule.** For strictly dominant signed-power characters `χ` with
signs `χ_l(-1) = (-1)^{p_l}`, the sum of all proper `(𝔤, K)`-stable subspaces of the
`O(n)`-finite principal series of `χ` is proper and `(𝔤, K)`-stable, and it lies in the kernel
of the Jacquet integral. -/
theorem isProperGKStable_largestProper (hχ : IsSignedPower χ e)
    (he : IsStrictlyDominant e (n - 1)) {p : ℕ → ℕ} (hp : ∀ l, χ l (-1) = (-1) ^ p l) :
    IsProperGKStable n χ (largestProper n χ) ∧ largestProper n χ ≤ jacquetKernel n hχ he := by
  have hker : largestProper n χ ≤ jacquetKernel n hχ he := iSup_le fun W => by
    obtain ⟨⟨hWX, hWK, hWD⟩, f, hf, hfW⟩ := W.2
    exact jacquet_eq_zero_of_proper hχ he _ hWX hWK hWD hf hfW
  refine ⟨⟨isGKStable_largestProper, ?_⟩, hker⟩
  obtain ⟨f, hf, hf0⟩ := exists_jacquet_ne_zero hχ he hp
  exact ⟨f, hf, fun hfR => hf0 (hker hfR).2⟩

end StrictPrincipalSeriesQuotient

end Langlands.Archimedean
