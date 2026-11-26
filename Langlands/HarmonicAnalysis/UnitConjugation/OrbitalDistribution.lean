import Langlands.HarmonicAnalysis.UnitConjugation.InvariantDistribution
import Langlands.Analysis.Local.QuotientMeasure

/-!
# Orbital distributions on an algebra for the conjugation action of its units

Let `A` be a ring, regarded as the Lie algebra of its unit group `Aˣ`, which acts on `A` by
conjugation. For `X₀ : A` let `C = C(X₀)` be the centralizer of `X₀` in `Aˣ`, the stabilizer
of `X₀` for the conjugation action (`conjugationCentralizer`). The function
`g ↦ f(g⁻¹ X₀ g)` on `Aˣ` is invariant under left multiplication by `C`, so it descends to the
Library's left coset space `C \ Aˣ` (`orbitalIntegrand`). For a measure `ν` on `C \ Aˣ`:

* `OrbitalIntegralConverges X₀ ν`: for every Schwartz–Bruhat function `f` on `A`, the orbital
  integrand of `f` is integrable for `ν`, that is the integral converges absolutely;
* under this premise, `orbitalDistribution X₀ ν h` is the distribution
  `f ↦ ∫_{C \ Aˣ} f(g⁻¹ X₀ g) dν(Cg)`.

The intended measures are the quotient measures compatible with Haar measures on `Aˣ` and on
`C` (`QuotientIntegration.IsCompatible`); right invariance of `ν`, part of compatibility, makes
the orbital distribution conjugation-invariant (`orbitalDistribution_isConjugationInvariant`),
and it is always supported in the closure of the orbit `{X₀}^G`
(`orbitalDistribution_mem_supportedOn`); so for a compatible `ν` it lies in `J({X₀})`
(`orbitalDistribution_mem_invariantSupportedIn`), with the compact set `{X₀}`.

The orbit of `0` is `{0}`: its centralizer is the whole unit group and its orbital distribution
is `f ↦ ν.real Set.univ · f(0)`, the total mass of `ν` times `f(0)` when `ν` is finite
(`orbitalDistribution_zero_apply`). Conjugates of a nilpotent element
are nilpotent (`isNilpotent_of_mem_conjugationSaturation`).

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), Introduction, printed pp. 2–3: for an orbit `O ∋ X₀`,
`μ_O(f) = ∫_{G/C_G(X₀)} f(x.X₀) dx*` with `dx*` an invariant measure on `G/C_G(X₀)`.
The map `C g ↦ g⁻¹ C` identifies the left coset space `C \ G` used here with `G/C`, and
`f(g⁻¹ X₀ g) = f(x.X₀)` for `x = g⁻¹`.
-/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.UnitConjugation

open QuotientIntegration

universe v

section Centralizer

variable {A : Type v} [Ring A]

/-- The centralizer of `X₀` in the unit group: the stabilizer of `X₀` for the conjugation
action `u • X = u X u⁻¹` of `Aˣ` on `A`. -/
def conjugationCentralizer (X₀ : A) : Subgroup Aˣ :=
  (MulAction.stabilizer (ConjAct Aˣ) X₀).comap (ConjAct.toConjAct : Aˣ ≃* ConjAct Aˣ).toMonoidHom

theorem mem_conjugationCentralizer_iff_smul (X₀ : A) (u : Aˣ) :
    u ∈ conjugationCentralizer X₀ ↔ ConjAct.toConjAct u • X₀ = X₀ :=
  Iff.rfl

theorem mem_conjugationCentralizer_iff (X₀ : A) (u : Aˣ) :
    u ∈ conjugationCentralizer X₀ ↔ (u : A) * X₀ = X₀ * u := by
  rw [mem_conjugationCentralizer_iff_smul, ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
  constructor
  · intro h
    calc (u : A) * X₀ = (u : A) * X₀ * ((u⁻¹ : Aˣ) : A) * u := by
          rw [mul_assoc _ ((u⁻¹ : Aˣ) : A), Units.inv_mul, mul_one]
      _ = X₀ * u := by rw [h]
  · intro h
    rw [h, mul_assoc, Units.mul_inv, mul_one]

/-- Every unit centralizes `0`. -/
theorem conjugationCentralizer_zero : conjugationCentralizer (0 : A) = ⊤ := by
  ext u
  simp [mem_conjugationCentralizer_iff]

/-- The function `g ↦ f(g⁻¹ X₀ g)` on `Aˣ`, constant on the left cosets `C g` of the
centralizer, as a function on the left coset space `C \ Aˣ`. -/
def orbitalIntegrand (X₀ : A) (f : A → ℂ) : LeftQuotient (conjugationCentralizer X₀) → ℂ :=
  descend (conjugationCentralizer X₀) (fun g : Aˣ => f (((g⁻¹ : Aˣ) : A) * X₀ * (g : A)))
    (by
      intro h g
      have hh := (mem_conjugationCentralizer_iff X₀ h.val).1 h.property
      have hX : ((h.val⁻¹ : Aˣ) : A) * X₀ * (h.val : A) = X₀ := by
        rw [mul_assoc, ← hh, ← mul_assoc, Units.inv_mul, one_mul]
      congr 1
      simp only [mul_inv_rev, Units.val_mul]
      calc ((g⁻¹ : Aˣ) : A) * ((h.val⁻¹ : Aˣ) : A) * X₀ * ((h.val : A) * (g : A))
          = ((g⁻¹ : Aˣ) : A) * (((h.val⁻¹ : Aˣ) : A) * X₀ * (h.val : A)) * (g : A) := by
            simp only [mul_assoc]
        _ = ((g⁻¹ : Aˣ) : A) * X₀ * (g : A) := by rw [hX])

@[simp]
theorem orbitalIntegrand_mk (X₀ : A) (f : A → ℂ) (g : Aˣ) :
    orbitalIntegrand X₀ f (Quotient.mk _ g) = f (((g⁻¹ : Aˣ) : A) * X₀ * (g : A)) := rfl

theorem orbitalIntegrand_add (X₀ : A) (f f' : A → ℂ) :
    orbitalIntegrand X₀ (f + f') = orbitalIntegrand X₀ f + orbitalIntegrand X₀ f' := by
  funext q
  induction q using Quotient.inductionOn with
  | h g => rfl

theorem orbitalIntegrand_smul (X₀ : A) (c : ℂ) (f : A → ℂ) :
    orbitalIntegrand X₀ (c • f) = c • orbitalIntegrand X₀ f := by
  funext q
  induction q using Quotient.inductionOn with
  | h g => rfl

/-- The orbital integrand of `0` is the constant `f(0)`. -/
theorem orbitalIntegrand_zero (f : A → ℂ) :
    orbitalIntegrand (0 : A) f = fun _ => f 0 := by
  funext q
  induction q using Quotient.inductionOn with
  | h g => simp

end Centralizer

section Distribution

variable {A : Type v} [Ring A] [TopologicalSpace A]

/-- Absolute convergence of the orbital integrals of `X₀` for the measure `ν` on `C \ Aˣ`: for
every Schwartz–Bruhat function `f` on `A`, `Cg ↦ f(g⁻¹ X₀ g)` is integrable for `ν`. -/
def OrbitalIntegralConverges (X₀ : A)
    [MeasurableSpace (LeftQuotient (conjugationCentralizer X₀))]
    (ν : Measure (LeftQuotient (conjugationCentralizer X₀))) : Prop :=
  ∀ f : SchwartzBruhat A, Integrable (orbitalIntegrand X₀ f) ν

/-- The orbital distribution of `X₀` for the measure `ν` on `C \ Aˣ`, under absolute
convergence of its integrals: `f ↦ ∫_{C \ Aˣ} f(g⁻¹ X₀ g) dν(Cg)`. -/
def orbitalDistribution (X₀ : A) [MeasurableSpace (LeftQuotient (conjugationCentralizer X₀))]
    (ν : Measure (LeftQuotient (conjugationCentralizer X₀)))
    (hν : OrbitalIntegralConverges X₀ ν) : Distribution A where
  toFun f := ∫ q, orbitalIntegrand X₀ f q ∂ν
  map_add' f f' := by
    change ∫ q, orbitalIntegrand X₀ ((f : A → ℂ) + f') q ∂ν = _
    rw [orbitalIntegrand_add]
    exact integral_add (hν f) (hν f')
  map_smul' c f := by
    change ∫ q, orbitalIntegrand X₀ (c • (f : A → ℂ)) q ∂ν = c • ∫ q, orbitalIntegrand X₀ f q ∂ν
    rw [orbitalIntegrand_smul]
    exact integral_smul c _

theorem orbitalDistribution_apply (X₀ : A)
    [MeasurableSpace (LeftQuotient (conjugationCentralizer X₀))]
    (ν : Measure (LeftQuotient (conjugationCentralizer X₀)))
    (hν : OrbitalIntegralConverges X₀ ν) (f : SchwartzBruhat A) :
    orbitalDistribution X₀ ν hν f = ∫ q, orbitalIntegrand X₀ f q ∂ν := rfl

/-- A finite measure on `C(0) \ Aˣ` makes the orbital integrals of `0` converge. -/
theorem orbitalIntegralConverges_zero
    [MeasurableSpace (LeftQuotient (conjugationCentralizer (0 : A)))]
    (ν : Measure (LeftQuotient (conjugationCentralizer (0 : A)))) [IsFiniteMeasure ν] :
    OrbitalIntegralConverges (0 : A) ν := fun f => by
  rw [orbitalIntegrand_zero]
  exact integrable_const _

/-- The orbital distribution of `0` is `f ↦ ν.real Set.univ · f(0)`, a multiple of the Dirac
distribution at `0`; for a finite `ν` the scalar is the total mass of `ν`. -/
theorem orbitalDistribution_zero_apply
    [MeasurableSpace (LeftQuotient (conjugationCentralizer (0 : A)))]
    (ν : Measure (LeftQuotient (conjugationCentralizer (0 : A))))
    (hν : OrbitalIntegralConverges (0 : A) ν) (f : SchwartzBruhat A) :
    orbitalDistribution (0 : A) ν hν f = ν.real Set.univ * f 0 := by
  rw [orbitalDistribution_apply, orbitalIntegrand_zero, integral_const, Complex.real_smul]

end Distribution

section Invariance

variable {A : Type v} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The orbital integrand of `f ∘ Ad u` is that of `f` translated on the right by `u⁻¹`. -/
theorem orbitalIntegrand_pullback_conjugation (X₀ : A) (u : Aˣ) (f : SchwartzBruhat A) :
    orbitalIntegrand X₀ (Hecke.TestFunction.pullback (conjugationHomeomorph u) f) =
      fun q => orbitalIntegrand X₀ f (rightTranslate (conjugationCentralizer X₀) u⁻¹ q) := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [rightTranslate_mk, orbitalIntegrand_mk, orbitalIntegrand_mk]
    change (f : A → ℂ) (conjugationHomeomorph u (((g⁻¹ : Aˣ) : A) * X₀ * (g : A))) = _
    simp only [conjugationHomeomorph_apply, mul_inv_rev, inv_inv, Units.val_mul, mul_assoc]

/-- The orbital distribution of `X₀` lies in the closure of the orbit `{X₀}^G`: it annihilates
every test function vanishing there. -/
theorem orbitalDistribution_mem_supportedOn (X₀ : A)
    [MeasurableSpace (LeftQuotient (conjugationCentralizer X₀))]
    (ν : Measure (LeftQuotient (conjugationCentralizer X₀)))
    (hν : OrbitalIntegralConverges X₀ ν) :
    orbitalDistribution X₀ ν hν ∈
      Distribution.supportedOn (closure (conjugationSaturation ({X₀} : Set A))) := by
  intro f hf
  rw [orbitalDistribution_apply]
  have h0 : orbitalIntegrand X₀ f = fun _ => 0 := by
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [orbitalIntegrand_mk]
      apply hf
      apply subset_closure
      refine mem_conjugationSaturation_iff.2 ⟨g⁻¹, X₀, rfl, ?_⟩
      rw [inv_inv]
  rw [h0, integral_zero]

/-- Right invariance of `ν` makes the orbital distribution invariant under conjugation. -/
theorem orbitalDistribution_isConjugationInvariant (X₀ : A)
    [MeasurableSpace (LeftQuotient (conjugationCentralizer X₀))]
    [BorelSpace (LeftQuotient (conjugationCentralizer X₀))]
    (ν : Measure (LeftQuotient (conjugationCentralizer X₀)))
    (hinv : ∀ g : Aˣ, MeasurePreserving (rightTranslate (conjugationCentralizer X₀) g) ν ν)
    (hν : OrbitalIntegralConverges X₀ ν) :
    IsConjugationInvariant (orbitalDistribution X₀ ν hν) := by
  rw [isConjugationInvariant_iff]
  intro u f
  rw [orbitalDistribution_apply, orbitalDistribution_apply,
    orbitalIntegrand_pullback_conjugation]
  exact (hinv u⁻¹).integral_comp
    (rightTranslate (conjugationCentralizer X₀) u⁻¹).measurableEmbedding _

/-- For a right-invariant `ν`, in particular a compatible quotient measure, the orbital
distribution of `X₀` lies in `J({X₀})`. -/
theorem orbitalDistribution_mem_invariantSupportedIn (X₀ : A)
    [MeasurableSpace (LeftQuotient (conjugationCentralizer X₀))]
    [BorelSpace (LeftQuotient (conjugationCentralizer X₀))]
    (ν : Measure (LeftQuotient (conjugationCentralizer X₀)))
    (hinv : ∀ g : Aˣ, MeasurePreserving (rightTranslate (conjugationCentralizer X₀) g) ν ν)
    (hν : OrbitalIntegralConverges X₀ ν) :
    orbitalDistribution X₀ ν hν ∈ invariantSupportedIn ({X₀} : Set A) :=
  ⟨orbitalDistribution_isConjugationInvariant X₀ ν hinv hν,
    orbitalDistribution_mem_supportedOn X₀ ν hν⟩

/-- The same membership for a quotient measure compatible with measures `μG` on `Aˣ` and `μH`
on the centralizer. -/
theorem orbitalDistribution_mem_invariantSupportedIn_of_isCompatible (X₀ : A)
    [MeasurableSpace Aˣ] [BorelSpace Aˣ]
    [MeasurableSpace (LeftQuotient (conjugationCentralizer X₀))]
    [BorelSpace (LeftQuotient (conjugationCentralizer X₀))]
    (μG : Measure Aˣ) (μH : Measure (conjugationCentralizer X₀)) [μH.IsMulRightInvariant]
    (ν : Measure (LeftQuotient (conjugationCentralizer X₀)))
    (hcompat : IsCompatible (conjugationCentralizer X₀) μG μH ν)
    (hν : OrbitalIntegralConverges X₀ ν) :
    orbitalDistribution X₀ ν hν ∈ invariantSupportedIn ({X₀} : Set A) :=
  orbitalDistribution_mem_invariantSupportedIn X₀ ν hcompat.right_invariant hν

/-- Conjugates of nilpotent elements are nilpotent: the orbit of a nilpotent element lies in
the nilpotent elements. -/
theorem isNilpotent_of_mem_conjugationSaturation {N Y : A} (hN : IsNilpotent N)
    (hY : Y ∈ conjugationSaturation ({N} : Set A)) : IsNilpotent Y := by
  obtain ⟨u, X, hX, rfl⟩ := mem_conjugationSaturation_iff.1 hY
  rw [Set.mem_singleton_iff] at hX
  subst hX
  obtain ⟨k, hk⟩ := hN
  refine ⟨k, ?_⟩
  have h : ∀ n : ℕ, ((u : A) * X * ((u⁻¹ : Aˣ) : A)) ^ (n + 1) =
      (u : A) * X ^ (n + 1) * ((u⁻¹ : Aˣ) : A) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, pow_succ X (n + 1)]
      simp only [mul_assoc, Units.inv_mul_cancel_left]
  cases k with
  | zero => rw [pow_zero] at hk ⊢; exact hk
  | succ n => rw [h n, hk, mul_zero, zero_mul]

end Invariance

end Langlands.HarmonicAnalysis.UnitConjugation
