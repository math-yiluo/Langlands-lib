import Langlands.HarmonicAnalysis.Distribution.ClopenCutoff
import Langlands.HarmonicAnalysis.UnitConjugation.FourierRegularityStatement
import Langlands.HarmonicAnalysis.UnitConjugation.HoweFinitenessStatement
import Langlands.HarmonicAnalysis.UnitConjugation.ConjugationDomainStatement
import Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalDensityStatement
import Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalFourierRegularityStatement
import Langlands.HarmonicAnalysis.Bicharacter.FourierRestriction
import Langlands.HarmonicAnalysis.Distribution.LocallyIntegrableGluing
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# Harish-Chandra's Theorem 4.4 (1) from its four inputs

Harish-Chandra derives the local summability clause of Theorem 4.4 from Howe's finiteness
theorem (Theorem 12.1), the vanishing of invariant distributions on functions with vanishing
regular orbital integrals (Theorem 3.1), the existence of `G`-domains (Lemma 4.3) and the local
summability of the Fourier transforms of regular orbital integrals (Theorem 1.1). This module
carries out that derivation for the Lie algebra `A` of the unit group of a finite-dimensional
semisimple algebra: `lieAlgebraFourierRegularityReduction` proves
`LieAlgebraFourierRegularityReductionStatement`, the implication from
`LieAlgebraHoweFinitenessStatement`, `LieAlgebraRegularOrbitalDensityStatement`,
`LieAlgebraConjugationDomainStatement` and `RegularOrbitalFourierRegularityStatement` to
`LieAlgebraFourierRegularityStatement`. It does not prove the four inputs.

The steps (in the namespace `FourierRegularityReduction`):

* `apply_clopenCutoff`, `orbitalDistribution_clopenCutoff_of_mem`,
  `orbitalDistribution_clopenCutoff_of_notMem`: cutting a test function off by the
  characteristic function of a `G`-domain `D ⊇ ω` changes neither the value of a distribution
  of `J(ω)` nor the orbital integrals over orbits in `D`, and kills those over orbits outside
  `D` (Harish-Chandra's Lemma 4.1);
* `exists_mem_span_regularOrbitals_eq`: on the test functions invariant under an open
  subgroup `L`, every `T ∈ J(ω)` agrees with a finite linear combination of orbital
  distributions of regular elements of `D` (Corollary 4.2);
* `exists_density_of_mem_span`: the Fourier transform of such a combination is a locally
  integrable function (Theorem 1.1);
* `lieAlgebraFourierRegularityReduction`: tests supported in a compact open subgroup `M` have
  Fourier transforms invariant under its annihilator `L`, so `T̂` agrees there with a locally
  integrable function; these local densities are glued (Theorem 4.4).

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), §4, printed pp. 30–31: Lemma 4.1, Corollary 4.2, Lemma 4.3 and the
proof of Theorem 4.4.
-/

noncomputable section

open MeasureTheory Function Topology

namespace Langlands.HarmonicAnalysis

open UnitConjugation QuotientIntegration

universe u v

/-- Harish-Chandra's derivation of Theorem 4.4 (1): Howe's finiteness theorem, Theorem 3.1,
Lemma 4.3 and the local summability in Theorem 1.1, for the unit groups of finite-dimensional
semisimple algebras, imply the local summability of the Fourier transforms of the distributions
in `J(ω)`. -/
def LieAlgebraFourierRegularityReductionStatement.{u', v'} : Prop :=
  LieAlgebraHoweFinitenessStatement.{u', v'} →
    LieAlgebraRegularOrbitalDensityStatement.{u', v'} →
      LieAlgebraConjugationDomainStatement.{u', v'} →
        RegularOrbitalFourierRegularityStatement.{u', v'} →
          LieAlgebraFourierRegularityStatement.{u', v'}

namespace FourierRegularityReduction

open Langlands.Whittaker.BruhatCompatibleSupport (clopenCutoff clopenCutoff_apply_of_mem clopenCutoff_apply_of_notMem)

section Ring

variable {A : Type v} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in
/-- The restriction `j_L T` evaluates `T` at an `L`-invariant test function. -/
theorem restrictToLatticeTests_apply (L : AddSubgroup A) (T : Distribution A)
    (f : latticeInvariantTests L) : restrictToLatticeTests L T f = T f := rfl

/-- The saturation of a subset of a conjugation-invariant set lies in that set. -/
theorem conjugationSaturation_subset_of_invariant {ω D : Set A}
    (hinv : ∀ (u : Aˣ), ∀ X ∈ D, conjugationHomeomorph u X ∈ D) (hωD : ω ⊆ D) :
    conjugationSaturation ω ⊆ D := by
  intro Y hY
  obtain ⟨u, X, hX, rfl⟩ := mem_conjugationSaturation_iff.1 hY
  exact hinv u X (hωD hX)

/-- The orbit of a point of `ω^G` lies in `ω^G`. -/
theorem conjugationSaturation_singleton_subset {ω : Set A} {X : A}
    (hX : X ∈ conjugationSaturation ω) :
    conjugationSaturation ({X} : Set A) ⊆ conjugationSaturation ω := by
  intro Y hY
  obtain ⟨u, X', hX', rfl⟩ := mem_conjugationSaturation_iff.1 hY
  rw [Set.mem_singleton_iff] at hX'
  subst hX'
  obtain ⟨w, Z, hZ, rfl⟩ := mem_conjugationSaturation_iff.1 hX
  refine mem_conjugationSaturation_iff.2 ⟨u * w, Z, hZ, ?_⟩
  simp only [Units.val_mul, mul_inv_rev, mul_assoc]

/-- A distribution of `J({X})` with `X ∈ ω₀^G` lies in `J(ω₀)`. -/
theorem mem_invariantSupportedIn_of_mem_saturation {ω₀ : Set A} {X : A}
    (hX : X ∈ conjugationSaturation ω₀) {T : Distribution A}
    (hT : T ∈ invariantSupportedIn ({X} : Set A)) : T ∈ invariantSupportedIn ω₀ := by
  rw [mem_invariantSupportedIn_iff] at hT ⊢
  exact ⟨hT.1, fun f hf => hT.2 f fun Y hY =>
    hf Y (closure_mono (conjugationSaturation_singleton_subset hX) hY)⟩

/-- A distribution of `J(ω)` does not see the cutoff of a test function to a closed
invariant set containing `ω`. -/
theorem apply_clopenCutoff {ω D : Set A} (hD : IsClopen D)
    (hinv : ∀ (u : Aˣ), ∀ X ∈ D, conjugationHomeomorph u X ∈ D) (hωD : ω ⊆ D)
    {T : Distribution A} (hT : T ∈ invariantSupportedIn ω) (f : SchwartzBruhat A) :
    T (clopenCutoff hD f) = T f := by
  have hsub : closure (conjugationSaturation ω) ⊆ D :=
    hD.isClosed.closure_subset_iff.2 (conjugationSaturation_subset_of_invariant hinv hωD)
  have h := ((mem_invariantSupportedIn_iff ω T).1 hT).2 (f - clopenCutoff hD f) (by
    intro Y hY
    change f Y - clopenCutoff hD f Y = 0
    rw [clopenCutoff_apply_of_mem hD f (hsub hY), sub_self])
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

/-- The orbital integrand of the cutoff, for an orbit inside the invariant set. -/
theorem orbitalIntegrand_clopenCutoff_of_mem {D : Set A} (hD : IsClopen D)
    (hinv : ∀ (u : Aˣ), ∀ X ∈ D, conjugationHomeomorph u X ∈ D) {X : A} (hX : X ∈ D)
    (f : SchwartzBruhat A) :
    orbitalIntegrand X (clopenCutoff hD f) = orbitalIntegrand X f := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [orbitalIntegrand_mk, orbitalIntegrand_mk]
    apply clopenCutoff_apply_of_mem
    have h := hinv g⁻¹ X hX
    rw [conjugationHomeomorph_apply, inv_inv] at h
    exact h

/-- The orbital integrand of the cutoff vanishes for an orbit outside the invariant set. -/
theorem orbitalIntegrand_clopenCutoff_of_notMem {D : Set A} (hD : IsClopen D)
    (hinv : ∀ (u : Aˣ), ∀ X ∈ D, conjugationHomeomorph u X ∈ D) {X : A} (hX : X ∉ D)
    (f : SchwartzBruhat A) :
    orbitalIntegrand X (clopenCutoff hD f) = fun _ => 0 := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [orbitalIntegrand_mk]
    apply clopenCutoff_apply_of_notMem
    intro h
    apply hX
    have h' := hinv g _ h
    rw [conjugationHomeomorph_apply] at h'
    simpa only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one] using h'

theorem orbitalDistribution_clopenCutoff_of_mem {D : Set A} (hD : IsClopen D)
    (hinv : ∀ (u : Aˣ), ∀ X ∈ D, conjugationHomeomorph u X ∈ D) {X : A} (hX : X ∈ D)
    [MeasurableSpace (LeftQuotient (conjugationCentralizer X))]
    (ν : Measure (LeftQuotient (conjugationCentralizer X)))
    (hconv : OrbitalIntegralConverges X ν) (f : SchwartzBruhat A) :
    orbitalDistribution X ν hconv (clopenCutoff hD f) = orbitalDistribution X ν hconv f := by
  rw [orbitalDistribution_apply, orbitalDistribution_apply,
    orbitalIntegrand_clopenCutoff_of_mem hD hinv hX]

theorem orbitalDistribution_clopenCutoff_of_notMem {D : Set A} (hD : IsClopen D)
    (hinv : ∀ (u : Aˣ), ∀ X ∈ D, conjugationHomeomorph u X ∈ D) {X : A} (hX : X ∉ D)
    [MeasurableSpace (LeftQuotient (conjugationCentralizer X))]
    (ν : Measure (LeftQuotient (conjugationCentralizer X)))
    (hconv : OrbitalIntegralConverges X ν) (f : SchwartzBruhat A) :
    orbitalDistribution X ν hconv (clopenCutoff hD f) = 0 := by
  rw [orbitalDistribution_apply, orbitalIntegrand_clopenCutoff_of_notMem hD hinv hX,
    integral_zero]

end Ring

section Algebra

variable (F : Type u) [Field F] {A : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A]
  [TopologicalSpace A] [IsTopologicalRing A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]

/-- The orbital distributions `μ_X` of the regular elements `X ∈ g'` lying in `D`, for Haar
measures on `Aˣ` and on the centralizer of `X`, a compatible quotient measure and absolutely
convergent orbital integrals. -/
def regularOrbitals (D : Set A) : Set (Distribution A) :=
  {R | ∃ X ∈ regularSet F A, X ∈ D ∧
    ∃ (_ : MeasurableSpace (LeftQuotient (conjugationCentralizer X)))
      (_ : BorelSpace (LeftQuotient (conjugationCentralizer X)))
      (μG : Measure Aˣ) (_ : μG.IsHaarMeasure)
      (μH : Measure (conjugationCentralizer X)) (_ : μH.IsHaarMeasure)
      (_ : μH.IsMulRightInvariant)
      (ν : Measure (LeftQuotient (conjugationCentralizer X)))
      (_ : IsCompatible (conjugationCentralizer X) μG μH ν)
      (hconv : OrbitalIntegralConverges X ν), R = orbitalDistribution X ν hconv}

end Algebra

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {A : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
  [TopologicalSpace A] [IsModuleTopology F A] [IsTopologicalRing A]
  [MeasurableSpace Aˣ] [BorelSpace Aˣ]

/-- **Harish-Chandra's Corollary 4.2.** Let `D` be a `G`-domain with `ω ⊆ D ⊆ ω₀^G`, `ω₀`
compact, and `L` an open subgroup. On the `L`-invariant test functions, every `T ∈ J(ω)` agrees
with a finite linear combination of orbital distributions of regular elements of `D`. -/
theorem exists_mem_span_regularOrbitals_eq
    (hHowe : LieAlgebraHoweFinitenessStatement.{u, v})
    (hDens : LieAlgebraRegularOrbitalDensityStatement.{u, v})
    {ω ω₀ D : Set A} (hω₀ : IsCompact ω₀) (hD : IsClopen D)
    (hinv : ∀ (u : Aˣ), ∀ X ∈ D, conjugationHomeomorph u X ∈ D) (hωD : ω ⊆ D)
    (hDω₀ : D ⊆ conjugationSaturation ω₀) (L : AddSubgroup A) (hL : IsOpen (L : Set A))
    (T : Distribution A) (hT : T ∈ invariantSupportedIn ω) :
    ∃ R ∈ Submodule.span ℂ (regularOrbitals F D), ∀ f ∈ latticeInvariantTests L, T f = R f := by
  let W : Submodule ℂ (Module.Dual ℂ (latticeInvariantTests L)) :=
    (invariantSupportedIn ω₀).map (restrictToLatticeTests L)
  have : FiniteDimensional ℂ W := hHowe F A ω₀ hω₀ L hL
  let S : Submodule ℂ (Module.Dual ℂ (latticeInvariantTests L)) :=
    (Submodule.span ℂ (regularOrbitals F D)).map (restrictToLatticeTests L)
  have hSW : S ≤ W := by
    refine Submodule.map_mono (Submodule.span_le.2 ?_)
    rintro _ ⟨X, -, hXD, _, _, μG, _, μH, _, _, ν, hcompat, hconv, rfl⟩
    exact mem_invariantSupportedIn_of_mem_saturation (hDω₀ hXD)
      (orbitalDistribution_mem_invariantSupportedIn_of_isCompatible X μG μH ν hcompat hconv)
  have : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSW
  have hjT : restrictToLatticeTests L T ∈ S := by
    by_contra hnot
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (K := ℂ)
      (V := latticeInvariantTests L) (W := S), Submodule.mem_dualAnnihilator] at hnot
    push Not at hnot
    obtain ⟨g, hg, hTg⟩ := hnot
    apply hTg
    rw [restrictToLatticeTests_apply, ← apply_clopenCutoff hD hinv hωD hT]
    refine hDens F A (clopenCutoff hD g.1) ?_ T ((mem_invariantSupportedIn_iff ω T).1 hT).1
    intro X hX _ _ μG _ μH _ _ ν hcompat hconv
    by_cases hXD : X ∈ D
    · rw [orbitalDistribution_clopenCutoff_of_mem hD hinv hXD]
      have hmem : orbitalDistribution X ν hconv ∈ regularOrbitals F D :=
        ⟨X, hX, hXD, _, inferInstance, μG, inferInstance, μH, inferInstance, inferInstance, ν,
          hcompat, hconv, rfl⟩
      exact (Submodule.mem_dualCoannihilator g).1 hg _
        (Submodule.mem_map_of_mem (Submodule.subset_span hmem))
    · exact orbitalDistribution_clopenCutoff_of_notMem hD hinv hXD ν hconv _
  obtain ⟨R, hR, hRT⟩ := Submodule.mem_map.1 hjT
  refine ⟨R, hR, fun f hf => ?_⟩
  have h := LinearMap.congr_fun hRT ⟨f, hf⟩
  rw [restrictToLatticeTests_apply, restrictToLatticeTests_apply] at h
  exact h.symm

variable [MeasurableSpace A] [BorelSpace A]

/-- **Harish-Chandra's Theorem 1.1, applied to a combination.** The Fourier transform of a
finite linear combination of orbital distributions of regular elements is a locally integrable
function. -/
theorem exists_density_of_mem_span
    (hP2 : RegularOrbitalFourierRegularityStatement.{u, v})
    (ψ : UnitaryAdditiveCharacter F) (B : LinearMap.BilinForm F A) (hB : IsInvariantPairing B)
    (μ : AdditiveHaarMeasure A) {D : Set A} {R : Distribution A}
    (hR : R ∈ Submodule.span ℂ (regularOrbitals F D)) :
    ∃ Θ : A → ℂ, LocallyIntegrable Θ μ.measure ∧ ∀ f : SchwartzBruhat A,
      distributionFourier ψ hB.isSymm hB.nondegenerate μ R f = ∫ Y, Θ Y * f Y ∂μ.measure := by
  have := t2Space_of_finiteDimensional F A
  induction hR using Submodule.span_induction with
  | mem R hR =>
    obtain ⟨X, hX, -, _, _, μG, _, μH, _, _, ν, hcompat, hconv, rfl⟩ := hR
    exact hP2 F A ψ B hB μ X hX μG μH ν hcompat hconv
  | zero =>
    exact ⟨0, locallyIntegrable_zero, fun f => by simp⟩
  | add R₁ R₂ _ _ ih₁ ih₂ =>
    obtain ⟨Θ₁, h₁, e₁⟩ := ih₁
    obtain ⟨Θ₂, h₂, e₂⟩ := ih₂
    refine ⟨Θ₁ + Θ₂, h₁.add h₂, fun f => ?_⟩
    have i₁ := h₁.integrable_smul_right_of_hasCompactSupport f.continuous f.hasCompactSupport
    have i₂ := h₂.integrable_smul_right_of_hasCompactSupport f.continuous f.hasCompactSupport
    simp only [smul_eq_mul] at i₁ i₂
    rw [map_add, LinearMap.add_apply, e₁, e₂, ← integral_add i₁ i₂]
    congr 1
    funext Y
    simp only [Pi.add_apply, add_mul]
  | smul c R _ ih =>
    obtain ⟨Θ, h, e⟩ := ih
    refine ⟨c • Θ, h.smul c, fun f => ?_⟩
    rw [map_smul, LinearMap.smul_apply, e, smul_eq_mul, ← integral_const_mul]
    congr 1
    funext Y
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

end LocalField

end FourierRegularityReduction

open FourierRegularityReduction

/-- **Harish-Chandra's Theorem 4.4 (1) from its inputs.** Howe's finiteness theorem,
Theorem 3.1, Lemma 4.3 and the local summability of Theorem 1.1 imply
`LieAlgebraFourierRegularityStatement`. -/
theorem lieAlgebraFourierRegularityReduction :
    LieAlgebraFourierRegularityReductionStatement.{u, v} := by
  intro hHowe hDens hDom hP2 F _ _ _ _ _ A _ _ _ _ _ _ _ _
  have := IsModuleTopology.isTopologicalRing F A
  intro ψ B hB μ ω hω T hT
  let : MeasurableSpace Aˣ := borel Aˣ
  have : BorelSpace Aˣ := ⟨rfl⟩
  have := IsModuleTopology.isTopologicalAddGroup F A
  have := t2Space_of_finiteDimensional F A
  have := locallyCompactSpace_of_finiteDimensional F A
  have := secondCountableTopology_of_finiteDimensional F A
  have := compactOpenExhaustion_of_finiteDimensional F A
  have : NonarchimedeanAddGroup A :=
    { toIsTopologicalAddGroup := inferInstance
      is_nonarchimedean := fun U hU => by
        obtain ⟨L, -, hLo, hLU⟩ := CompactOpenExhaustion.exists_subset U hU
        exact ⟨⟨L, hLo⟩, hLU⟩ }
  have : TotallyDisconnectedSpace A := inferInstance
  obtain ⟨ω₀, hω₀, D, hD, hinv, hωD, hDω₀⟩ := hDom F A ω hω
  let he := isSelfDualBicharacter_pairingCharacter ψ hB.isSymm hB.nondegenerate
  have hlocal : ∀ x : A, ∃ U : Set A, IsOpen U ∧ x ∈ U ∧ ∃ θ : A → ℂ,
      (∀ _ : Unit, LocallyIntegrableOn θ U μ.measure ∧
        ∀ f : SchwartzBruhat A, support (f : A → ℂ) ⊆ U →
          distributionFourier ψ hB.isSymm hB.nondegenerate μ T f =
            ∫ y, f y * θ y ∂μ.measure) ∧
      ∀ y ∈ U ∩ (∅ : Set A), ∀ᶠ z in 𝓝 y, θ z = θ y := by
    intro x
    obtain ⟨M, hMc, hMo, hxM⟩ :=
      CompactOpenExhaustion.exists_superset ({x} : Set A) isCompact_singleton
    have hL : IsOpen (he.annihilator (M : Set A) : Set A) := he.isOpen_annihilator hMc
    obtain ⟨R, hR, hTR⟩ := exists_mem_span_regularOrbitals_eq F hHowe hDens hω₀ hD hinv hωD
      hDω₀ (he.annihilator (M : Set A)) hL T hT
    obtain ⟨θ, hθ, hRθ⟩ := exists_density_of_mem_span F hP2 ψ B hB μ hR
    refine ⟨M, hMo, hxM rfl, θ, fun _ => ⟨hθ.locallyIntegrableOn _, fun f hf => ?_⟩, ?_⟩
    · have hinvf : ∀ t ∈ he.annihilator (M : Set A), ∀ X : A,
          pairingFourierSB ψ hB.isSymm hB.nondegenerate μ f (X + t) =
            pairingFourierSB ψ hB.isSymm hB.nondegenerate μ f X :=
        fun t ht X => bicharacterFourierSB_annihilatorInvariant μ.measure he M f hf t ht X
      rw [distributionFourier_apply, hTR _ hinvf, ← distributionFourier_apply, hRθ f]
      congr 1
      funext y
      exact mul_comm _ _
    · intro y hy
      exact absurd hy.2 (Set.notMem_empty y)
  obtain ⟨Θ, hΘ, -⟩ := Distribution.exists_locallyIntegrableDensity_of_locally.{v, 0} A
    (fun _ : Unit => μ.measure)
    (fun _ : Unit => distributionFourier ψ hB.isSymm hB.nondegenerate μ T) ∅ hlocal
  obtain ⟨hΘi, hΘe⟩ := hΘ ()
  refine ⟨Θ, hΘi, fun f => ?_⟩
  rw [hΘe f]
  congr 1
  funext y
  exact mul_comm _ _

end Langlands.HarmonicAnalysis
