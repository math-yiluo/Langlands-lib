import Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalVanishing
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Vanishing of orbital integrals: transport between orbits

Let `A` be a topological ring, the Lie algebra of its unit group `Aˣ`. For `X : A` and a
Schwartz–Bruhat function `f`, `OrbitalVanishingAt X f` says that every orbital integral
`∫_{C \ Aˣ} f(g⁻¹ X g) dν` of `f` at `X` vanishes, for every compatible quotient measure `ν`
with absolutely convergent orbital integrals; `RegularOrbitalVanishing F A f` is this condition
at every regular `X` (`regularOrbitalVanishing_iff`).

If a homeomorphism `φ` of `A` carries the orbit map of `X` to that of `X'`,
`φ(g⁻¹ X g) = g⁻¹ X' g` for all units `g`, then `X` and `X'` have the same centralizer and the
orbital integrals of `f` at `X'` are those of `f ∘ φ` at `X`
(`orbitalVanishingAt_iff_of_homeomorph`). Two instances:

* a translation by a central element `Z` (`orbitalVanishingAt_add_central_iff`), with
  `X + Z` regular exactly when `X` is (`add_central_mem_regularSet_iff`);
* a dilation by a unit `s` of the field (`orbitalVanishingAt_smul_iff`), with `s • X` regular
  exactly when `X` is (`smul_mem_regularSet_iff`).

Consequently `D₀` is stable under translations by central elements
(`RegularOrbitalVanishing.translate_central`) and under the dilations `f ↦ f_s`
(`RegularOrbitalVanishing.scalarDilation`). The orbital integrals at `X` depend only on the
values of `f` on the orbit of `X` (`orbitalVanishingAt_congr`). This is the part of
Harish-Chandra's Lemma 3.16 on dilations: Harish-Chandra, *Admissible invariant distributions on
reductive p-adic groups* (notes by DeBacker and Sally, 1999), §3.5, printed p. 28.
-/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.UnitConjugation

open QuotientIntegration

universe u v

section Translation

variable {M : Type v} [AddGroup M] [TopologicalSpace M] [ContinuousAdd M]

/-- Translation of test functions by `Z`: `(translateTest Z f)(Y) = f(Y + Z)`. -/
def translateTest (Z : M) : SchwartzBruhat M ≃ₗ[ℂ] SchwartzBruhat M :=
  Hecke.TestFunction.pullback (Homeomorph.addRight Z)

@[simp]
theorem translateTest_apply (Z Y : M) (f : SchwartzBruhat M) :
    translateTest Z f Y = f (Y + Z) := rfl

end Translation

section Transport

variable {A : Type v} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
  [MeasurableSpace Aˣ] [BorelSpace Aˣ]

/-- Every orbital integral of `f` at `X` vanishes: for every Borel σ-algebra on the coset space
of the centralizer `C` of `X`, every Haar measure on `Aˣ`, every right-invariant Haar measure
on `C`, every compatible quotient measure `ν` and every proof of absolute convergence,
`∫_{C \ Aˣ} f(g⁻¹ X g) dν = 0`. -/
def OrbitalVanishingAt (X : A) (f : SchwartzBruhat A) : Prop :=
  ∀ [MeasurableSpace (LeftQuotient (conjugationCentralizer X))]
    [BorelSpace (LeftQuotient (conjugationCentralizer X))]
    (μG : Measure Aˣ) [μG.IsHaarMeasure]
    (μH : Measure (conjugationCentralizer X)) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (ν : Measure (LeftQuotient (conjugationCentralizer X))),
    IsCompatible (conjugationCentralizer X) μG μH ν →
    ∀ hconv : OrbitalIntegralConverges X ν, orbitalDistribution X ν hconv f = 0

theorem regularOrbitalVanishing_iff (F : Type u) [Field F] [Algebra F A] [FiniteDimensional F A]
    (f : SchwartzBruhat A) :
    RegularOrbitalVanishing F A f ↔ ∀ X ∈ regularSet F A, OrbitalVanishingAt X f :=
  Iff.rfl

/-- Orbital vanishing for an orbit map `p : Aˣ → A` constant on the cosets of a subgroup `H`,
stated uniformly in `H`. -/
def OrbitMapVanishing (H : Subgroup Aˣ) (p : Aˣ → A)
    (hp : ∀ (h : H) (g : Aˣ), p (h.val * g) = p g) (f : SchwartzBruhat A) : Prop :=
  ∀ [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
    (μG : Measure Aˣ) [μG.IsHaarMeasure]
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (ν : Measure (LeftQuotient H)),
    IsCompatible H μG μH ν →
    (∀ f' : SchwartzBruhat A,
      Integrable (descend H (fun g => f' (p g)) (fun h g => by rw [hp h g])) ν) →
    ∫ q, descend H (fun g => f (p g)) (fun h g => by rw [hp h g]) q ∂ν = 0

omit [TopologicalSpace A] [IsTopologicalRing A] [MeasurableSpace Aˣ] [BorelSpace Aˣ] in
/-- The orbit map `g ↦ g⁻¹ X g` is constant on the cosets of the centralizer of `X`. -/
theorem orbitMap_left_mul (X : A) (h : conjugationCentralizer X) (g : Aˣ) :
    (((h.val * g)⁻¹ : Aˣ) : A) * X * ((h.val * g : Aˣ) : A) = ((g⁻¹ : Aˣ) : A) * X * (g : A) := by
  have hh := (mem_conjugationCentralizer_iff X h.val).1 h.property
  have hX : ((h.val⁻¹ : Aˣ) : A) * X * (h.val : A) = X := by
    rw [mul_assoc, ← hh, ← mul_assoc, Units.inv_mul, one_mul]
  simp only [mul_inv_rev, Units.val_mul]
  calc ((g⁻¹ : Aˣ) : A) * ((h.val⁻¹ : Aˣ) : A) * X * ((h.val : A) * (g : A))
      = ((g⁻¹ : Aˣ) : A) * (((h.val⁻¹ : Aˣ) : A) * X * (h.val : A)) * (g : A) := by
        simp only [mul_assoc]
    _ = ((g⁻¹ : Aˣ) : A) * X * (g : A) := by rw [hX]

theorem orbitalVanishingAt_iff_orbitMapVanishing (X : A) (f : SchwartzBruhat A) :
    OrbitalVanishingAt X f ↔
      OrbitMapVanishing (conjugationCentralizer X)
        (fun g => ((g⁻¹ : Aˣ) : A) * X * (g : A)) (orbitMap_left_mul X) f :=
  Iff.rfl

theorem orbitMapVanishing_congr_subgroup {H H' : Subgroup Aˣ} (e : H = H') (p : Aˣ → A)
    (hp : ∀ (h : H) (g : Aˣ), p (h.val * g) = p g)
    (hp' : ∀ (h : H') (g : Aˣ), p (h.val * g) = p g) (f : SchwartzBruhat A) :
    OrbitMapVanishing H p hp f ↔ OrbitMapVanishing H' p hp' f := by
  subst e
  rfl

theorem orbitMapVanishing_congr_fun {H : Subgroup Aˣ} {p p' : Aˣ → A} (e : p = p')
    (hp : ∀ (h : H) (g : Aˣ), p (h.val * g) = p g)
    (hp' : ∀ (h : H) (g : Aˣ), p' (h.val * g) = p' g) (f : SchwartzBruhat A) :
    OrbitMapVanishing H p hp f ↔ OrbitMapVanishing H p' hp' f := by
  subst e
  rfl

/-- Composing the orbit map with a homeomorphism `φ` is the same as pulling the test functions
back along `φ`. -/
theorem orbitMapVanishing_comp_homeomorph (H : Subgroup Aˣ) (p : Aˣ → A)
    (hp : ∀ (h : H) (g : Aˣ), p (h.val * g) = p g) (φ : A ≃ₜ A) (f : SchwartzBruhat A) :
    OrbitMapVanishing H (fun g => φ (p g)) (fun h g => by rw [hp h g]) f ↔
      OrbitMapVanishing H p hp (Hecke.TestFunction.pullback φ f) := by
  constructor
  · intro hf _ _ μG _ μH _ _ ν hν hconv
    exact hf μG μH ν hν fun f' => by
      have := hconv (Hecke.TestFunction.pullback φ f')
      exact this
  · intro hf _ _ μG _ μH _ _ ν hν hconv
    refine hf μG μH ν hν fun f' => ?_
    have h := hconv (Hecke.TestFunction.pullback φ.symm f')
    convert h using 3
    · simp only [Hecke.TestFunction.pullback_apply, Homeomorph.symm_apply_apply]

/-- **Transport of orbital vanishing.** If a homeomorphism `φ` of `A` satisfies
`φ(g⁻¹ X g) = g⁻¹ X' g` for every unit `g`, the orbital integrals of `f` at `X'` vanish exactly
when those of `f ∘ φ` at `X` do. -/
theorem orbitalVanishingAt_iff_of_homeomorph {X X' : A} (φ : A ≃ₜ A)
    (hφ : ∀ g : Aˣ, φ (((g⁻¹ : Aˣ) : A) * X * (g : A)) = ((g⁻¹ : Aˣ) : A) * X' * (g : A))
    (f : SchwartzBruhat A) :
    OrbitalVanishingAt X' f ↔ OrbitalVanishingAt X (Hecke.TestFunction.pullback φ f) := by
  have hX' : X' = φ X := by simpa using (hφ 1).symm
  have hC : conjugationCentralizer X' = conjugationCentralizer X := by
    ext u
    rw [mem_conjugationCentralizer_iff_smul, mem_conjugationCentralizer_iff_smul,
      ConjAct.units_smul_def, ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
    have h := hφ u⁻¹
    rw [inv_inv] at h
    rw [← h, hX']
    exact φ.injective.eq_iff
  rw [orbitalVanishingAt_iff_orbitMapVanishing, orbitalVanishingAt_iff_orbitMapVanishing]
  have hinv : ∀ (h : conjugationCentralizer X) (g : Aˣ),
      (((h.val * g)⁻¹ : Aˣ) : A) * X' * ((h.val * g : Aˣ) : A) =
        ((g⁻¹ : Aˣ) : A) * X' * (g : A) := fun h g => by
    rw [← hφ, ← hφ, orbitMap_left_mul X h g]
  rw [orbitMapVanishing_congr_subgroup hC _ _ hinv, ← orbitMapVanishing_comp_homeomorph]
  exact orbitMapVanishing_congr_fun (funext fun g => (hφ g).symm) _ _ f

/-- The orbital integrals at `X` depend only on the values of `f` on the orbit of `X`. -/
theorem orbitalVanishingAt_congr {X : A} {f f' : SchwartzBruhat A}
    (h : ∀ g : Aˣ, f (((g⁻¹ : Aˣ) : A) * X * (g : A)) = f' (((g⁻¹ : Aˣ) : A) * X * (g : A))) :
    OrbitalVanishingAt X f ↔ OrbitalVanishingAt X f' := by
  have hI : orbitalIntegrand X f = orbitalIntegrand X f' := by
    funext q
    induction q using Quotient.inductionOn with
    | h g => exact h g
  constructor
  · intro hf _ _ μG _ μH _ _ ν hν hconv
    have := hf μG μH ν hν hconv
    rw [orbitalDistribution_apply] at this ⊢
    rwa [← hI]
  · intro hf _ _ μG _ μH _ _ ν hν hconv
    have := hf μG μH ν hν hconv
    rw [orbitalDistribution_apply] at this ⊢
    rwa [hI]

theorem orbitalVanishingAt_zero (X : A) : OrbitalVanishingAt X 0 := by
  intro _ _ μG _ μH _ _ ν _ hconv
  exact map_zero _

theorem OrbitalVanishingAt.add {X : A} {f f' : SchwartzBruhat A} (hf : OrbitalVanishingAt X f)
    (hf' : OrbitalVanishingAt X f') : OrbitalVanishingAt X (f + f') := by
  intro _ _ μG _ μH _ _ ν hν hconv
  rw [map_add, hf μG μH ν hν hconv, hf' μG μH ν hν hconv, add_zero]

theorem OrbitalVanishingAt.smul {X : A} {f : SchwartzBruhat A} (hf : OrbitalVanishingAt X f)
    (c : ℂ) : OrbitalVanishingAt X (c • f) := by
  intro _ _ μG _ μH _ _ ν hν hconv
  rw [map_smul, hf μG μH ν hν hconv, smul_zero]

/-- Orbital integrals at `X + Z`, for central `Z`, are those of the translate at `X`. -/
theorem orbitalVanishingAt_add_central_iff {Z : A} (hZ : ∀ Y : A, Y * Z = Z * Y) (X : A)
    (f : SchwartzBruhat A) :
    OrbitalVanishingAt (X + Z) f ↔ OrbitalVanishingAt X (translateTest Z f) := by
  refine orbitalVanishingAt_iff_of_homeomorph (Homeomorph.addRight Z) (fun g => ?_) f
  change ((g⁻¹ : Aˣ) : A) * X * (g : A) + Z = ((g⁻¹ : Aˣ) : A) * (X + Z) * (g : A)
  rw [mul_add, add_mul, mul_assoc ((g⁻¹ : Aˣ) : A) Z, ← hZ (g : A), ← mul_assoc,
    Units.inv_mul, one_mul]

end Transport

section Field

variable {F : Type u} [Field F] {A : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A]

omit [FiniteDimensional F A] in
theorem adjointEndomorphism_add_central {Z : A} (hZ : ∀ Y : A, Y * Z = Z * Y) (X : A) :
    adjointEndomorphism F (X + Z) = adjointEndomorphism F X := by
  ext Y
  simp only [adjointEndomorphism_apply, add_mul, mul_add, hZ Y]
  abel

theorem add_central_mem_regularSet_iff {Z : A} (hZ : ∀ Y : A, Y * Z = Z * Y) (X : A) :
    X + Z ∈ regularSet F A ↔ X ∈ regularSet F A := by
  simp only [regularSet, adjointEta, Set.mem_ofPred_eq, adjointEndomorphism_add_central hZ]

omit [FiniteDimensional F A] in
theorem adjointEndomorphism_smul (s : F) (X : A) :
    adjointEndomorphism F (s • X) = s • adjointEndomorphism F X := by
  ext Y
  simp only [adjointEndomorphism_apply, LinearMap.smul_apply, smul_mul_assoc, mul_smul_comm,
    smul_sub]

/-- Scaling an endomorphism by a nonzero scalar does not change the multiplicity of the root
`0` of its characteristic polynomial. -/
theorem natTrailingDegree_charpoly_smul {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (φ : Module.End F V) {s : F} (hs : s ≠ 0) :
    (s • φ).charpoly.natTrailingDegree = φ.charpoly.natTrailingDegree := by
  have h : (s • φ).maxGenEigenspace 0 = φ.maxGenEigenspace 0 := by
    ext y
    simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero, smul_pow,
      LinearMap.smul_apply, smul_eq_zero, pow_eq_zero_iff', hs, false_and, false_or]
  rw [← LinearMap.finrank_maxGenEigenspace_zero_eq, ← LinearMap.finrank_maxGenEigenspace_zero_eq, h]

theorem smul_mem_regularSet_iff {s : F} (hs : s ≠ 0) (X : A) :
    s • X ∈ regularSet F A ↔ X ∈ regularSet F A := by
  rw [mem_regularSet_iff, mem_regularSet_iff, adjointEndomorphism_smul,
    natTrailingDegree_charpoly_smul _ hs]

variable [TopologicalSpace A] [IsTopologicalRing A] [MeasurableSpace Aˣ] [BorelSpace Aˣ]
  [TopologicalSpace F] [ContinuousSMul F A]

omit [FiniteDimensional F A] [TopologicalSpace F] [ContinuousSMul F A] in
/-- Orbital integrals at `s • X` are those of the test function `f(s ·)` at `X`. -/
theorem orbitalVanishingAt_smul_iff (s : Fˣ) (X : A) (f : SchwartzBruhat A) :
    OrbitalVanishingAt ((s : F) • X) f ↔
      OrbitalVanishingAt X (Hecke.TestFunction.pullback (Homeomorph.smul s) f) := by
  refine orbitalVanishingAt_iff_of_homeomorph (Homeomorph.smul s) (fun g => ?_) f
  change (s : F) • (((g⁻¹ : Aˣ) : A) * X * (g : A)) = ((g⁻¹ : Aˣ) : A) * ((s : F) • X) * (g : A)
  rw [mul_smul_comm, smul_mul_assoc]

omit [TopologicalSpace F] [ContinuousSMul F A] in
/-- `D₀` is stable under translation by central elements. -/
theorem RegularOrbitalVanishing.translate_central {f : SchwartzBruhat A}
    (hf : RegularOrbitalVanishing F A f) {Z : A} (hZ : ∀ Y : A, Y * Z = Z * Y) :
    RegularOrbitalVanishing F A (translateTest Z f) := by
  intro X hX
  exact (orbitalVanishingAt_add_central_iff hZ X f).1
    (hf (X + Z) ((add_central_mem_regularSet_iff hZ X).2 hX))

omit [TopologicalSpace F] [ContinuousSMul F A] in
/-- `D₀` is stable under the dilations `f ↦ f_s`, `f_s(X) = f(s⁻¹ X)`. -/
theorem RegularOrbitalVanishing.scalarDilation {f : SchwartzBruhat A}
    (hf : RegularOrbitalVanishing F A f) (s : Fˣ) :
    RegularOrbitalVanishing F A (scalarDilation s f) := by
  intro X hX
  exact (orbitalVanishingAt_smul_iff s⁻¹ X f).1
    (hf _ ((smul_mem_regularSet_iff (Units.ne_zero _) X).2 hX))

end Field

end Langlands.HarmonicAnalysis.UnitConjugation
