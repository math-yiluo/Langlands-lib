import Langlands.HarmonicAnalysis.UnitConjugation.CenterOrthogonalFourier
import Langlands.HarmonicAnalysis.UnitConjugation.RegularOrbitalFourierStabilityStatement
import Langlands.HarmonicAnalysis.UnitConjugation.NilpotentInvariantSpanStatement
import Langlands.HarmonicAnalysis.UnitConjugation.NilpotentOrbitalHomogeneityStatement
import Langlands.HarmonicAnalysis.UnitConjugation.CentralNilpotentDensityStatement

/-!
# Invariant distributions on the orthogonal of the center

Let `A` be a finite-dimensional semisimple algebra over a nonarchimedean local field `F` of
characteristic zero, `z` its center and `V = z^⊥` the trace-form orthogonal of `z`. This module
compares conjugation-invariant distributions on `A` with those on `V`:

* `centerOrthogonalInvariant`: the distributions on `V` invariant under conjugation, and
  `centerOrthogonalNilpotentInvariant`: those among them supported on the nilpotent cone;
* a distribution on `V` gives the distribution `S ∘ restrict` on `A`
  (`isConjugationInvariant_comp_restrict`) and a distribution on `A` gives
  `T ∘ extendTest α` on `V` (`comp_extendTest_mem_centerOrthogonalInvariant`); for `T`
  supported on the nilpotent cone and `α(0) = 1`, `T f = (T ∘ extendTest α)(f|_V)`
  (`apply_eq_comp_extendTest_restrict`), since the nilpotent cone lies in `V`;

and translates three of the inputs of Harish-Chandra's proof of Theorem 3.1 to `V`:

* Lemma 3.16 (`LieAlgebraRegularOrbitalFourierStabilityStatement`) gives the stability of the
  `D₀` of `V` under the Fourier transform of `V` (`CenterOrthogonalVanishing.fourier`), through
  the product formula `restrict_fourier_extendTest`;
* Lemma 3.3 (`LieAlgebraNilpotentInvariantSpanStatement`) gives that the nilpotent invariant
  distributions on `V` form a finite-dimensional space spanned by the transported nilpotent
  orbital distributions (`centerOrthogonalNilpotentInvariant_le_span`,
  `finiteDimensional_centerOrthogonalNilpotentInvariant`);
* Lemma 3.2 (`LieAlgebraNilpotentOrbitalHomogeneityStatement`) gives their homogeneity, with
  degree smaller than `dim V` when `A` is not commutative (`exists_homogeneity_degree`).

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), §3, printed pp. 17–30: Lemmas 3.2, 3.3, 3.11 and 3.16.
-/

noncomputable section

open MeasureTheory Module

namespace Langlands.HarmonicAnalysis.UnitConjugation

open QuotientIntegration

universe u v

section Distributions

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {A : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
  [TopologicalSpace A] [IsTopologicalRing A] [IsModuleTopology F A] [T2Space A]

variable (F A) in
/-- The distributions on `V = z^⊥` invariant under conjugation by `Aˣ`. -/
def centerOrthogonalInvariant : Submodule ℂ (Distribution (centerOrthogonal F A)) where
  carrier := {S | ∀ (u : Aˣ) (β : SchwartzBruhat (centerOrthogonal F A)),
    S (Hecke.TestFunction.pullback (centerOrthogonalConj u) β) = S β}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun hS hS' u β => by
    simp only [LinearMap.add_apply, hS u β, hS' u β]
  smul_mem' := fun c S hS u β => by
    simp only [LinearMap.smul_apply, hS u β]

variable (F A) in
/-- The conjugation-invariant distributions on `V` supported on the nilpotent cone: they
annihilate every test function vanishing at the points of `V` in the closure of the nilpotent
elements of `A`. -/
def centerOrthogonalNilpotentInvariant : Submodule ℂ (Distribution (centerOrthogonal F A)) where
  carrier := {S | S ∈ centerOrthogonalInvariant F A ∧
    ∀ β : SchwartzBruhat (centerOrthogonal F A),
      (∀ Y : centerOrthogonal F A, (Y : A) ∈ closure {X : A | IsNilpotent X} → β Y = 0) →
        S β = 0}
  zero_mem' := ⟨(centerOrthogonalInvariant F A).zero_mem, fun _ _ => rfl⟩
  add_mem' := fun hS hS' => ⟨(centerOrthogonalInvariant F A).add_mem hS.1 hS'.1,
    fun β hβ => by rw [LinearMap.add_apply, hS.2 β hβ, hS'.2 β hβ, add_zero]⟩
  smul_mem' := fun c _ hS => ⟨(centerOrthogonalInvariant F A).smul_mem c hS.1,
    fun β hβ => by rw [LinearMap.smul_apply, hS.2 β hβ, smul_zero]⟩

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem restrict_pullback_conjugation (u : Aˣ) (f : SchwartzBruhat A) :
    restrictCenterOrthogonal (F := F) (Hecke.TestFunction.pullback (conjugationHomeomorph u) f) =
      Hecke.TestFunction.pullback (centerOrthogonalConj u) (restrictCenterOrthogonal f) := rfl

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [T2Space A] in
theorem extendTest_pullback_conj (α : SchwartzBruhat (centerSubmodule F A)) (u : Aˣ)
    (β : SchwartzBruhat (centerOrthogonal F A)) :
    extendTest α (Hecke.TestFunction.pullback (centerOrthogonalConj u) β) =
      Hecke.TestFunction.pullback (conjugationHomeomorph u) (extendTest α β) := by
  ext X
  rw [Hecke.TestFunction.pullback_apply, extendTest_apply, extendTest_apply,
    conjugationHomeomorph_apply, centerDecomposition_symm_conj]
  rfl

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem restrict_extendTest (α : SchwartzBruhat (centerSubmodule F A))
    (β : SchwartzBruhat (centerOrthogonal F A)) :
    restrictCenterOrthogonal (extendTest α β) = α 0 • β := by
  ext Y
  rw [restrictCenterOrthogonal_apply, extendTest_apply_coe]
  rfl

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem isConjugationInvariant_comp_restrict {S : Distribution (centerOrthogonal F A)}
    (hS : S ∈ centerOrthogonalInvariant F A) :
    IsConjugationInvariant (S.comp restrictCenterOrthogonal) := by
  rw [isConjugationInvariant_iff]
  intro u f
  rw [LinearMap.comp_apply, LinearMap.comp_apply, restrict_pullback_conjugation]
  exact hS u _

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [T2Space A] in
theorem comp_extendTest_mem_centerOrthogonalInvariant {T : Distribution A}
    (hT : IsConjugationInvariant T) (α : SchwartzBruhat (centerSubmodule F A)) :
    T.comp (extendTest α) ∈ centerOrthogonalInvariant F A := by
  intro u β
  rw [LinearMap.comp_apply, LinearMap.comp_apply, extendTest_pullback_conj]
  exact (isConjugationInvariant_iff T).1 hT u _

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [T2Space A] in
theorem mem_centerOrthogonal_iff_fst_eq_zero (X : A) :
    X ∈ centerOrthogonal F A ↔ ((centerDecomposition F A).symm X).1 = 0 := by
  constructor
  · intro hX
    rw [show X = ((⟨X, hX⟩ : centerOrthogonal F A) : A) from rfl,
      centerDecomposition_symm_of_mem]
  · intro h
    rw [← centerDecomposition_symm_add (F := F) X, h, Submodule.coe_zero, zero_add]
    exact ((centerDecomposition F A).symm X).2.2

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem isClosed_centerOrthogonal : IsClosed (centerOrthogonal F A : Set A) := by
  have : (centerOrthogonal F A : Set A) = {X | ((centerDecomposition F A).symm X).1 = 0} :=
    Set.ext fun X => mem_centerOrthogonal_iff_fst_eq_zero X
  rw [this]
  exact isClosed_eq (continuous_fst.comp (centerDecomposition F A).symm.continuous)
    continuous_const

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem closure_nilpotent_subset_centerOrthogonal :
    closure {X : A | IsNilpotent X} ⊆ centerOrthogonal F A :=
  closure_minimal (fun _ hX => mem_centerOrthogonal_of_isNilpotent hX)
    isClosed_centerOrthogonal

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- A distribution on `A` supported on the closure of the nilpotent cone is determined by the
restrictions of test functions to `V`. -/
theorem apply_eq_comp_extendTest_restrict {T : Distribution A}
    (hT : ∀ f : SchwartzBruhat A, (∀ X ∈ closure {X : A | IsNilpotent X}, f X = 0) → T f = 0)
    {α : SchwartzBruhat (centerSubmodule F A)} (hα : α 0 = 1) (f : SchwartzBruhat A) :
    T f = (T.comp (extendTest α)) (restrictCenterOrthogonal f) := by
  have h := hT (f - extendTest α (restrictCenterOrthogonal f)) (by
    intro X hX
    have hXV := closure_nilpotent_subset_centerOrthogonal (F := F) hX
    change f X - extendTest α (restrictCenterOrthogonal f) X = 0
    rw [show X = ((⟨X, hXV⟩ : centerOrthogonal F A) : A) from rfl, extendTest_apply_coe, hα,
      one_mul, restrictCenterOrthogonal_apply, sub_self])
  rw [map_sub, sub_eq_zero] at h
  exact h

omit [IsSemisimpleRing A] [T2Space A] in
theorem conjugationSaturation_nilpotent :
    conjugationSaturation {X : A | IsNilpotent X} = {X : A | IsNilpotent X} := by
  refine Set.Subset.antisymm (fun Y hY => ?_) (subset_conjugationSaturation _)
  obtain ⟨u, X, hX, rfl⟩ := mem_conjugationSaturation_iff.1 hY
  exact isNilpotent_of_mem_conjugationSaturation hX
    (mem_conjugationSaturation_iff.2 ⟨u, X, rfl, rfl⟩)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
theorem comp_restrict_mem_invariantSupportedIn {S : Distribution (centerOrthogonal F A)}
    (hS : S ∈ centerOrthogonalNilpotentInvariant F A) :
    S.comp restrictCenterOrthogonal ∈ invariantSupportedIn {X : A | IsNilpotent X} := by
  refine (mem_invariantSupportedIn_iff _ _).2 ⟨isConjugationInvariant_comp_restrict hS.1, ?_⟩
  intro f hf
  rw [conjugationSaturation_nilpotent] at hf
  exact hS.2 _ fun Y hY => hf Y hY

omit [CharZero F] [IsSemisimpleRing A] [T2Space A] in
/-- Characteristic function of a compact open subgroup of the center: a test function `α` on
`z` with `α(0) = 1` and positive integral for every Haar measure. -/
theorem exists_centerBump :
    ∃ α : SchwartzBruhat (centerSubmodule F A), α 0 = 1 ∧
      ∀ [MeasurableSpace (centerSubmodule F A)] [BorelSpace (centerSubmodule F A)]
        (μ : Measure (centerSubmodule F A)) [μ.IsAddHaarMeasure], (∫ Z, α Z ∂μ) ≠ 0 := by
  obtain ⟨K, hKc, hKo, -⟩ :=
    CompactOpenExhaustion.exists_superset (∅ : Set (centerSubmodule F A)) isCompact_empty
  have hKcl : IsClopen (K : Set (centerSubmodule F A)) :=
    ⟨AddSubgroup.isClosed_of_isOpen K hKo, hKo⟩
  refine ⟨Hecke.TestFunction.characteristic hKcl hKc, ?_, ?_⟩
  · rw [Hecke.TestFunction.characteristic_apply, Set.indicator_of_mem K.zero_mem]
  · intro _ _ μ _
    simp only [Hecke.TestFunction.characteristic_apply]
    rw [integral_indicator_const _ hKo.measurableSet]
    have hpos : 0 < μ (K : Set (centerSubmodule F A)) := hKo.measure_pos μ ⟨0, K.zero_mem⟩
    have hfin : μ (K : Set (centerSubmodule F A)) < ⊤ := hKc.measure_lt_top
    have : 0 < μ.real (K : Set (centerSubmodule F A)) := ENNReal.toReal_pos hpos.ne' hfin.ne
    rw [Complex.real_smul, mul_one]
    exact_mod_cast this.ne'

end Distributions

section Inputs

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {A : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
  [TopologicalSpace A] [IsTopologicalRing A] [IsModuleTopology F A] [T2Space A]
  [MeasurableSpace Aˣ] [BorelSpace Aˣ]

/-- **Lemma 3.16 on `V`.** The `D₀` of `V` is stable under the Fourier transform of `V`. -/
theorem CenterOrthogonalVanishing.fourier
    (hP1 : LieAlgebraRegularOrbitalFourierStabilityStatement.{u, v})
    [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace (centerSubmodule F A)] [BorelSpace (centerSubmodule F A)]
    [MeasurableSpace (centerOrthogonal F A)] [BorelSpace (centerOrthogonal F A)]
    (ψ : UnitaryAdditiveCharacter F) (μz : Measure (centerSubmodule F A)) [μz.IsAddHaarMeasure]
    (μV : AdditiveHaarMeasure (centerOrthogonal F A)) {α : SchwartzBruhat (centerSubmodule F A)}
    (hα : (∫ Z, α Z ∂μz) ≠ 0) {β : SchwartzBruhat (centerOrthogonal F A)}
    (hβ : CenterOrthogonalVanishing F A β) :
    CenterOrthogonalVanishing F A (centerOrthogonalFourier ψ μV β) := by
  have h1 := hP1 F A ψ (traceFormPairing F A) isInvariantPairing_traceFormPairing
    (productHaar μz μV) (extendTest α β) (hβ.regularOrbitalVanishing α)
  have h2 := RegularOrbitalVanishing.centerOrthogonalVanishing_restrict h1
  rw [restrict_fourier_extendTest] at h2
  have h3 := h2.smul (∫ Z, α Z ∂μz)⁻¹
  rwa [inv_smul_smul₀ hα] at h3

/-- **Lemma 3.3 on `V`.** The nilpotent invariant distributions on `V` lie in the span of the
nilpotent orbital distributions composed with `extendTest α`. -/
theorem centerOrthogonalNilpotentInvariant_le_span
    (hP2a : LieAlgebraNilpotentInvariantSpanStatement.{u, v})
    {α : SchwartzBruhat (centerSubmodule F A)} (hα : α 0 = 1) :
    centerOrthogonalNilpotentInvariant F A ≤
      Submodule.span ℂ ((fun T : Distribution A => T.comp (extendTest α)) '' nilpotentOrbitals A) := by
  intro S hS
  have hT := (hP2a F A).2 (comp_restrict_mem_invariantSupportedIn hS)
  have h := Submodule.apply_mem_span_image_of_mem_span
    ((extendTest α).dualMap : Distribution A →ₗ[ℂ] Distribution (centerOrthogonal F A)) hT
  have hS' : (extendTest α).dualMap (S.comp restrictCenterOrthogonal) = S := by
    ext β
    change S (restrictCenterOrthogonal (extendTest α β)) = S β
    rw [restrict_extendTest, hα, one_smul]
  rw [hS'] at h
  exact h

theorem finiteDimensional_centerOrthogonalNilpotentInvariant
    (hP2a : LieAlgebraNilpotentInvariantSpanStatement.{u, v}) :
    FiniteDimensional ℂ (centerOrthogonalNilpotentInvariant F A) := by
  have hfin := (hP2a F A).1
  obtain ⟨α, hα, -⟩ := exists_centerBump (F := F) (A := A)
  let φ : centerOrthogonalNilpotentInvariant F A →ₗ[ℂ]
      invariantSupportedIn {X : A | IsNilpotent X} :=
    { toFun := fun S => ⟨S.1.comp restrictCenterOrthogonal,
        comp_restrict_mem_invariantSupportedIn S.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective φ := by
    intro S S' h
    apply Subtype.ext
    ext β
    have h' := congrArg (fun T : invariantSupportedIn {X : A | IsNilpotent X} =>
      (T : Distribution A) (extendTest α β)) h
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, restrict_extendTest,
      hα, one_smul] at h'
    exact h'

  exact Module.Finite.of_injective φ hinj

omit [IsSemisimpleRing A] [IsTopologicalRing A] [T2Space A] [MeasurableSpace Aˣ] [BorelSpace Aˣ] in
/-- The values of an orbital distribution depend only on the values of the test function on the
orbit. -/
theorem orbitalDistribution_congr {X₀ : A}
    [MeasurableSpace (LeftQuotient (conjugationCentralizer X₀))]
    (ν : Measure (LeftQuotient (conjugationCentralizer X₀)))
    (hν : OrbitalIntegralConverges X₀ ν) {f f' : SchwartzBruhat A}
    (h : ∀ g : Aˣ, f (((g⁻¹ : Aˣ) : A) * X₀ * (g : A)) = f' (((g⁻¹ : Aˣ) : A) * X₀ * (g : A))) :
    orbitalDistribution X₀ ν hν f = orbitalDistribution X₀ ν hν f' := by
  rw [orbitalDistribution_apply, orbitalDistribution_apply]
  congr 1
  funext q
  induction q using Quotient.inductionOn with
  | h g => exact h g

omit [T2Space A] in
/-- **Lemma 3.2 on `V`.** When `A` is not commutative, a nilpotent orbital distribution composed
with `extendTest α` is homogeneous of a degree smaller than `dim V`. -/
theorem exists_homogeneity_degree
    (hP2b : LieAlgebraNilpotentOrbitalHomogeneityStatement.{u, v})
    (hA : Subalgebra.center F A ≠ ⊤) (α : SchwartzBruhat (centerSubmodule F A)) {R : Distribution A}
    (hR : R ∈ nilpotentOrbitals A) :
    ∃ d : ℕ, d < finrank F (centerOrthogonal F A) ∧
      ∀ (t : Fˣ) (β : SchwartzBruhat (centerOrthogonal F A)),
        (R.comp (extendTest α)) (scalarDilation (t ^ 2) β) =
          ((distribHaarChar F t : ℝ) : ℂ) ^ d * (R.comp (extendTest α)) β := by
  obtain ⟨N, hN, _, _, μG, _, μH, _, _, ν, hcompat, hconv, rfl⟩ := hR
  refine ⟨finrank F A - finrank F (Subalgebra.centralizer F ({N} : Set A)), ?_, ?_⟩
  · have h1 := finrank_center_lt_finrank_centralizer hA hN
    have h2 := Submodule.finrank_add_eq_of_isCompl
      (isCompl_center_centerOrthogonal (F := F) (A := A))
    have h3 : finrank F (Subalgebra.centralizer F ({N} : Set A)) ≤ finrank F A :=
      Submodule.finrank_le (Subalgebra.centralizer F ({N} : Set A)).toSubmodule
    have h4 : finrank F (Subalgebra.center F A) =
        finrank F (Subalgebra.center F A).toSubmodule := rfl
    omega
  · intro t β
    have hP := hP2b F A N hN μG μH ν hcompat hconv t (extendTest α β)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hP]
    apply orbitalDistribution_congr
    intro g
    have hmem : ((g⁻¹ : Aˣ) : A) * N * (g : A) ∈ centerOrthogonal F A := by
      apply mem_centerOrthogonal_of_isNilpotent
      apply isNilpotent_of_mem_conjugationSaturation hN
      exact mem_conjugationSaturation_iff.2 ⟨g⁻¹, N, rfl, by rw [inv_inv]⟩
    set Y : centerOrthogonal F A := ⟨_, hmem⟩
    change extendTest α (scalarDilation (t ^ 2) β) (Y : A) =
      scalarDilation (t ^ 2) (extendTest α β) (Y : A)
    rw [scalarDilation_extendTest, extendTest_apply_coe, extendTest_apply_coe,
      scalarDilation_apply, scalarDilation_apply, smul_zero]

end Inputs

end Langlands.HarmonicAnalysis.UnitConjugation
