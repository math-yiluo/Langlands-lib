import Langlands.HarmonicAnalysis.UnitConjugation.CenterOrthogonalDistributions
import Langlands.HarmonicAnalysis.AdditiveCharacterExists
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalModulusDeterminant

/-!
# Harish-Chandra's Theorem 3.1 from Lemmas 3.2, 3.3, 3.12 and 3.16

For the Lie algebra `A` of the unit group of a finite-dimensional semisimple algebra over a
nonarchimedean local field `F` of characteristic zero, this module derives Harish-Chandra's
Theorem 3.1 (`LieAlgebraRegularOrbitalDensityStatement`) from four of his lemmas:

* Lemma 3.16, Fourier part: `LieAlgebraRegularOrbitalFourierStabilityStatement`;
* Lemma 3.3: `LieAlgebraNilpotentInvariantSpanStatement`;
* Lemma 3.2: `LieAlgebraNilpotentOrbitalHomogeneityStatement`;
* Lemma 3.12 with central translates, under the induction hypothesis:
  `LieAlgebraCentralNilpotentDensityStatement`.

`lieAlgebraRegularOrbitalDensityReduction` proves the implication
`LieAlgebraRegularOrbitalDensityReductionStatement`. The four inputs are not proved here.
-/

noncomputable section

open MeasureTheory Module Filter Topology

namespace Langlands.HarmonicAnalysis

open UnitConjugation QuotientIntegration

/-- **Harish-Chandra's Theorem 3.1 from four of its lemmas**: for the unit groups of
finite-dimensional semisimple algebras over nonarchimedean local fields of characteristic zero,
Lemma 3.16 (Fourier stability of `D₀`), Lemma 3.3 (`J(N)` is finite-dimensional and spanned by
nilpotent orbital integrals), Lemma 3.2 (homogeneity of nilpotent orbital integrals) and
Lemma 3.12 with central translates (under the induction hypothesis) imply Theorem 3.1. -/
def LieAlgebraRegularOrbitalDensityReductionStatement.{u', v'} : Prop :=
  LieAlgebraRegularOrbitalFourierStabilityStatement.{u', v'} →
    LieAlgebraNilpotentInvariantSpanStatement.{u', v'} →
      LieAlgebraNilpotentOrbitalHomogeneityStatement.{u', v'} →
        LieAlgebraCentralNilpotentDensityStatement.{u', v'} →
          LieAlgebraRegularOrbitalDensityStatement.{u', v'}

namespace RegularOrbitalDensityReduction

universe u v

/-! ### Two elementary facts -/

/-- A complex number that is, for every `m`, a finite combination of the `m`-th powers of
numbers of absolute value `< 1` is `0`: here those powers are `(x⁻¹)^{(n - d - e i) m}`. -/
theorem eq_zero_of_forall_scaling {ι : Type*} [Fintype ι] {x : ℝ} (hx : 1 < x) {n d : ℕ}
    {e : ι → ℕ} (he : ∀ i, d + e i < n) {L : ℂ} {c : ι → ℂ}
    (h : ∀ m : ℕ, ((x ^ m : ℝ) : ℂ) ^ n * (((x ^ m : ℝ) : ℂ)⁻¹) ^ d * L =
      ∑ i, c i * ((x ^ m : ℝ) : ℂ) ^ e i) : L = 0 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have key : ∀ m : ℕ, L = ∑ i, c i * ((((x⁻¹ : ℝ) : ℂ) ^ (n - d - e i)) ^ m) := by
    intro m
    have hz : ((x ^ m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hx0 m).ne'
    have hzinv : ((x⁻¹ : ℝ) : ℂ) ^ m = (((x ^ m : ℝ) : ℂ))⁻¹ := by
      push_cast
      rw [inv_pow]
    have h1 := h m
    set z : ℂ := ((x ^ m : ℝ) : ℂ) with hzdef
    have inv_cancel : ∀ k : ℕ, z ^ k * z⁻¹ ^ k = 1 := fun k => by
      rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hz)]
    calc L = (z ^ d * z⁻¹ ^ d) * (z ^ n * z⁻¹ ^ n) * L := by
          rw [inv_cancel, inv_cancel, one_mul, one_mul]
      _ = (z ^ d * z⁻¹ ^ n) * (z ^ n * z⁻¹ ^ d * L) := by ring
      _ = ∑ i, c i * (z ^ d * z⁻¹ ^ n * z ^ e i) := by
          rw [h1, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = ∑ i, c i * ((((x⁻¹ : ℝ) : ℂ) ^ (n - d - e i)) ^ m) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 1
          rw [pow_right_comm, hzinv]
          obtain ⟨k, hk⟩ : ∃ k, n = d + e i + k := ⟨n - (d + e i), by have := he i; omega⟩
          rw [hk, show d + e i + k - d - e i = k by omega, pow_add, pow_add]
          calc z ^ d * (z⁻¹ ^ d * z⁻¹ ^ e i * z⁻¹ ^ k) * z ^ e i
              = (z ^ d * z⁻¹ ^ d) * (z ^ e i * z⁻¹ ^ e i) * z⁻¹ ^ k := by ring
            _ = z⁻¹ ^ k := by rw [inv_cancel, inv_cancel, one_mul, one_mul]
  have hlim : Tendsto (fun m : ℕ => ∑ i, c i * ((((x⁻¹ : ℝ) : ℂ) ^ (n - d - e i)) ^ m))
      atTop (𝓝 0) := by
    have : (0 : ℂ) = ∑ i : ι, c i * 0 := by simp
    rw [this]
    refine tendsto_finsetSum _ fun i _ => Tendsto.const_mul _ ?_
    apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hx0)]
    have hk : 1 ≤ n - d - e i := by have := he i; omega
    calc x⁻¹ ^ (n - d - e i) ≤ x⁻¹ ^ 1 :=
          pow_le_pow_of_le_one (inv_pos.2 hx0).le (inv_lt_one_of_one_lt₀ hx).le hk
      _ < 1 := by rw [pow_one]; exact inv_lt_one_of_one_lt₀ hx
  have hconst : Tendsto (fun _ : ℕ => L) atTop (𝓝 0) := by
    have hfun : (fun _ : ℕ => L) =
        fun m : ℕ => ∑ i, c i * ((((x⁻¹ : ℝ) : ℂ) ^ (n - d - e i)) ^ m) := funext key
    rw [hfun]
    exact hlim
  exact tendsto_nhds_unique tendsto_const_nhds hconst

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The modulus of `F` takes a value larger than `1`, at the inverse of a uniformizer. -/
theorem exists_one_lt_distribHaarChar : ∃ t : Fˣ, 1 < (distribHaarChar F t : ℝ) := by
  refine ⟨(Units.mk0 (LocalField.uniformizer F) (LocalField.uniformizer_ne_zero F))⁻¹, ?_⟩
  rw [map_inv, NNReal.coe_inv,
    HarishChandraSchwartz.distribHaarChar_eq_residueNormalizedAbsoluteValue, Units.val_mk0,
    LocalField.residueNormalizedAbsoluteValue_uniformizer, zpow_neg_one, inv_inv]
  exact_mod_cast LocalField.residueCardinality_gt_one F

section Main

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {A : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
  [TopologicalSpace A] [IsTopologicalRing A] [IsModuleTopology F A] [T2Space A]
  [MeasurableSpace Aˣ] [BorelSpace Aˣ]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
  [FiniteDimensional F A] [IsSemisimpleRing A] [IsModuleTopology F A] [T2Space A]
  [MeasurableSpace Aˣ] [BorelSpace Aˣ] in
/-- Translation by a central element commutes with conjugation. -/
theorem translateTest_pullback_conjugation {Z : A} (hZ : Z ∈ Subalgebra.center F A) (u : Aˣ)
    (g : SchwartzBruhat A) :
    translateTest Z (Hecke.TestFunction.pullback (conjugationHomeomorph u) g) =
      Hecke.TestFunction.pullback (conjugationHomeomorph u) (translateTest Z g) := by
  ext X
  simp only [translateTest_apply, Hecke.TestFunction.pullback_apply, conjugationHomeomorph_apply]
  rw [mul_add, add_mul, (Subalgebra.mem_center_iff (R := F)).1 hZ (u : A), mul_assoc Z,
    Units.mul_inv, mul_one]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [MeasurableSpace Aˣ] [BorelSpace Aˣ] in
/-- An invariant distribution supported on a central translate `Z + N` of the nilpotent cone is
`f ↦ S₂((f(· + Z))|_V)` for a nilpotent invariant distribution `S₂` on `V`. -/
theorem exists_centerOrthogonalNilpotentInvariant_of_translate
    {α : SchwartzBruhat (centerSubmodule F A)} (hα : α 0 = 1) {Z : A}
    (hZ : Z ∈ Subalgebra.center F A) {S : Distribution A}
    (hS : S ∈ invariantSupportedIn {X : A | IsNilpotent (X - Z)}) :
    ∃ S₂ ∈ centerOrthogonalNilpotentInvariant F A, ∀ f : SchwartzBruhat A,
      S f = S₂ (restrictCenterOrthogonal (translateTest Z f)) := by
  obtain ⟨hSinv, hSsupp⟩ := (mem_invariantSupportedIn_iff _ _).1 hS
  have hnegZ : -Z ∈ Subalgebra.center F A := Subalgebra.neg_mem _ hZ
  let S₁ : Distribution A := S.comp (translateTest (-Z)).toLinearMap
  have hS₁inv : IsConjugationInvariant S₁ := by
    rw [isConjugationInvariant_iff]
    intro u g
    change S (translateTest (-Z) _) = S (translateTest (-Z) g)
    rw [translateTest_pullback_conjugation hnegZ]
    exact (isConjugationInvariant_iff S).1 hSinv u _
  have hS₁supp : ∀ g : SchwartzBruhat A,
      (∀ X ∈ closure {X : A | IsNilpotent X}, g X = 0) → S₁ g = 0 := by
    intro g hg
    apply hSsupp
    intro Y hY
    have hsub : conjugationSaturation {X : A | IsNilpotent (X - Z)} ⊆
        (Homeomorph.addRight (-Z)) ⁻¹' {X : A | IsNilpotent X} := by
      intro W hW
      obtain ⟨u, X, hX, rfl⟩ := mem_conjugationSaturation_iff.1 hW
      have hZu : (u : A) * Z * ((u⁻¹ : Aˣ) : A) = Z := by
        rw [(Subalgebra.mem_center_iff (R := F)).1 hZ (u : A), mul_assoc, Units.mul_inv, mul_one]
      change IsNilpotent ((u : A) * X * ((u⁻¹ : Aˣ) : A) + -Z)
      rw [← sub_eq_add_neg, ← hZu, ← sub_mul, ← mul_sub]
      exact isNilpotent_of_mem_conjugationSaturation hX
        (mem_conjugationSaturation_iff.2 ⟨u, X - Z, rfl, rfl⟩)
    have hY' := closure_mono hsub hY
    rw [← Homeomorph.preimage_closure] at hY'
    change translateTest (-Z) g Y = 0
    rw [translateTest_apply]
    exact hg _ hY'
  refine ⟨S₁.comp (extendTest α),
    ⟨comp_extendTest_mem_centerOrthogonalInvariant hS₁inv α, ?_⟩, ?_⟩
  · intro β hβ
    apply hS₁supp
    intro X hX
    have hXV := closure_nilpotent_subset_centerOrthogonal (F := F) hX
    rw [show X = ((⟨X, hXV⟩ : centerOrthogonal F A) : A) from rfl, extendTest_apply_coe,
      hβ _ hX, mul_zero]
  · intro f
    have h1 : S f = S₁ (translateTest Z f) := by
      change S f = S (translateTest (-Z) (translateTest Z f))
      congr 1
      ext X
      rw [translateTest_apply, translateTest_apply, neg_add_cancel_right]
    rw [h1, apply_eq_comp_extendTest_restrict hS₁supp hα]

/-- **Lemma 3.12 on `V`.** Under the induction hypothesis, an invariant distribution on `V`
annihilates every `β` in the `D₀` of `V` that the nilpotent invariant distributions annihilate. -/
theorem centerOrthogonalInvariant_apply_eq_zero
    (hP3 : LieAlgebraCentralNilpotentDensityStatement.{u, v})
    (hIH : ∀ (B : Type v) [Ring B] [Algebra F B] [FiniteDimensional F B] [IsSemisimpleRing B],
      finrank F B < finrank F A → RegularOrbitalDensityFor F B)
    {α : SchwartzBruhat (centerSubmodule F A)} (hα : α 0 = 1)
    {S : Distribution (centerOrthogonal F A)} (hS : S ∈ centerOrthogonalInvariant F A)
    {β : SchwartzBruhat (centerOrthogonal F A)} (hβ : CenterOrthogonalVanishing F A β)
    (hN : ∀ R ∈ centerOrthogonalNilpotentInvariant F A, R β = 0) : S β = 0 := by
  have key := hP3 F A hIH (extendTest α β) (hβ.regularOrbitalVanishing α) ?_
    (S.comp restrictCenterOrthogonal) (isConjugationInvariant_comp_restrict hS)
  · rwa [LinearMap.comp_apply, restrict_extendTest, hα, one_smul] at key
  · intro Z hZ S'' hS''
    obtain ⟨S₂, hS₂, hS₂eq⟩ := exists_centerOrthogonalNilpotentInvariant_of_translate hα hZ hS''
    rw [hS₂eq, show translateTest Z (extendTest α β) =
      extendTest (translateTest (⟨Z, hZ⟩ : centerSubmodule F A) α) β from
        translateTest_extendTest α β ⟨Z, hZ⟩, restrict_extendTest, map_smul, hN S₂ hS₂,
      smul_zero]

end Main

section Noncommutative

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {A : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
  [TopologicalSpace A] [IsTopologicalRing A] [IsModuleTopology F A] [T2Space A]
  [MeasurableSpace Aˣ] [BorelSpace Aˣ]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- The nilpotent orbital distributions, composed with `extendTest α`, are nilpotent invariant
distributions on `V`. -/
theorem comp_extendTest_mem_centerOrthogonalNilpotentInvariant
    {μ : Distribution A} (hμ : μ ∈ nilpotentOrbitals A) (α : SchwartzBruhat (centerSubmodule F A)) :
    μ.comp (extendTest α) ∈ centerOrthogonalNilpotentInvariant F A := by
  obtain ⟨N, hN, _, _, μG, _, μH, _, _, ν, hcompat, hconv, rfl⟩ := hμ
  refine ⟨comp_extendTest_mem_centerOrthogonalInvariant
    (orbitalDistribution_isConjugationInvariant N ν hcompat.right_invariant hconv) α, ?_⟩
  intro β hβ
  apply orbitalDistribution_mem_supportedOn N ν hconv
  intro X hX
  have hsub : closure (conjugationSaturation ({N} : Set A)) ⊆ closure {X : A | IsNilpotent X} :=
    closure_mono fun Y hY => isNilpotent_of_mem_conjugationSaturation hN hY
  have hXN := hsub hX
  have hXV := closure_nilpotent_subset_centerOrthogonal (F := F) hXN
  rw [show X = ((⟨X, hXV⟩ : centerOrthogonal F A) : A) from rfl, extendTest_apply_coe,
    hβ _ hXN, mul_zero]

/-- **The final step of Harish-Chandra's proof (Lemma 3.15 and the homogeneity argument),
on `V`.** When `A` is not commutative, every nilpotent invariant distribution on `V` annihilates
the `D₀` of `V`. -/
theorem centerOrthogonalNilpotentInvariant_apply_eq_zero_of_ne_top
    (hP1 : LieAlgebraRegularOrbitalFourierStabilityStatement.{u, v})
    (hP2a : LieAlgebraNilpotentInvariantSpanStatement.{u, v})
    (hP2b : LieAlgebraNilpotentOrbitalHomogeneityStatement.{u, v})
    (hP3 : LieAlgebraCentralNilpotentDensityStatement.{u, v})
    (hIH : ∀ (B : Type v) [Ring B] [Algebra F B] [FiniteDimensional F B] [IsSemisimpleRing B],
      finrank F B < finrank F A → RegularOrbitalDensityFor F B)
    (hA : Subalgebra.center F A ≠ ⊤)
    {R : Distribution (centerOrthogonal F A)} (hR : R ∈ centerOrthogonalNilpotentInvariant F A)
    {β : SchwartzBruhat (centerOrthogonal F A)} (hβ : CenterOrthogonalVanishing F A β) :
    R β = 0 := by
  classical
  borelize A
  let : MeasurableSpace (centerSubmodule F A) := borel _
  have : BorelSpace (centerSubmodule F A) := ⟨rfl⟩
  let : MeasurableSpace (centerOrthogonal F A) := borel _
  have : BorelSpace (centerOrthogonal F A) := ⟨rfl⟩
  have : IsFiniteDimensionalOverLocalField F A := ⟨inferInstance, inferInstance⟩
  obtain ⟨α, hα1, hαint⟩ := exists_centerBump (F := F) (A := A)
  obtain ⟨ψ⟩ := nonempty_unitaryAdditiveCharacter F
  let μz : Measure (centerSubmodule F A) := Measure.addHaar
  let μV : AdditiveHaarMeasure (centerOrthogonal F A) :=
    ⟨Measure.addHaar, inferInstance, inferInstance⟩
  let Fv := centerOrthogonalFourier ψ μV
  have hFst : ∀ γ, CenterOrthogonalVanishing F A γ → CenterOrthogonalVanishing F A (Fv γ) :=
    fun γ hγ => hγ.fourier hP1 ψ μz μV (hαint μz)
  obtain ⟨C, hC, hinv⟩ : ∃ C : ℝ, 0 < C ∧
      ∀ (γ : SchwartzBruhat (centerOrthogonal F A)) (Y : centerOrthogonal F A),
        Fv (Fv γ) Y = (C : ℂ) * γ (-Y) := by
    obtain ⟨C, hC, h⟩ := exists_pos_bicharacterFourier_bicharacterFourier μV.measure
      (isSelfDualBicharacter_pairingCharacter ψ centerOrthogonalPairing_isSymm
        centerOrthogonalPairing_nondegenerate)
    exact ⟨C, hC, fun γ Y => h γ γ.2 Y⟩
  have hsurj : ∀ γ, CenterOrthogonalVanishing F A γ →
      ∃ δ, CenterOrthogonalVanishing F A δ ∧ Fv δ = γ := by
    intro γ hγ
    refine ⟨((C : ℂ)⁻¹) • Fv (scalarDilation (-1) γ),
      (hFst _ (hγ.scalarDilation (-1))).smul _, ?_⟩
    ext Y
    rw [map_smul, SetLike.val_smul, Pi.smul_apply, hinv, scalarDilation_apply, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hC.ne'), one_mul]
    rw [inv_neg, inv_one, Units.smul_def, Units.val_neg, Units.val_one, neg_one_smul, neg_neg]
  let G := (fun T : Distribution A => T.comp (extendTest α)) '' nilpotentOrbitals A
  have hGle : G ⊆ centerOrthogonalNilpotentInvariant F A := by
    rintro _ ⟨μ, hμ, rfl⟩
    exact comp_extendTest_mem_centerOrthogonalNilpotentInvariant hμ α
  have hspanN : centerOrthogonalNilpotentInvariant F A ≤ Submodule.span ℂ G :=
    centerOrthogonalNilpotentInvariant_le_span hP2a hα1
  -- the transported Fourier transform of a generator vanishes on the `D₀` of `V`
  have key : ∀ μ ∈ nilpotentOrbitals A, ∀ δ, CenterOrthogonalVanishing F A δ →
      (μ.comp (extendTest α)) (Fv δ) = 0 := by
    intro μ hμ δ hδ
    have hRinv := (comp_extendTest_mem_centerOrthogonalNilpotentInvariant hμ α).1
    have hRhat : (μ.comp (extendTest α)).comp Fv ∈ centerOrthogonalInvariant F A := by
      intro u γ
      rw [LinearMap.comp_apply, LinearMap.comp_apply, fourier_pullback_centerOrthogonalConj]
      exact hRinv u _
    let C₁ := centerOrthogonalVanishingSubmodule (F := F) (A := A)
    let ρ : Distribution (centerOrthogonal F A) →ₗ[ℂ] Module.Dual ℂ C₁ := C₁.subtype.dualMap
    let W : Submodule ℂ (Module.Dual ℂ C₁) := Submodule.span ℂ (ρ '' G)
    have hWfin : FiniteDimensional ℂ W := by
      have := finiteDimensional_centerOrthogonalNilpotentInvariant (F := F) (A := A) hP2a
      have hle : W ≤ (centerOrthogonalNilpotentInvariant F A).map ρ :=
        Submodule.span_le.2 (by rintro _ ⟨S, hS, rfl⟩; exact ⟨S, hGle hS, rfl⟩)
      exact Submodule.finiteDimensional_of_le hle
    have hmem : ρ ((μ.comp (extendTest α)).comp Fv) ∈ W := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (K := ℂ) (V := C₁) (W := W),
        Submodule.mem_dualAnnihilator]
      intro x hx
      rw [Submodule.mem_dualCoannihilator] at hx
      change (μ.comp (extendTest α)).comp Fv (x : SchwartzBruhat (centerOrthogonal F A)) = 0
      refine centerOrthogonalInvariant_apply_eq_zero hP3 hIH hα1 hRhat x.2 fun R' hR' => ?_
      exact hx _ (Submodule.apply_mem_span_image_of_mem_span ρ (hspanN hR'))
    obtain ⟨n, c, w, hw⟩ := Submodule.mem_span_set'.1 hmem
    choose S hS hSw using fun i => (w i).2
    have hSG : ∀ i, ∃ μ' ∈ nilpotentOrbitals A, S i = μ'.comp (extendTest α) := by
      intro i
      obtain ⟨μ', hμ', h⟩ := hS i
      exact ⟨μ', hμ', h.symm⟩
    choose μ' hμ' hSμ using hSG
    choose e he hhom using fun i => exists_homogeneity_degree hP2b hA α (hμ' i)
    obtain ⟨d, hd, hhomd⟩ := exists_homogeneity_degree hP2b hA α hμ
    obtain ⟨t, ht⟩ := exists_one_lt_distribHaarChar F
    set n₁ := finrank F (centerOrthogonal F A)
    refine eq_zero_of_forall_scaling (x := (distribHaarChar F t : ℝ)) ht (n := 2 * n₁) (d := d)
      (e := e) (c := fun i => c i * S i δ) (fun i => by have := he i; omega) fun m => ?_
    have hδm : CenterOrthogonalVanishing F A (scalarDilation ((t ^ m) ^ 2) δ) :=
      hδ.scalarDilation _
    have hev := congrArg (fun φ : Module.Dual ℂ C₁ => φ ⟨scalarDilation ((t ^ m) ^ 2) δ, hδm⟩) hw
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hev
    have hχ : ((distribHaarChar F (t ^ m) : ℝ) : ℂ) = (((distribHaarChar F t : ℝ) ^ m : ℝ) : ℂ) := by
      rw [map_pow, NNReal.coe_pow]
    have hlhs : ρ ((μ.comp (extendTest α)).comp Fv) ⟨scalarDilation ((t ^ m) ^ 2) δ, hδm⟩ =
        (((distribHaarChar F t : ℝ) ^ m : ℝ) : ℂ) ^ (2 * n₁) *
          ((((distribHaarChar F t : ℝ) ^ m : ℝ) : ℂ)⁻¹) ^ d * (μ.comp (extendTest α)) (Fv δ) := by
      change (μ.comp (extendTest α)) (Fv (scalarDilation ((t ^ m) ^ 2) δ)) = _
      rw [fourier_scalarDilation, map_smul, ← inv_pow, hhomd, map_pow, map_inv, NNReal.coe_pow,
        NNReal.coe_inv, smul_eq_mul, ← hχ]
      push_cast
      ring
    have hrhs : ∀ i, (w i : Module.Dual ℂ C₁) ⟨scalarDilation ((t ^ m) ^ 2) δ, hδm⟩ =
        (((distribHaarChar F t : ℝ) ^ m : ℝ) : ℂ) ^ e i * S i δ := by
      intro i
      rw [← hSw i]
      change S i (scalarDilation ((t ^ m) ^ 2) δ) = _
      rw [hSμ i, hhom i, ← hSμ i, hχ]
    rw [hlhs] at hev
    rw [← hev]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrhs i]
    ring
  have hgen : ∀ R' ∈ G, ∀ γ, CenterOrthogonalVanishing F A γ → R' γ = 0 := by
    rintro _ ⟨μ, hμ, rfl⟩ γ hγ
    obtain ⟨δ, hδ, rfl⟩ := hsurj γ hγ
    exact key μ hμ δ hδ
  have hRspan : R ∈ Submodule.span ℂ G := hspanN hR
  clear hR
  induction hRspan using Submodule.span_induction with
  | mem x hx => exact hgen x hx β hβ
  | zero => rfl
  | add x y _ _ hx hy => rw [LinearMap.add_apply, hx, hy, add_zero]
  | smul a x _ hx => rw [LinearMap.smul_apply, hx, smul_zero]

end Noncommutative

section Final

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {A : Type v} [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsSemisimpleRing A] in
/-- In a commutative semisimple algebra every element, in particular `0`, is regular. -/
theorem zero_mem_regularSet_of_center_eq_top (hA : Subalgebra.center F A = ⊤) :
    (0 : A) ∈ regularSet F A := by
  obtain ⟨X, hX⟩ := regularSet_nonempty F (A := A)
  have hXc : ∀ Y : A, Y * X = X * Y :=
    (Subalgebra.mem_center_iff (R := F)).1 (by rw [hA]; exact Algebra.mem_top)
  have h : adjointEndomorphism F (0 : A) = adjointEndomorphism F X := by
    ext Y
    simp [adjointEndomorphism_apply, hXc Y]
  show adjointEta F (0 : A) ≠ 0
  rw [adjointEta, h]
  exact hX

variable [TopologicalSpace A] [IsTopologicalRing A] [IsModuleTopology F A] [T2Space A]
  [MeasurableSpace Aˣ] [BorelSpace Aˣ]

omit [T2Space A] in
/-- **The commutative case.** If `A` is commutative, `V = 0`, and the `D₀` of `V` is `0`: the
Dirac distribution at `0` lies in `J(N)`, so by Lemma 3.3 there is a compatible quotient measure
on the one-point coset space of the centralizer `Aˣ` of `0`, whose orbital integral at `0` is a
nonzero multiple of the value at `0`. -/
theorem centerOrthogonalVanishing_eq_zero_of_center_eq_top
    (hP2a : LieAlgebraNilpotentInvariantSpanStatement.{u, v}) (hA : Subalgebra.center F A = ⊤)
    {β : SchwartzBruhat (centerOrthogonal F A)} (hβ : CenterOrthogonalVanishing F A β) :
    β = 0 := by
  have hcen : ∀ X : A, X ∈ Subalgebra.center F A := fun X => by rw [hA]; exact Algebra.mem_top
  have hV : ∀ Y : centerOrthogonal F A, Y = 0 := fun Y =>
    Subtype.ext (eq_zero_of_mem_center_of_mem_centerOrthogonal (hcen Y) Y.2)
  let δ : Distribution A :=
    { toFun := fun f => f 0, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hδ : δ ∈ invariantSupportedIn {X : A | IsNilpotent X} := by
    refine (mem_invariantSupportedIn_iff _ _).2 ⟨?_, ?_⟩
    · rw [isConjugationInvariant_iff]
      intro u f
      change f ((u : A) * 0 * ((u⁻¹ : Aˣ) : A)) = f 0
      rw [mul_zero, zero_mul]
    · intro f hf
      exact hf 0 (subset_closure (subset_conjugationSaturation _ IsNilpotent.zero))
  have : IsFiniteDimensionalOverLocalField F A := ⟨inferInstance, inferInstance⟩
  have hδ0 : δ ≠ 0 := by
    obtain ⟨K, hKc, hKo, -⟩ := CompactOpenExhaustion.exists_superset (∅ : Set A) isCompact_empty
    have hKcl : IsClopen (K : Set A) := ⟨AddSubgroup.isClosed_of_isOpen K hKo, hKo⟩
    intro h
    have h' := congrArg (fun T : Distribution A =>
      T (Hecke.TestFunction.characteristic hKcl hKc)) h
    simp only [δ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] at h'
    rw [Hecke.TestFunction.characteristic_apply, Set.indicator_of_mem K.zero_mem] at h'
    exact one_ne_zero h'
  obtain ⟨R, hR⟩ : (nilpotentOrbitals A).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hspan := (hP2a F A).2 hδ
    rw [hne, Submodule.span_empty, Submodule.mem_bot] at hspan
    exact hδ0 hspan
  obtain ⟨N, hN, _, _, μG, _, μH, _, _, ν, hcompat, hconv, rfl⟩ := hR
  have hN0 : N = 0 := eq_zero_of_isNilpotent_of_commute hN fun Y =>
    (Subalgebra.mem_center_iff (R := F)).1 (hcen N) Y
  subst hN0
  obtain ⟨α, hα, -⟩ := exists_centerBump (F := F) (A := A)
  have h0 : OrbitalVanishingAt (0 : A) (extendTest α β) :=
    hβ α 0 (zero_mem_regularSet_of_center_eq_top hA)
  have h1 := h0 μG μH ν hcompat hconv
  rw [orbitalDistribution_zero_apply] at h1
  have h2 : extendTest α β (0 : A) = β 0 := by
    rw [show (0 : A) = ((0 : centerOrthogonal F A) : A) from rfl, extendTest_apply_coe, hα,
      one_mul]
  rw [h2] at h1
  have hsub : (Set.univ : Set (LeftQuotient (conjugationCentralizer (0 : A)))).Subsingleton := by
    intro q _ q' _
    induction q using Quotient.inductionOn with
    | h g =>
      induction q' using Quotient.inductionOn with
      | h g' =>
        exact Quotient.sound (QuotientGroup.rightRel_apply.2
          (by rw [conjugationCentralizer_zero]; trivial))
  have hfin : ν Set.univ ≠ ⊤ := by
    have := hcompat.regular
    exact hsub.isCompact.measure_lt_top.ne
  have hne : ν Set.univ ≠ 0 := by
    rw [Ne, Measure.measure_univ_eq_zero]
    exact hcompat.nonzero
  have hreal : ν.real Set.univ ≠ 0 := by
    rw [measureReal_def]
    exact ENNReal.toReal_ne_zero.2 ⟨hne, hfin⟩
  have hβ0 : β 0 = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (by exact_mod_cast h) hreal
    · exact h
  ext Y
  rw [hV Y]
  exact hβ0

/-- Every nilpotent invariant distribution on `V` annihilates the `D₀` of `V`. -/
theorem centerOrthogonalNilpotentInvariant_apply_eq_zero
    (hP1 : LieAlgebraRegularOrbitalFourierStabilityStatement.{u, v})
    (hP2a : LieAlgebraNilpotentInvariantSpanStatement.{u, v})
    (hP2b : LieAlgebraNilpotentOrbitalHomogeneityStatement.{u, v})
    (hP3 : LieAlgebraCentralNilpotentDensityStatement.{u, v})
    (hIH : ∀ (B : Type v) [Ring B] [Algebra F B] [FiniteDimensional F B] [IsSemisimpleRing B],
      finrank F B < finrank F A → RegularOrbitalDensityFor F B)
    {R : Distribution (centerOrthogonal F A)} (hR : R ∈ centerOrthogonalNilpotentInvariant F A)
    {β : SchwartzBruhat (centerOrthogonal F A)} (hβ : CenterOrthogonalVanishing F A β) :
    R β = 0 := by
  by_cases hA : Subalgebra.center F A = ⊤
  · rw [centerOrthogonalVanishing_eq_zero_of_center_eq_top hP2a hA hβ, map_zero]
  · exact centerOrthogonalNilpotentInvariant_apply_eq_zero_of_ne_top hP1 hP2a hP2b hP3 hIH hA hR hβ

end Final

/-- **The inductive step.** If Theorem 3.1 holds for all semisimple algebras of smaller
dimension, it holds for `A`: by Lemma 3.12 with central translates it suffices that every
invariant distribution supported on `Z + N` annihilates `D₀`, and such a distribution is a
nilpotent invariant distribution on `V` applied to the restriction of the translate by `Z`. -/
theorem regularOrbitalDensityFor_of_inputs {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
    (hP1 : LieAlgebraRegularOrbitalFourierStabilityStatement.{u, v})
    (hP2a : LieAlgebraNilpotentInvariantSpanStatement.{u, v})
    (hP2b : LieAlgebraNilpotentOrbitalHomogeneityStatement.{u, v})
    (hP3 : LieAlgebraCentralNilpotentDensityStatement.{u, v})
    (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A]
    (hIH : ∀ (B : Type v) [Ring B] [Algebra F B] [FiniteDimensional F B] [IsSemisimpleRing B],
      finrank F B < finrank F A → RegularOrbitalDensityFor F B) :
    RegularOrbitalDensityFor F A := by
  intro _ _ _ _
  have : IsTopologicalRing A := IsModuleTopology.isTopologicalRing F A
  have : T2Space A := t2Space_of_finiteDimensional F A
  intro f hf T hT
  obtain ⟨α, hα, -⟩ := exists_centerBump (F := F) (A := A)
  refine hP3 F A hIH f hf ?_ T hT
  intro Z hZ S hS
  obtain ⟨S₂, hS₂, hS₂eq⟩ := exists_centerOrthogonalNilpotentInvariant_of_translate hα hZ hS
  rw [hS₂eq]
  exact centerOrthogonalNilpotentInvariant_apply_eq_zero hP1 hP2a hP2b hP3 hIH hS₂
    (RegularOrbitalVanishing.centerOrthogonalVanishing_restrict
      (hf.translate_central fun Y => (Subalgebra.mem_center_iff (R := F)).1 hZ Y))

/-- Theorem 3.1 for every algebra, by strong induction on the dimension. -/
theorem regularOrbitalDensityFor_of_finrank_eq {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
    (hP1 : LieAlgebraRegularOrbitalFourierStabilityStatement.{u, v})
    (hP2a : LieAlgebraNilpotentInvariantSpanStatement.{u, v})
    (hP2b : LieAlgebraNilpotentOrbitalHomogeneityStatement.{u, v})
    (hP3 : LieAlgebraCentralNilpotentDensityStatement.{u, v}) (n : ℕ) :
    ∀ (A : Type v) [Ring A] [Algebra F A] [FiniteDimensional F A] [IsSemisimpleRing A],
      finrank F A = n → RegularOrbitalDensityFor F A := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A _ _ _ _ hn
    refine regularOrbitalDensityFor_of_inputs hP1 hP2a hP2b hP3 A fun B _ _ _ _ hB => ?_
    exact ih (finrank F B) (hn ▸ hB) B rfl

end RegularOrbitalDensityReduction

open RegularOrbitalDensityReduction in
/-- **Harish-Chandra's Theorem 3.1 from Lemmas 3.2, 3.3, 3.12 and 3.16.** -/
theorem lieAlgebraRegularOrbitalDensityReduction.{u, v} :
    LieAlgebraRegularOrbitalDensityReductionStatement.{u, v} := by
  intro hP1 hP2a hP2b hP3
  rw [lieAlgebraRegularOrbitalDensityStatement_iff]
  intro F _ _ _ _ _ A _ _ _ _
  exact regularOrbitalDensityFor_of_finrank_eq hP1 hP2a hP2b hP3 (finrank F A) A rfl

end Langlands.HarmonicAnalysis
