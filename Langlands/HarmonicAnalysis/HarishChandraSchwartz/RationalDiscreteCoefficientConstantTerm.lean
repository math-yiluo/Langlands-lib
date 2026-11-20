import Langlands.Analysis.Local.SiegelSetMeasure
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSquareIntegrableDecayProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalSpace
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SquareIntegrableSemisimplicity
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralSubgroupQuotientHaar
import Langlands.Representation.Plancherel.CoefficientTensors
import Langlands.Representation.Aubert.General.RationalLatticeStrictExponentProof
import Langlands.Representation.Aubert.General.JacquetAdmissibility
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityReduction
import Langlands.Representation.Exponents.CentralDecompositionProof
import Langlands.Representation.Jacquet.StandardFixedVectorStructure
import Langlands.Representation.Intertwining.PQCompositionHaarReduction
import Langlands.Representation.Plancherel.RationalModerateGrowthUniformization
import Langlands.Representation.Category.Contragredient
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CoefficientIndependence

/-! # Discrete-series coefficients have vanishing constant terms -/

noncomputable section

universe u uG uV uW

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct

namespace Langlands.HarishChandraSchwartz.DiscreteConstantTerm

/-! ### Invariant pairings between generalized eigenvectors -/

section GeneralizedEigenPairing

variable {X : Type*} {Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

/-- An invariant bilinear form vanishes on a pair of generalized eigenvectors whose
eigenvalues have product different from one. -/
theorem bilinear_eq_zero_of_genEigen (β : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (T : Module.End ℂ X)
    (S : Module.End ℂ Y) (hβ : ∀ x y, β (T x) (S y) = β x y) {a b : ℂ} (hab : a * b ≠ 1) :
    ∀ (n : ℕ) (x : X), ((T - a • 1) ^ n) x = 0 →
      ∀ (m : ℕ) (y : Y), ((S - b • 1) ^ m) y = 0 → β x y = 0 := by
  intro n
  induction n with
  | zero =>
    intro x hx m y _
    simp only [pow_zero, Module.End.one_apply] at hx
    simp [hx]
  | succ n ihn =>
    intro x hx m
    induction m with
    | zero =>
      intro y hy
      simp only [pow_zero, Module.End.one_apply] at hy
      simp [hy]
    | succ m ihm =>
      intro y hy
      rw [pow_succ, Module.End.mul_apply] at hx hy
      have h1 : β ((T - a • 1) x) y = 0 := ihn _ hx (m + 1) y (by
        rw [pow_succ, Module.End.mul_apply]; exact hy)
      have h2 : β ((T - a • 1) x) ((S - b • 1) y) = 0 := ihn _ hx m _ hy
      have h3 : β x ((S - b • 1) y) = 0 := ihm _ hy
      have hTx : T x = a • x + (T - a • 1) x := by
        simp
      have hSy : S y = b • y + (S - b • 1) y := by
        simp
      have key := hβ x y
      rw [hTx, hSy] at key
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        h1, h2, h3, mul_zero, add_zero] at key
      have h0 : (1 - a * b) * β x y = 0 := by linear_combination -key
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd (by linear_combination -h) hab
      · exact h

end GeneralizedEigenPairing

/-! ### Change of variables under conjugation -/

section Conjugation

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

variable (U : Subgroup Γ) [MeasurableSpace U] [BorelSpace U] [LocallyCompactSpace U]

/-- Integration against a Haar measure on `U` of the conjugate `u ↦ f (g⁻¹ u g)`. -/
theorem integral_conj_symm (g : Subgroup.normalizer (U : Set Γ)) (mu : Measure U)
    [mu.IsHaarMeasure] [mu.Regular] (f : U → ℂ) :
    (∫ u, f ((HaarModulus.normalizerConj U g).symm u) ∂mu) =
      (mulEquivHaarChar (HaarModulus.normalizerConj U g) : ℝ≥0) • ∫ u, f u ∂mu := by
  let e := (HaarModulus.normalizerConj U g).toHomeomorph.toMeasurableEquiv
  change (∫ u, f (e.symm u) ∂mu) = _
  rw [← integral_map_equiv e.symm, e.map_symm]
  change (∫ u, f u ∂(mu.comap (HaarModulus.normalizerConj U g))) = _
  rw [← mulEquivHaarChar_smul_eq_comap mu (HaarModulus.normalizerConj U g)]
  exact integral_smul_nnreal_measure f _

end Conjugation

/-! ### The radical pairing -/

section RadicalPairing

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  (U : Subgroup Γ) [MeasurableSpace U] (mu : Measure U)
  {X : Type uV} {Y : Type uW} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  (ρ₁ : Representation ℂ Γ X) (ρ₂ : Representation ℂ Γ Y) (p : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)

/-- Absolute convergence of the radical integrals `u ↦ p (ρ₁(u) x) y`. -/
def IsRadicalIntegrable : Prop :=
  ∀ (x : X) (y : Y), Integrable (fun u : U => p (ρ₁ (u : Γ) x) y) mu

variable {U mu ρ₁ ρ₂ p}

/-- The bilinear form `(x, y) ↦ ∫_U p (ρ₁(u) x) y du`. -/
def radicalPairing (hint : IsRadicalIntegrable U mu ρ₁ p) : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun x y => ∫ u, p (ρ₁ (u : Γ) x) y ∂mu)
    (fun x₁ x₂ y => by
      simp only [map_add, LinearMap.add_apply]
      exact integral_add (hint _ _) (hint _ _))
    (fun c x y => by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact integral_const_mul c _)
    (fun x y₁ y₂ => by
      simp only [map_add]
      exact integral_add (hint _ _) (hint _ _))
    (fun c x y => by
      simp only [map_smul, smul_eq_mul]
      exact integral_const_mul c _)

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
@[simp] theorem radicalPairing_apply (hint : IsRadicalIntegrable U mu ρ₁ p) (x : X) (y : Y) :
    radicalPairing hint x y = ∫ u, p (ρ₁ (u : Γ) x) y ∂mu := rfl

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
/-- Right translation by the radical: right invariance of the measure. -/
theorem radicalPairing_right [MeasurableMul U] [mu.IsMulRightInvariant]
    (hint : IsRadicalIntegrable U mu ρ₁ p) (u₀ : U) (x : X) (y : Y) :
    radicalPairing hint (ρ₁ (u₀ : Γ) x) y = radicalPairing hint x y := by
  simp only [radicalPairing_apply]
  have h : ∀ u : U, p (ρ₁ (u : Γ) (ρ₁ (u₀ : Γ) x)) y = p (ρ₁ ((u * u₀ : U) : Γ) x) y := by
    intro u
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  simp_rw [h]
  exact integral_mul_right_eq_self (fun u : U => p (ρ₁ (u : Γ) x) y) u₀

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] in
/-- Translation of the second variable by the radical: invariance of `p` and left
invariance of the measure. -/
theorem radicalPairing_left [MeasurableMul U] [mu.IsMulLeftInvariant]
    (hint : IsRadicalIntegrable U mu ρ₁ p)
    (hp : ∀ (g : Γ) (x : X) (y : Y), p (ρ₁ g x) (ρ₂ g y) = p x y) (u₀ : U) (x : X) (y : Y) :
    radicalPairing hint x (ρ₂ (u₀ : Γ) y) = radicalPairing hint x y := by
  simp only [radicalPairing_apply]
  have h : ∀ u : U, p (ρ₁ (u : Γ) x) (ρ₂ (u₀ : Γ) y) = p (ρ₁ ((u₀⁻¹ * u : U) : Γ) x) y := by
    intro u
    rw [← hp ((u₀ : Γ)⁻¹) (ρ₁ (u : Γ) x) (ρ₂ (u₀ : Γ) y), Representation.inv_self_apply,
      Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Module.End.mul_apply]
  simp_rw [h]
  exact integral_mul_left_eq_self (fun u : U => p (ρ₁ (u : Γ) x) y) u₀⁻¹

variable [BorelSpace U] [LocallyCompactSpace U]

/-- Simultaneous translation by an element of the normalizer multiplies the pairing by the
Haar modulus of the conjugation automorphism. -/
theorem radicalPairing_conj [mu.IsHaarMeasure] [mu.Regular]
    (hint : IsRadicalIntegrable U mu ρ₁ p)
    (hp : ∀ (g : Γ) (x : X) (y : Y), p (ρ₁ g x) (ρ₂ g y) = p x y)
    (g : Subgroup.normalizer (U : Set Γ)) (x : X) (y : Y) :
    radicalPairing hint (ρ₁ (g : Γ) x) (ρ₂ (g : Γ) y) =
      ((mulEquivHaarChar (HaarModulus.normalizerConj U g) : ℝ) : ℂ) *
        radicalPairing hint x y := by
  simp only [radicalPairing_apply]
  have h : ∀ u : U, p (ρ₁ (u : Γ) (ρ₁ (g : Γ) x)) (ρ₂ (g : Γ) y) =
      p (ρ₁ (((HaarModulus.normalizerConj U g).symm u : U) : Γ) x) y := by
    intro u
    rw [← hp ((g : Γ)⁻¹) _ (ρ₂ (g : Γ) y), Representation.inv_self_apply,
      HaarModulus.normalizerConj_symm_apply, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply]
  simp_rw [h]
  have key := integral_conj_symm U g mu (fun u : U => p (ρ₁ (u : Γ) x) y)
  rw [key, NNReal.smul_def, Complex.real_smul]

end RadicalPairing

/-! ### Descent to Jacquet modules -/

section JacquetPairing

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {U : Subgroup Γ} [MeasurableSpace U] [BorelSpace U] {mu : Measure U}
  {X : Type uV} {Y : Type uW} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  {ρ₁ : Representation ℂ Γ X} {ρ₂ : Representation ℂ Γ Y} {p : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ}

/-- The radical pairing factors through the two spaces of `U`-coinvariants. -/
def jacquetPairing [mu.IsMulLeftInvariant] [mu.IsMulRightInvariant]
    (hint : IsRadicalIntegrable U mu ρ₁ p)
    (hp : ∀ (g : Γ) (x : X) (y : Y), p (ρ₁ g x) (ρ₂ g y) = p x y) :
    Jacquet.Localization.Coinvariants ρ₁ U 1 →ₗ[ℂ]
      Jacquet.Localization.Coinvariants ρ₂ U 1 →ₗ[ℂ] ℂ :=
  (Jacquet.Localization.lift ρ₂ U 1
    (Jacquet.Localization.lift ρ₁ U 1 (radicalPairing hint) (fun u x => by
      ext y
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      exact radicalPairing_right hint u x y)).flip
    (fun u y => by
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
        Jacquet.Localization.lift_mk, MonoidHom.one_apply, Units.val_one, one_smul]
      exact radicalPairing_left hint hp u x y)).flip

@[simp] theorem jacquetPairing_mk [mu.IsMulLeftInvariant] [mu.IsMulRightInvariant]
    (hint : IsRadicalIntegrable U mu ρ₁ p)
    (hp : ∀ (g : Γ) (x : X) (y : Y), p (ρ₁ g x) (ρ₂ g y) = p x y) (x : X) (y : Y) :
    jacquetPairing hint hp (Jacquet.Localization.mk ρ₁ U 1 x)
      (Jacquet.Localization.mk ρ₂ U 1 y) = radicalPairing hint x y := rfl

end JacquetPairing

/-! ### Vanishing from strict central exponents -/

section StrictExponents

variable {M : Type uG} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
  {X : Type uV} {Y : Type uW} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

/-- A bilinear form invariant under a central element `z` vanishes when every central
exponent of both smooth center-finite representations has absolute value less than one
at `z`. -/
theorem bilinear_eq_zero_of_strictExponents (ρ₁ : Representation ℂ M X)
    (ρ₂ : Representation ℂ M Y) (hs₁ : IsSmooth ρ₁) (hs₂ : IsSmooth ρ₂)
    (hc₁ : IsCenterFinite ρ₁) (hc₂ : IsCenterFinite ρ₂) (β : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (z : Subgroup.center M) (hβ : ∀ x y, β (ρ₁ (z : M) x) (ρ₂ (z : M) y) = β x y)
    (h₁ : ∀ χ, IsCentralExponent ρ₁ χ → ‖(χ z : ℂ)‖ < 1)
    (h₂ : ∀ χ, IsCentralExponent ρ₂ χ → ‖(χ z : ℂ)‖ < 1) :
    β = 0 := by
  have key : ∀ (χ₁ χ₂ : {χ : Subgroup.center M →* ℂˣ //
      IsOpen (χ.ker : Set (Subgroup.center M))}) (x : X) (y : Y),
      x ∈ (generalizedCentralCharacterSpace ρ₁ χ₁.val).toSubmodule →
      y ∈ (generalizedCentralCharacterSpace ρ₂ χ₂.val).toSubmodule → β x y = 0 := by
    intro χ₁ χ₂ x y hx hy
    by_cases hx0 : x = 0
    · simp [hx0]
    by_cases hy0 : y = 0
    · simp [hy0]
    have he₁ : IsCentralExponent ρ₁ χ₁.val := ⟨χ₁.2, fun hbot => hx0 (by
      rw [hbot] at hx
      exact (Submodule.mem_bot ℂ).mp hx)⟩
    have he₂ : IsCentralExponent ρ₂ χ₂.val := ⟨χ₂.2, fun hbot => hy0 (by
      rw [hbot] at hy
      exact (Submodule.mem_bot ℂ).mp hy)⟩
    obtain ⟨n, hn⟩ := (mem_generalizedCentralCharacterSpace ρ₁ χ₁.val x).mp hx
    obtain ⟨m, hm⟩ := (mem_generalizedCentralCharacterSpace ρ₂ χ₂.val y).mp hy
    refine bilinear_eq_zero_of_genEigen β (ρ₁ (z : M)) (ρ₂ (z : M)) hβ ?_ n x (hn z) m y (hm z)
    intro hab
    have hlt : ‖(χ₁.val z : ℂ) * (χ₂.val z : ℂ)‖ < 1 := by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (h₂ _ he₂).le).trans_lt (h₁ _ he₁)
    rw [hab, norm_one] at hlt
    exact lt_irrefl _ hlt
  have hX : ∀ x : X, x ∈ ⨆ χ : {χ : Subgroup.center M →* ℂˣ //
      IsOpen (χ.ker : Set (Subgroup.center M))},
      (generalizedCentralCharacterSpace ρ₁ χ.val).toSubmodule := by
    intro x
    rw [CentralDecomposition.smooth_spanning ρ₁ hs₁ hc₁]
    exact Submodule.mem_top
  have hY : ∀ y : Y, y ∈ ⨆ χ : {χ : Subgroup.center M →* ℂˣ //
      IsOpen (χ.ker : Set (Subgroup.center M))},
      (generalizedCentralCharacterSpace ρ₂ χ.val).toSubmodule := by
    intro y
    rw [CentralDecomposition.smooth_spanning ρ₂ hs₂ hc₂]
    exact Submodule.mem_top
  ext x y
  simp only [LinearMap.zero_apply]
  refine Submodule.iSup_induction _ (motive := fun x => β x y = 0) (hX x)
    (fun χ₁ x hx => ?_) (by simp)
    (fun x₁ x₂ h₁ h₂ => by simp only [map_add, LinearMap.add_apply, h₁, h₂, add_zero])
  exact Submodule.iSup_induction _ (motive := fun y => β x y = 0) (hY y)
    (fun χ₂ y hy => key χ₁ χ₂ x y hx hy) (by simp)
    (fun y₁ y₂ h₁ h₂ => by simp only [map_add, h₁, h₂, add_zero])

end StrictExponents

/-! ### Normalized Jacquet modules -/

section NormalizedJacquet

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [LocallyCompactSpace Γ]
  [NonarchimedeanGroup Γ]
  {U : Subgroup Γ} [MeasurableSpace U] [BorelSpace U] [LocallyCompactSpace U] {mu : Measure U}
  [mu.IsHaarMeasure] [mu.Regular] [mu.IsMulRightInvariant]
  {A₁ : SmoothRep.{0, uG, uV} ℂ Γ} {A₂ : SmoothRep.{0, uG, uW} ℂ Γ}
  {p : A₁ →ₗ[ℂ] A₂ →ₗ[ℂ] ℂ}

/-- The radical pairing as a bilinear form on the two normalized Jacquet modules. -/
def normalizedJacquetPairing (M : Subgroup Γ) (hU : IsClosed (U : Set Γ))
    (hMU : M ≤ Subgroup.normalizer (U : Set Γ))
    (hint : IsRadicalIntegrable U mu A₁.representation p)
    (hp : ∀ (g : Γ) (x : A₁) (y : A₂),
      p (A₁.representation g x) (A₂.representation g y) = p x y) :
    (Aubert.General.normalizedJacquetFunctor U M hU hMU).obj A₁ →ₗ[ℂ]
      (Aubert.General.normalizedJacquetFunctor U M hU hMU).obj A₂ →ₗ[ℂ] ℂ :=
  jacquetPairing hint hp

omit [LocallyCompactSpace U] [mu.Regular] in
theorem normalizedJacquetPairing_mk (M : Subgroup Γ) (hU : IsClosed (U : Set Γ))
    (hMU : M ≤ Subgroup.normalizer (U : Set Γ))
    (hint : IsRadicalIntegrable U mu A₁.representation p)
    (hp : ∀ (g : Γ) (x : A₁) (y : A₂),
      p (A₁.representation g x) (A₂.representation g y) = p x y) (x : A₁) (y : A₂) :
    normalizedJacquetPairing M hU hMU hint hp (Jacquet.Localization.mk A₁.representation U 1 x)
      (Jacquet.Localization.mk A₂.representation U 1 y) = radicalPairing hint x y := rfl

/-- The normalization `δ_P^{-1/2}` exactly compensates the Haar modulus of conjugation, so
the radical pairing is invariant under the normalized Jacquet actions of `M`. -/
theorem normalizedJacquetPairing_invariant (M : Subgroup Γ) (hU : IsClosed (U : Set Γ))
    (hMU : M ≤ Subgroup.normalizer (U : Set Γ))
    (hint : IsRadicalIntegrable U mu A₁.representation p)
    (hp : ∀ (g : Γ) (x : A₁) (y : A₂),
      p (A₁.representation g x) (A₂.representation g y) = p x y) (m : M)
    (x : (Aubert.General.normalizedJacquetFunctor U M hU hMU).obj A₁)
    (y : (Aubert.General.normalizedJacquetFunctor U M hU hMU).obj A₂) :
    normalizedJacquetPairing M hU hMU hint hp
        (((Aubert.General.normalizedJacquetFunctor U M hU hMU).obj A₁).representation m x)
        (((Aubert.General.normalizedJacquetFunctor U M hU hMU).obj A₂).representation m y) =
      normalizedJacquetPairing M hU hMU hint hp x y := by
  obtain ⟨x, rfl⟩ := Jacquet.Localization.mk_surjective A₁.representation U 1 x
  obtain ⟨y, rfl⟩ := Jacquet.Localization.mk_surjective A₂.representation U 1 y
  set c := HaarModulus.closedInverseHalfCharacter U hU M hMU m
  change jacquetPairing hint hp
      (((c : ℂˣ) : ℂ) • Jacquet.Localization.mk A₁.representation U 1 (A₁.representation m x))
      (((c : ℂˣ) : ℂ) • Jacquet.Localization.mk A₂.representation U 1 (A₂.representation m y)) =
    radicalPairing hint x y
  rw [map_smul, map_smul, LinearMap.smul_apply, jacquetPairing_mk,
    radicalPairing_conj (ρ₂ := A₂.representation) hint hp ⟨(m : Γ), hMU m.2⟩ x y]
  have hsq := Jacquet.inverseHalfCharacter_sq (HaarModulus.closedRestrictCharacter U hU M hMU) m
  have hδ : (HaarModulus.closedRestrictCharacter U hU M hMU m : ℝ≥0) =
      mulEquivHaarChar (HaarModulus.normalizerConj U ⟨(m : Γ), hMU m.2⟩) :=
    Langlands.SiegelSetMeasure.mulEquivHaarChar_congr (@BorelSpace.mk _ _ (borel U) rfl) _ _
  have hc : ((c : ℂˣ) : ℂ) ^ 2 *
      ((mulEquivHaarChar (HaarModulus.normalizerConj U ⟨(m : Γ), hMU m.2⟩) : ℝ) : ℂ) = 1 := by
    have h1 := congrArg (fun w : ℂˣ => (w : ℂ)) hsq
    simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      Jacquet.complexCharacter_apply] at h1
    change ((c : ℂˣ) : ℂ) ^ 2 = _ at h1
    rw [h1, hδ, inv_mul_cancel₀]
    exact_mod_cast (mulEquivHaarChar_pos _).ne'
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc, ← pow_two, hc, one_mul]

/-- Vanishing of radical integrals from strict central exponents of both admissible
normalized Jacquet modules at one central element of `M`. -/
theorem radicalPairing_eq_zero_of_strict (M : Subgroup Γ) (hU : IsClosed (U : Set Γ))
    (hMU : M ≤ Subgroup.normalizer (U : Set Γ))
    (hint : IsRadicalIntegrable U mu A₁.representation p)
    (hp : ∀ (g : Γ) (x : A₁) (y : A₂),
      p (A₁.representation g x) (A₂.representation g y) = p x y)
    (hadm₁ : ((Aubert.General.normalizedJacquetFunctor U M hU hMU).obj A₁).IsAdmissible)
    (hadm₂ : ((Aubert.General.normalizedJacquetFunctor U M hU hMU).obj A₂).IsAdmissible)
    (z : Subgroup.center M)
    (h₁ : ∀ χ, IsCentralExponent
      ((Aubert.General.normalizedJacquetFunctor U M hU hMU).obj A₁).representation χ →
        ‖(χ z : ℂ)‖ < 1)
    (h₂ : ∀ χ, IsCentralExponent
      ((Aubert.General.normalizedJacquetFunctor U M hU hMU).obj A₂).representation χ →
        ‖(χ z : ℂ)‖ < 1) (x : A₁) (y : A₂) :
    radicalPairing hint x y = 0 := by
  have hβ := bilinear_eq_zero_of_strictExponents _ _
    ((Aubert.General.normalizedJacquetFunctor U M hU hMU).obj A₁).isSmooth
    ((Aubert.General.normalizedJacquetFunctor U M hU hMU).obj A₂).isSmooth
    (CentralDecomposition.admissible_centerFinite _ hadm₁)
    (CentralDecomposition.admissible_centerFinite _ hadm₂)
    (normalizedJacquetPairing M hU hMU hint hp) z
    (fun x y => normalizedJacquetPairing_invariant M hU hMU hint hp (z : M) x y) h₁ h₂
  rw [← normalizedJacquetPairing_mk M hU hMU hint hp, hβ]
  rfl

end NormalizedJacquet

/-! ### The evaluation pairing on universe lifts -/

section EvaluationPairing

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- The evaluation pairing `(v, ℓ) ↦ ℓ(v)` between the universe lifts of a smooth
representation and of its smooth contragredient. -/
def liftedEvaluation (A : SmoothRep.{0, uG, uV} ℂ Γ) :
    SmoothRep.universeLift.{uW} A →ₗ[ℂ]
      SmoothRep.universeLift.{uW} A.contragredient →ₗ[ℂ] ℂ :=
  (smoothDualPairing A.representation).flip.compl₁₂
    (SmoothRep.universeLiftEquiv.{uW} A).symm.toLinearEquiv.toLinearMap
    (SmoothRep.universeLiftEquiv.{uW} A.contragredient).symm.toLinearEquiv.toLinearMap

theorem liftedEvaluation_apply (A : SmoothRep.{0, uG, uV} ℂ Γ) (v : A)
    (ℓ : SmoothDual A.representation) :
    liftedEvaluation.{uG, uV, uW} A (SmoothRep.universeLiftEquiv.{uW} A v)
        (SmoothRep.universeLiftEquiv.{uW} A.contragredient ℓ) = ℓ.val v := rfl

/-- The evaluation pairing is invariant under the diagonal action. -/
theorem liftedEvaluation_invariant (A : SmoothRep.{0, uG, uV} ℂ Γ) (g : Γ)
    (x : SmoothRep.universeLift.{uW} A) (y : SmoothRep.universeLift.{uW} A.contragredient) :
    liftedEvaluation A ((SmoothRep.universeLift.{uW} A).representation g x)
        ((SmoothRep.universeLift.{uW} A.contragredient).representation g y) =
      liftedEvaluation A x y :=
  smoothDualPairing_invariant g _ _

end EvaluationPairing

/-! ### Rational points: vanishing of radical integrals of discrete-series coefficients -/

section Rational

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Aubert.General Aubert.General.RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalDecaySecondCountable
  rationalDecayT2 rationalDecayNonarchimedean

/-- **Radical integrals of discrete-series coefficients vanish.** Let `A` be square
integrable modulo the image `A_G(F)` of a split component, and let `U` be the unipotent
radical of a proper standard parabolic. If every coefficient `u ↦ ℓ(A(u) v)` is integrable
on `U`, then all these integrals vanish. -/
theorem integral_unipotent_coefficient_eq_zero (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
      (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
      IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
          hs.isCentralSplitTorus.isCentral.range_le_center A.representation mu →
      ∀ (I : Finset (SimpleRoot i ν)), rootSet i ν I ≠ simpleRelativeRoots i ν →
      ∀ (muU : Measure (standardUnipotentPoints i ν (rootSet i ν I))) [muU.IsHaarMeasure],
        (∀ (v : A) (ℓ : SmoothDual A.representation),
          Integrable (fun u : standardUnipotentPoints i ν (rootSet i ν I) =>
            ℓ.val (A.representation (u : rationalPoints G) v)) muU) →
        ∀ (v : A) (ℓ : SmoothDual A.representation),
          ∫ u : standardUnipotentPoints i ν (rootSet i ν I),
            ℓ.val (A.representation (u : rationalPoints G) v) ∂muU = 0 := by
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  have : BorelSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := ⟨rfl⟩
  intro mu _ A hsq I hI muU _ hint v ℓ
  have hC := hs.isCentralSplitTorus.isCentral.range_le_center
  have : mu.IsInvInvariant := (rationalSplitCentralQuotientHaar_invariant hG s hs mu).2
  have hsq' : IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range hC
      A.contragredient.representation mu :=
    IsSquareIntegrableModCentralSubgroup.smoothContragredient _ hC mu
      (rationalPoint_compactOpenCofinal F G) hsq
  -- a standard cocharacter for the proper root subset
  have hstd := standardCocharacter F G hG S i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)
  obtain ⟨ζ, hζ⟩ := hstd.1
  have hcomp := hstd.2 ζ hζ
  have hdec := isSemidirectDecomposition_of_standardCocharacterStatement i ν standardCocharacter
    hG hi hν
  have hU : ∀ J : Finset (SimpleRoot i ν),
      IsClosed (unipotent i ν J : Set (rationalPoints G)) :=
    fun J => isClosed_unipotent_of_isNonarchimedeanLocalField i ν J
  have : LocallyCompactSpace (standardUnipotentPoints i ν (rootSet i ν I)) :=
    (hU I).locallyCompactSpace
  have : SecondCountableTopology (standardUnipotentPoints i ν (rootSet i ν I)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : TopologicalSpace.MetrizableSpace (standardUnipotentPoints i ν (rootSet i ν I)) :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  have : muU.Regular :=
    MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure muU
  have : muU.IsMulRightInvariant :=
    RepresentedParabolic.isMulRightInvariant_of_forall_isCompact_subgroup muU
      (standardUnipotentPoints_isLimitOfCompactSubgroups i ν (rootSet i ν I) hG ⟨ζ, hζ⟩)
  -- strict normalized Jacquet exponents of `A` and of its contragredient
  have hstrict₁ := hasStrictNormalizedJacquetExponents_universeLift hG hi hν hs mu A hsq
  have hstrict₂ := hasStrictNormalizedJacquetExponents_universeLift hG hi hν hs mu
    A.contragredient hsq'
  -- a contracting central direction of the standard Levi
  have hzero : ∀ β ∈ I, simpleRootPairing i ν β ζ = 0 := fun β hβ =>
    hζ.2.1 β.1 ((val_mem_rootSet i ν I β).mpr hβ)
  have hnonneg : ∀ β, 0 ≤ simpleRootPairing i ν β ζ := by
    intro β
    by_cases hβ : β.1 ∈ rootSet i ν I
    · exact (hζ.2.1 β.1 hβ).ge
    · exact (hζ.2.2 β.1 β.2 hβ).le
  have hpos : ∃ β, 0 < simpleRootPairing i ν β ζ := by
    obtain ⟨α, hα, hαI⟩ := Set.exists_of_ssubset
      (Set.ssubset_iff_subset_ne.mpr ⟨rootSet_subset i ν I, hI⟩)
    exact ⟨⟨α, hα⟩, hζ.2.2 α hα hαI⟩
  obtain ⟨z₁, hz₁, h₁⟩ := rationalLatticeStrictExponent F G hG S i hi ν hν standardCocharacter
    hU (SmoothRep.universeLift.{u + 1} A) hstrict₁ I ζ hzero hnonneg hpos
  obtain ⟨z₂, hz₂, h₂⟩ := rationalLatticeStrictExponent F G hG S i hi ν hν standardCocharacter
    hU (SmoothRep.universeLift.{u + 1} A.contragredient) hstrict₂ I ζ hzero hnonneg hpos
  have hz : z₂ = z₁ := Subtype.ext (Subtype.ext (hz₂.trans hz₁.symm))
  subst hz
  -- admissibility of both normalized Jacquet modules
  obtain ⟨g, hBasis⟩ := RationalPointFamily.dynamic_hasOppositeIwahoriContractionBasis G hG
    (CommGroupScheme.groupHom ζ ≫ i)
  have hBasis' := hBasis.hasIwahoriContractionBasis
  rw [← hcomp.2.2, ← hcomp.2.1] at hBasis'
  have hadm₁ := isAdmissible_jacquetFunctor_obj_of_iwahoriContraction (hdec I) (hU I) _ hBasis'
    (SmoothRep.universeLift.{u + 1} A) ((SmoothRep.isAdmissible_universeLift_iff A).mpr hsq.1)
  have hadm₂ := isAdmissible_jacquetFunctor_obj_of_iwahoriContraction (hdec I) (hU I) _ hBasis'
    (SmoothRep.universeLift.{u + 1} A.contragredient)
    ((SmoothRep.isAdmissible_universeLift_iff A.contragredient).mpr hsq'.1)
  exact radicalPairing_eq_zero_of_strict (levi i ν I) (hU I) (hdec I).levi_le_normalizer
    (p := liftedEvaluation.{u, uV, u + 1} A)
    (fun x y => hint ((SmoothRep.universeLiftEquiv.{u + 1} A).symm x)
      ((SmoothRep.universeLiftEquiv.{u + 1} A.contragredient).symm y))
    (liftedEvaluation_invariant A) hadm₁ hadm₂ z₂ h₁ h₂
    (SmoothRep.universeLiftEquiv.{u + 1} A v)
    (SmoothRep.universeLiftEquiv.{u + 1} A.contragredient ℓ)

/-- **Coefficients of a discrete series are cuspidal.** Under the hypotheses of
`integral_unipotent_coefficient_eq_zero`, every element of the coefficient space of `A`
satisfies the integrable cuspidality condition along the radical `U` of a proper standard
parabolic: all two-sided translates are integrable on `U` with integral zero. -/
theorem isIntegrableUnipotentCuspidal_coefficientTensorMap (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
      (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
      IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
          hs.isCentralSplitTorus.isCentral.range_le_center A.representation mu →
      ∀ (I : Finset (SimpleRoot i ν)), rootSet i ν I ≠ simpleRelativeRoots i ν →
      ∀ (muU : Measure (standardUnipotentPoints i ν (rootSet i ν I))) [muU.IsHaarMeasure],
        (∀ (v : A) (ℓ : SmoothDual A.representation),
          Integrable (fun u : standardUnipotentPoints i ν (rootSet i ν I) =>
            ℓ.val (A.representation (u : rationalPoints G) v)) muU) →
        ∀ t : CoefficientTensor A,
          IsIntegrableUnipotentCuspidal muU (coefficientTensorMap A t : rationalPoints G → ℂ) := by
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ A hsq I hI muU _ hint t
  have key : ∀ (v : A) (ℓ : SmoothDual A.representation),
      IsIntegrableUnipotentCuspidal muU
        (coefficientTensorMap A (v ⊗ₜ[ℂ] ℓ) : rationalPoints G → ℂ) := by
    intro v ℓ x y
    have hf : ∀ u : standardUnipotentPoints i ν (rootSet i ν I),
        (coefficientTensorMap A (v ⊗ₜ[ℂ] ℓ) : rationalPoints G → ℂ) (x * u * y) =
          ((smoothContragredient A.representation x⁻¹) ℓ).val
            (A.representation (u : rationalPoints G) (A.representation y v)) := by
      intro u
      change ℓ.val (A.representation (x * u * y) v) =
        ℓ.val (A.representation x⁻¹⁻¹ (A.representation u (A.representation y v)))
      rw [inv_inv, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    simp_rw [hf]
    exact ⟨hint _ _, integral_unipotent_coefficient_eq_zero hG hi hν hs mu A hsq I hI muU hint
      _ _⟩
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ => exact key v ℓ
  | add t₁ t₂ h₁ h₂ =>
    rw [map_add, LocallyConstant.coe_add]
    exact (integrableUnipotentCuspidalSubmodule muU).add_mem h₁ h₂

/-- The coefficient space `A(π)` of a discrete series lies in the integrable cuspidal kernel
of the radical of every proper standard parabolic, given integrability of the coefficients. -/
theorem coefficientFunctionSpace_le_integrableUnipotentCuspidalSubmodule
    (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {s : T.toGrp ⟶ G}
    (hs : IsSplitComponent s) :
    letI := (rationalPoints.map s).range.normal_of_le_center
      hs.isCentralSplitTorus.isCentral.range_le_center
    letI : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
    ∀ (mu : Measure (rationalPoints G ⧸ (rationalPoints.map s).range)) [mu.IsHaarMeasure]
      (A : SmoothRep.{0, u, uV} ℂ (rationalPoints G)),
      IsSquareIntegrableModCentralSubgroup (rationalPoints.map s).range
          hs.isCentralSplitTorus.isCentral.range_le_center A.representation mu →
      ∀ (I : Finset (SimpleRoot i ν)), rootSet i ν I ≠ simpleRelativeRoots i ν →
      ∀ (muU : Measure (standardUnipotentPoints i ν (rootSet i ν I))) [muU.IsHaarMeasure],
        (∀ (v : A) (ℓ : SmoothDual A.representation),
          Integrable (fun u : standardUnipotentPoints i ν (rootSet i ν I) =>
            ℓ.val (A.representation (u : rationalPoints G) v)) muU) →
        coefficientFunctionSpace A ≤ integrableUnipotentCuspidalSubmodule muU := by
  let := (rationalPoints.map s).range.normal_of_le_center
    hs.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints G ⧸ (rationalPoints.map s).range) := borel _
  intro mu _ A hsq I hI muU _ hint
  refine iSup_le fun ℓ => ?_
  rintro _ ⟨v, rfl⟩
  exact isIntegrableUnipotentCuspidal_coefficientTensorMap hG hi hν hs mu A hsq I hI muU hint
    (v ⊗ₜ[ℂ] ℓ)

end Rational

end Langlands.HarishChandraSchwartz.DiscreteConstantTerm
