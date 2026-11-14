import Langlands.Representation.Conductor.SphericalHecke
import Langlands.Representation.Conductor.SphericalCentral
import Langlands.Representation.Conductor.UnramifiedPrincipalSeries
import Langlands.Representation.Conductor.EssentialExistenceReduction
import Langlands.Representation.RankinSelberg.UnramifiedRecursionUniqueness
import Langlands.Representation.RankinSelberg.UnramifiedWhittakerCells
import Langlands.Representation.RankinSelberg.SphericalTorusRecursion
import Langlands.Representation.Unramified.PrincipalSeriesHecke
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement

/-!
# Spherical Whittaker functions of unramified principal series over every local field

Over an arbitrary field with a valuation, a uniformizing element `ϖ` and residue lifts
`σ : Λ → F` with `|Λ| = q`, a `θ`-equivariant right `GL_(n+1)(O)`-invariant function on
which the minuscule coset sums act by the eigenvalues of the Satake parameter `x`, and
the central element `ϖ⁻¹` by `(∏ x_i)⁻¹`, is its value at `1` times the explicit spherical
Whittaker function `W(·; x)` (Shintani's uniqueness). Applied to the coefficient
functions of the normalized spherical section of the unramified principal series `I(z)`
over a nonarchimedean local field, it gives
`ℓ(I(z)(g) f₀) = ℓ(f₀) W(g; z; ψ̄)` for every inverse-character functional `ℓ`.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa Langlands.GeneralLinear.Spherical
open Langlands.Unramified.MinusculeCosets Langlands.RankinSelberg.UnramifiedWhittaker
open Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.Whittaker.UpperUnipotentCharacter (adjacentUnit)
open scoped BigOperators

universe uF uΓ uΛ uV

section Functions

variable {F : Type uF} [Field F] {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation F Γ₀} {n : ℕ} {ϖ : Fˣ} {θ : upperUnipotent (n + 1) F →* ℂˣ}
variable {Λ : Type uΛ} [Fintype Λ]

/-- A `θ`-equivariant right `GL_(n+1)(O)`-invariant function on which every standard
minuscule coset sum and the central element `ϖ⁻¹` act by scalars, and which vanishes
at the identity, vanishes identically. -/
theorem eq_zero_of_minusculeRelations (hϖ : IsUniformizingElement v ϖ)
    (hΛ : 0 < Fintype.card Λ) (σ : Λ → F) (hσ : ∀ x, σ x ∈ v.integer)
    (hθK : IsIntegrallyTrivial v θ)
    (hθ : ∀ i : Fin n, ∃ x : F, v x * v (ϖ : F) ≤ 1 ∧ θ (adjacentUnit i x) ≠ 1)
    {f : Matrix.GeneralLinearGroup (Fin (n + 1)) F → ℂ}
    (hf : ∀ (u : upperUnipotent (n + 1) F) g, f (u.val * g) = (θ u : ℂ) * f g)
    (hfK : ∀ g, ∀ k ∈ integralSubgroup v.integer n, f (g * k) = f g)
    (hrec : ∀ k : ℕ, 1 ≤ k → k ≤ n + 1 → ∃ c : ℂ, ∀ g,
      ∑ α : CosetIndex Λ (n + 1) k, f (g * labelledRep ϖ σ α) = c * f g)
    (hcent : ∃ c : ℂ, ∀ g,
      f (g * torus ϖ (fun _ : Fin (n + 1) => (-1 : ℤ))) = c * f g)
    (h1 : f 1 = 0) : f = 0 := by
  classical
  let d : (Fin (n + 1) → ℤ) → ℂ := fun lam => f (torus ϖ lam)
  have hanti : ∀ lam, ¬ Antitone lam → d lam = 0 := fun lam hlam =>
    eval_torus_eq_zero_of_not_antitone hϖ hf hfK hθ hlam
  have hd0 : d 0 = 0 := by
    have : torus ϖ (0 : Fin (n + 1) → ℤ) = 1 := by
      rw [torus]
      simp only [Pi.zero_apply, zpow_zero]
      exact map_one diagonalUnits
    change f (torus ϖ 0) = 0
    rw [this]
    exact h1
  have hd : SatisfiesHeckeRecursion
      (fun S => ((Fintype.card Λ : ℂ) ^ Fintype.card (RadicalPairs S))) d := by
    intro lam hlam k hk1 hkm
    obtain ⟨c, hc⟩ := hrec k hk1 hkm
    refine ⟨c, ?_⟩
    rw [← hc (torus ϖ lam), sum_eval_torus_mul_labelledRep hϖ.1.le hθK hf hσ hlam.1 k]
  have hpow : ∀ k, k ≤ n + 1 →
      ((Fintype.card Λ : ℂ) ^
        Fintype.card (RadicalPairs (initialSegment (n + 1) k))) ≠ 0 := by
    intro k _
    apply pow_ne_zero
    exact_mod_cast hΛ.ne'
  have hpart := eq_zero_of_satisfiesHeckeRecursion hpow hd hanti hd0
  obtain ⟨c', hc'⟩ := hcent
  have hshift : ∀ lam : Fin (n + 1) → ℤ, d (lam + fun _ => -1) = c' * d lam := by
    intro lam
    change f (torus ϖ (lam + fun _ => -1)) = c' * f (torus ϖ lam)
    rw [← torus_mul_torus, hc']
  have hshiftN : ∀ (j : ℕ) (lam : Fin (n + 1) → ℤ),
      d (lam + fun _ => -(j : ℤ)) = c' ^ j * d lam := by
    intro j
    induction j with
    | zero =>
      intro lam
      simp only [Nat.cast_zero, neg_zero, pow_zero, one_mul]
      congr 1
      funext i
      simp
    | succ j ih =>
      intro lam
      have : (lam + fun _ => -((j + 1 : ℕ) : ℤ)) =
          (lam + fun _ => -(j : ℤ)) + fun _ => -1 := by
        funext i
        simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one]
        ring
      rw [this, hshift, ih, pow_succ]
      ring
  have hall : ∀ lam, d lam = 0 := by
    intro lam
    by_cases hlam : Antitone lam
    · set N : ℕ := (-lam (Fin.last n)).toNat
      have hpos : IsPartitionExponent (lam + fun _ => (N : ℤ)) := by
        refine ⟨fun i j hij => ?_, fun i => ?_⟩
        · simp only [Pi.add_apply]
          have := hlam hij
          omega
        · simp only [Pi.add_apply]
          have h1 := hlam (Fin.le_last i)
          have h2 : -lam (Fin.last n) ≤ (N : ℤ) := Int.self_le_toNat _
          omega
      have := hshiftN N (lam + fun _ => (N : ℤ))
      have heq : ((lam + fun _ => (N : ℤ)) + fun _ => -(N : ℤ)) = lam := by
        funext i
        simp
      rw [heq, hpart _ hpos, mul_zero] at this
      exact this
    · exact hanti lam hlam
  funext g
  obtain ⟨k, hk, hg⟩ := exists_eq_unipotentPart hϖ g
  rw [hg, hfK _ _ hk, hf, Pi.zero_apply]
  have := hall (exponent hϖ g)
  change f (torus ϖ (exponent hϖ g)) = 0 at this
  rw [this, mul_zero]

/-- Over an arbitrary valued field, the explicit spherical Whittaker function satisfies
the normalized minuscule Hecke eigenrelations with Satake parameter `x`. -/
theorem sum_sphericalWhittaker_mul_labelledRep (hϖ : IsUniformizingElement v ϖ) {q : ℕ}
    (hq : 0 < q) (hcard : Fintype.card Λ = q) (σ : Λ → F) (hσ : ∀ x, σ x ∈ v.integer)
    (hinj : ∀ x y, v (σ x - σ y) < 1 → x = y)
    (hsurj : ∀ z ∈ v.integer, ∃ x, v (z - σ x) < 1)
    (hθK : IsIntegrallyTrivial v θ)
    (hθ : ∀ i : Fin n, ∃ x : F, v x * v (ϖ : F) ≤ 1 ∧ θ (adjacentUnit i x) ≠ 1)
    (x : Fin (n + 1) → ℂˣ) (k : ℕ) (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    ∑ α : CosetIndex Λ (n + 1) k, sphericalWhittaker hϖ θ q x (g * labelledRep ϖ σ α) =
      ((Real.sqrt (q : ℝ) : ℂ) ^ (k * (n + 1 - k)) *
        Langlands.Unramified.elementaryCoefficient
          (Langlands.Unramified.Eigenvalues.ofTuple x) k) *
        sphericalWhittaker hϖ θ q x g := by
  have h := congrArg (symmetricTorusEvaluation (Fin (n + 1)) ℂ x)
    (sphericalWhittakerMinusculeSum_eq hϖ θ q hq hcard hθK hθ σ hσ hinj hsurj k g)
  simpa only [sphericalWhittakerMinusculeSum, map_sum, map_mul,
    symmetricTorusEvaluation_sphericalWhittakerPolynomial,
    symmetricTorusEvaluation_heckeScalar] using h

/-- The central element `ϖ⁻¹` acts on the explicit spherical Whittaker function by
`(∏ x_i)⁻¹`. -/
theorem sphericalWhittaker_mul_torus_neg_one (hϖ : IsUniformizingElement v ϖ) (q : ℕ)
    (hθK : IsIntegrallyTrivial v θ) (x : Fin (n + 1) → ℂˣ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    sphericalWhittaker hϖ θ q x (g * torus ϖ (fun _ : Fin (n + 1) => (-1 : ℤ))) =
      (∏ i, (x i : ℂ))⁻¹ * sphericalWhittaker hϖ θ q x g := by
  have h := congrArg (symmetricTorusEvaluation (Fin (n + 1)) ℂ x)
    (sphericalWhittakerPolynomial_mul_torus_const hϖ θ q hθK g (-1))
  rw [map_mul, symmetricTorusEvaluation_sphericalWhittakerPolynomial,
    symmetricTorusEvaluation_sphericalWhittakerPolynomial] at h
  rw [h]
  congr 1
  have hD := congrArg Units.val
    (map_zpow (Units.map (symmetricTorusEvaluation (Fin (n + 1)) ℂ x).toMonoidHom)
      (symmetricTorusDeterminantUnit (Fin (n + 1)) ℂ) (-1))
  rw [symmetricTorusEvaluation_determinantUnit] at hD
  simpa using hD

/-- Shintani's uniqueness over an arbitrary valued field: a `θ`-equivariant right
`GL_(n+1)(O)`-invariant function on which the standard minuscule coset sums act by the
normalized Hecke eigenvalues of `x` and the central element `ϖ⁻¹` by `(∏ x_i)⁻¹` is its
value at `1` times the explicit spherical Whittaker function. -/
theorem eq_smul_sphericalWhittaker (hϖ : IsUniformizingElement v ϖ) {q : ℕ}
    (hq : 0 < q) (hcard : Fintype.card Λ = q) (σ : Λ → F) (hσ : ∀ x, σ x ∈ v.integer)
    (hinj : ∀ x y, v (σ x - σ y) < 1 → x = y)
    (hsurj : ∀ z ∈ v.integer, ∃ x, v (z - σ x) < 1)
    (hθK : IsIntegrallyTrivial v θ)
    (hθ : ∀ i : Fin n, ∃ x : F, v x * v (ϖ : F) ≤ 1 ∧ θ (adjacentUnit i x) ≠ 1)
    (x : Fin (n + 1) → ℂˣ)
    {f : Matrix.GeneralLinearGroup (Fin (n + 1)) F → ℂ}
    (hf : ∀ (u : upperUnipotent (n + 1) F) g, f (u.val * g) = (θ u : ℂ) * f g)
    (hfK : ∀ g, ∀ k ∈ integralSubgroup v.integer n, f (g * k) = f g)
    (hrec : ∀ k : ℕ, 1 ≤ k → k ≤ n + 1 → ∀ g,
      ∑ α : CosetIndex Λ (n + 1) k, f (g * labelledRep ϖ σ α) =
        ((Real.sqrt (q : ℝ) : ℂ) ^ (k * (n + 1 - k)) *
          Langlands.Unramified.elementaryCoefficient
            (Langlands.Unramified.Eigenvalues.ofTuple x) k) * f g)
    (hcent : ∀ g, f (g * torus ϖ (fun _ : Fin (n + 1) => (-1 : ℤ))) =
      (∏ i, (x i : ℂ))⁻¹ * f g) :
    f = f 1 • sphericalWhittaker hϖ θ q x := by
  set W := sphericalWhittaker hϖ θ q x with hWdef
  have hWmem := sphericalWhittaker_mem hϖ q x hθK
  have hWu : ∀ (u : upperUnipotent (n + 1) F) g, W (u.val * g) = (θ u : ℂ) * W g :=
    fun u g => hWmem u g
  have hΛ : 0 < Fintype.card Λ := hcard ▸ hq
  have h0 := eq_zero_of_minusculeRelations (f := f - f 1 • W) hϖ hΛ σ hσ hθK hθ
    (fun u g => by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hf u g, hWu u g]
      ring)
    (fun g k hk => by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hfK g k hk,
        hWdef, sphericalWhittaker_mul_integral hϖ q x hθK g hk])
    (fun k hk1 hkm => ⟨(Real.sqrt (q : ℝ) : ℂ) ^ (k * (n + 1 - k)) *
        Langlands.Unramified.elementaryCoefficient
          (Langlands.Unramified.Eigenvalues.ofTuple x) k, fun g => by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hrec k hk1 hkm g, hWdef,
        sum_sphericalWhittaker_mul_labelledRep hϖ hq hcard σ hσ hinj hsurj hθK hθ x k g]
      ring⟩)
    ⟨(∏ i, (x i : ℂ))⁻¹, fun g => by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hcent g, hWdef,
        sphericalWhittaker_mul_torus_neg_one hϖ q hθK x g]
      ring⟩
    (by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hWdef,
        sphericalWhittaker_one hϖ q x hθK, mul_one, sub_self])
  exact sub_eq_zero.mp h0

end Functions

section Representation

variable {F : Type uF} [Field F] {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation F Γ₀} {n : ℕ} {ϖ : Fˣ} {θ : upperUnipotent (n + 1) F →* ℂˣ}
variable {Λ : Type uΛ} [Fintype Λ]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Shintani's uniqueness for coefficients: if `w` is fixed by `GL_(n+1)(O)`, the standard
minuscule coset sums act on `w` by the normalized Hecke eigenvalues of `x`, and `ϖ⁻¹` acts
on `w` by `(∏ x_i)⁻¹`, then the coefficient of `w` for any `θ`-functional `ℓ` is
`ℓ(w)` times the explicit spherical Whittaker function. -/
theorem coefficientMap_eq_smul_sphericalWhittaker (hϖ : IsUniformizingElement v ϖ) {q : ℕ}
    (hq : 0 < q) (hcard : Fintype.card Λ = q) (σ : Λ → F) (hσ : ∀ x, σ x ∈ v.integer)
    (hinj : ∀ x y, v (σ x - σ y) < 1 → x = y)
    (hsurj : ∀ z ∈ v.integer, ∃ x, v (z - σ x) < 1)
    (hθK : IsIntegrallyTrivial v θ)
    (hθ : ∀ i : Fin n, ∃ x : F, v x * v (ϖ : F) ≤ 1 ∧ θ (adjacentUnit i x) ≠ 1)
    (x : Fin (n + 1) → ℂˣ)
    (ρ : Representation ℂ (Matrix.GeneralLinearGroup (Fin (n + 1)) F) V)
    (ℓ : functionals (upperUnipotent (n + 1) F) θ ρ) (w : V)
    (hwK : ∀ k ∈ integralSubgroup v.integer n, ρ k w = w)
    (hwrec : ∀ k : ℕ, 1 ≤ k → k ≤ n + 1 →
      ∑ α : CosetIndex Λ (n + 1) k, ρ (labelledRep ϖ σ α) w =
        ((Real.sqrt (q : ℝ) : ℂ) ^ (k * (n + 1 - k)) *
          Langlands.Unramified.elementaryCoefficient
            (Langlands.Unramified.Eigenvalues.ofTuple x) k) • w)
    (hwcent : ρ (torus ϖ (fun _ : Fin (n + 1) => (-1 : ℤ))) w = (∏ i, (x i : ℂ))⁻¹ • w) :
    (coefficientMap ρ ℓ w).val = ℓ.val w • sphericalWhittaker hϖ θ q x := by
  have hval : ∀ g, (coefficientMap ρ ℓ w).val g = ℓ.val (ρ g w) := fun g => rfl
  have h := eq_smul_sphericalWhittaker (f := (coefficientMap ρ ℓ w).val) hϖ hq hcard σ hσ
    hinj hsurj hθK hθ x
    (fun u g => (coefficientMap ρ ℓ w).property u g)
    (fun g k hk => by rw [hval, hval, map_mul, Module.End.mul_apply, hwK k hk])
    (fun k hk1 hkm g => by
      simp only [hval, map_mul, Module.End.mul_apply]
      rw [← map_sum ℓ.val, ← map_sum (ρ g), hwrec k hk1 hkm, map_smul, map_smul, smul_eq_mul])
    (fun g => by
      rw [hval, hval, map_mul, Module.End.mul_apply, hwcent, map_smul, map_smul, smul_eq_mul])
  rwa [hval 1, map_one, Module.End.one_apply] at h

end Representation

section PrincipalSeries

open UnramifiedPrincipalSeries

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ) (n : ℕ)
variable {q : ℕ} (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ)

/-- Evaluation of principal-series functions at a point, as a linear functional. -/
def valueLinear (g : Langlands.GeneralLinear (n + 1) F) :
    PrincipalSeries hϖ n hq z →ₗ[ℂ] ℂ where
  toFun f := value hϖ n f g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem value_sum {ι : Type*} (s : Finset ι) (f : ι → PrincipalSeries hϖ n hq z)
    (g : Langlands.GeneralLinear (n + 1) F) :
    value hϖ n (∑ i ∈ s, f i) g = ∑ i ∈ s, value hϖ n (f i) g :=
  map_sum (valueLinear hϖ n hq z g) f s

theorem value_smul (c : ℂ) (f : PrincipalSeries hϖ n hq z)
    (g : Langlands.GeneralLinear (n + 1) F) :
    value hϖ n (c • f) g = c * value hϖ n f g := rfl

theorem ext_value {f f' : PrincipalSeries hϖ n hq z}
    (h : ∀ g, value hϖ n f g = value hϖ n f' g) : f = f' := by
  apply Subtype.ext
  apply Subtype.ext
  exact funext h

theorem value_borel_mul (f : PrincipalSeries hϖ n hq z) (b : Borel (F := F) n)
    (g : Langlands.GeneralLinear (n + 1) F) :
    value hϖ n f (b.val * g) = (normalizedCharacter hϖ n hq z b : ℂ) * value hϖ n f g := by
  rw [covariance, normalizedCharacter_apply]

/-- A right `GL_(n+1)(O)`-invariant function with the normalized Borel covariance is its
value at `1` times the normalized spherical section. -/
theorem eq_mul_sphericalSection_of_covariance
    {f : Langlands.GeneralLinear (n + 1) F → ℂ}
    (hcov : ∀ (b : Borel (F := F) n) g,
      f (b.val * g) = (normalizedCharacter hϖ n hq z b : ℂ) * f g)
    (hK : ∀ g, ∀ k ∈ integralSubgroup (ValuativeRel.valuation F).integer n, f (g * k) = f g)
    (g : Langlands.GeneralLinear (n + 1) F) :
    f g = f 1 * value hϖ n (sphericalSection hϖ n hq z) g := by
  obtain ⟨b, k, rfl⟩ := exists_borel_integral n g
  rw [hK _ _ k.property, sphericalSection_borel_mul_integral hϖ n hq z b k.property]
  have h1 := hcov b 1
  rw [mul_one] at h1
  rw [h1, mul_comm]

/-- The normalized spherical section at a labelled minuscule representative. -/
theorem sphericalSection_labelledRep {Λ : Type*} (σ : Λ → F) {k : ℕ}
    (α : CosetIndex Λ (n + 1) k) :
    value hϖ n (sphericalSection hϖ n hq z) (labelledRep ϖ σ α) =
      Spherical.halfModulus q (subsetExponent α.1.1) * ∏ j ∈ α.1.1, (z j : ℂ) := by
  classical
  let b : Borel (F := F) n := ⟨radicalElement α.1.1 (liftCoeff σ α.1.1 α.2),
    (radicalElement_mem_upperUnipotent _ _).1⟩
  have hb : ∀ i, diagonalUnit n i b = 1 := fun i =>
    Units.ext ((radicalElement_mem_upperUnipotent α.1.1 (liftCoeff σ α.1.1 α.2)).2 i)
  have hmod : (halfModulusCharacter hϖ n hq b : ℂ) = 1 := by
    rw [halfModulusCharacter_apply]
    simp [hb]
  change value hϖ n _ (b.val * subsetTorus ϖ α.1.1) = _
  rw [sphericalSection_covariance, sphericalSection_torus, hmod]
  simp only [hb, map_one, Units.val_one, Finset.prod_const_one, one_mul]
  congr 1
  have hz : ∀ i, (z i : ℂ) ^ subsetExponent α.1.1 i = if i ∈ α.1.1 then (z i : ℂ) else 1 := by
    intro i
    by_cases h : i ∈ α.1.1 <;> simp [subsetExponent, h]
  rw [Finset.prod_congr rfl (fun i _ => hz i), Fintype.prod_ite_mem]

/-- The sum of the normalized spherical section over the labelled representatives of
`K t_k K` is the normalized Hecke eigenvalue of `z`. -/
theorem sum_sphericalSection_labelledRep {Λ : Type*} [Fintype Λ]
    (hcard : Fintype.card Λ = q) (σ : Λ → F) (k : ℕ) :
    ∑ α : CosetIndex Λ (n + 1) k,
        value hϖ n (sphericalSection hϖ n hq z) (labelledRep ϖ σ α) =
      (Real.sqrt (q : ℝ) : ℂ) ^ (k * (n + 1 - k)) *
        Langlands.Unramified.elementaryCoefficient
          (Langlands.Unramified.Eigenvalues.ofTuple z) k := by
  classical
  simp only [sphericalSection_labelledRep]
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, hcard, nsmul_eq_mul]
  rw [Langlands.Unramified.elementaryCoefficient_ofTuple, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have key := Spherical.radical_mul_halfModulus q (residueCardinality_pos hq) S.1
  rw [S.2] at key
  push_cast
  rw [← mul_assoc, key]

/-- On the normalized spherical section, the sum of the translates by the labelled
representatives of `K t_k K` is the normalized Hecke eigenvalue of `z`. -/
theorem sum_principalSeries_labelledRep {Λ : Type*} [Fintype Λ]
    (hcard : Fintype.card Λ = q) (σ : Λ → F)
    (hσ : ∀ x, σ x ∈ (ValuativeRel.valuation F).integer)
    (hinj : ∀ x y, ValuativeRel.valuation F (σ x - σ y) < 1 → x = y)
    (hsurj : ∀ z ∈ (ValuativeRel.valuation F).integer,
      ∃ x, ValuativeRel.valuation F (z - σ x) < 1) (k : ℕ) :
    ∑ α : CosetIndex Λ (n + 1) k,
        principalSeries hϖ n hq z (labelledRep ϖ σ α) (sphericalSection hϖ n hq z) =
      ((Real.sqrt (q : ℝ) : ℂ) ^ (k * (n + 1 - k)) *
        Langlands.Unramified.elementaryCoefficient
          (Langlands.Unramified.Eigenvalues.ofTuple z) k) • sphericalSection hϖ n hq z := by
  apply ext_value hϖ n hq z
  intro g
  rw [value_sum, value_smul, ← sum_sphericalSection_labelledRep hϖ n hq z hcard σ k]
  simp only [UnramifiedPrincipalSeries.rightTranslation]
  let f0 := value hϖ n (sphericalSection hϖ n hq z)
  let h : Langlands.GeneralLinear (n + 1) F → ℂ := minusculeSumOperator ℂ ϖ σ k f0
  have hcov : ∀ (b : Borel (F := F) n) g,
      h (b.val * g) = (normalizedCharacter hϖ n hq z b : ℂ) * h g := by
    intro b g
    simp only [h, minusculeSumOperator_apply, Finset.mul_sum, mul_assoc, f0,
      value_borel_mul]
  have hK : ∀ g, ∀ c ∈ integralSubgroup (ValuativeRel.valuation F).integer n,
      h (g * c) = h g := fun g c hc =>
    minusculeSumOperator_mul_integral hϖ σ hσ hinj hsurj k f0
      (fun g c hc => sphericalSection_mul_integral hϖ n hq z g hc) g hc
  have hg := eq_mul_sphericalSection_of_covariance hϖ n hq z hcov hK g
  simp only [h, minusculeSumOperator_apply, one_mul, f0] at hg
  rw [hg, mul_comm]

/-- The central element `ϖ⁻¹` acts on the unramified principal series by `(∏ z_i)⁻¹`. -/
theorem principalSeries_torus_neg_one (f : PrincipalSeries hϖ n hq z) :
    principalSeries hϖ n hq z (torus ϖ (fun _ : Fin (n + 1) => (-1 : ℤ))) f =
      (∏ i, (z i : ℂ))⁻¹ • f := by
  apply ext_value hϖ n hq z
  intro g
  rw [UnramifiedPrincipalSeries.rightTranslation, value_smul, ← torus_const_commute]
  change value hϖ n f ((torusBorel n ϖ (fun _ => -1)).val * g) = _
  have hhalf : Spherical.halfModulus q (fun _ : Fin (n + 1) => (-1 : ℤ)) = 1 := by
    have h := halfModulus_add_const q (0 : Fin (n + 1) → ℤ) (-1)
    simp only [Pi.zero_apply, zero_add] at h
    rw [h, Spherical.halfModulus_zero]
  rw [covariance, halfModulusCharacter_torus, hhalf, one_mul]
  congr 1
  have hord : ord hϖ ϖ⁻¹ = -1 := by
    have h := ord_zpow hϖ ϖ (-1)
    rw [zpow_neg_one, ord_uniformizer, mul_one] at h
    exact h
  simp [diagonalUnit_torusBorel, character_apply, hord, Finset.prod_inv_distrib]

/-- The central element `-1` acts trivially on the unramified principal series. -/
theorem principalSeries_neg_one (f : PrincipalSeries hϖ n hq z) :
    principalSeries hϖ n hq z (-1) f = f := by
  apply ext_value hϖ n hq z
  intro g
  let b : Borel (F := F) n := ⟨-1, by
    change (-(1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F)).IsUpperTriangular
    intro i j hij
    rw [Matrix.neg_apply, neg_eq_zero]
    exact Matrix.one_apply_ne (Ne.symm (ne_of_lt hij))⟩
  have hb : ∀ i, ord hϖ (diagonalUnit n i b) = 0 := by
    intro i
    rw [ord_eq_zero_iff]
    change ValuativeRel.valuation F (((-1 : Langlands.GeneralLinear (n + 1) F) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F) i i) = 1
    simp
  have hchar : (normalizedCharacter hϖ n hq z b : ℂ) = 1 := by
    rw [normalizedCharacter_apply, halfModulusCharacter_apply]
    simp [hb]
  rw [UnramifiedPrincipalSeries.rightTranslation, mul_neg_one, ← neg_one_mul]
  change value hϖ n f (b.val * g) = _
  rw [value_borel_mul, hchar, one_mul]

/-- The minus-one scalar of every Whittaker model of the unramified principal series is `1`. -/
theorem hasModelMinusOneScalar_principalSeries {θ : upperUnipotent (n + 1) F →* ℂˣ}
    (ℓ : functionals (upperUnipotent (n + 1) F) θ (principalSeries hϖ n hq z)) :
    Langlands.RankinSelberg.HasModelMinusOneScalar (principalSeries hϖ n hq z) ℓ 1 := by
  intro f g
  obtain ⟨w, hw⟩ := f.property
  rw [← hw]
  change ℓ.val (principalSeries hϖ n hq z ((-1) * g) w) =
    ((1 : ℂˣ) : ℂ) * ℓ.val (principalSeries hϖ n hq z g w)
  rw [Units.val_one, one_mul, neg_one_mul, ← mul_neg_one, map_mul, Module.End.mul_apply,
    principalSeries_neg_one]

/-- The coefficients of the normalized spherical section of the unramified principal
series `I(z)` for any inverse-character functional `ℓ` are `ℓ(f₀)` times Jacquet's
spherical function `W(·; z; ψ̄)`, over every nonarchimedean local field. -/
theorem coefficientMap_sphericalSection {ψ : UnitaryAdditiveCharacter F}
    (hψ : HasIntegerConductor ψ)
    (ℓ : glInverseFunctionals ψ n (principalSeries hϖ n hq z)) :
    (coefficientMap (principalSeries hϖ n hq z) ℓ (sphericalSection hϖ n hq z)).val =
      ℓ.val (sphericalSection hϖ n hq z) • (inverseSphericalWhittaker hψ.1 hϖ q z).val := by
  classical
  let _ : Fintype (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) :=
    Fintype.ofFinite _
  have hcard : Fintype.card (IsLocalRing.ResidueField (ValuativeRel.valuation F).integer) =
      q := by
    rw [hq, Nat.card_eq_fintype_card]
  exact coefficientMap_eq_smul_sphericalWhittaker hϖ (residueCardinality_pos hq) hcard
    residueClassLift residueClassLift_mem
    (fun _ _ hrt => residueClassLift_eq_of_lt_one hrt)
    (fun _ hz => exists_residueClassLift_lt_one hz)
    (isIntegrallyTrivial_inverseStandardCharacter hψ.1 n)
    (exists_adjacentUnit_ne_one hψ hϖ n) z (principalSeries hϖ n hq z) ℓ
    (sphericalSection hϖ n hq z)
    (fun k hk => sphericalSection_fixed hϖ n hq z hk)
    (fun k _ _ => sum_principalSeries_labelledRep hϖ n hq z hcard residueClassLift
      residueClassLift_mem (fun _ _ hrt => residueClassLift_eq_of_lt_one hrt)
      (fun _ hz => exists_residueClassLift_lt_one hz) k)
    (principalSeries_torus_neg_one hϖ n hq z _)

/-- Pointwise form of `coefficientMap_sphericalSection`. -/
theorem coefficientMap_sphericalSection_apply {ψ : UnitaryAdditiveCharacter F}
    (hψ : HasIntegerConductor ψ)
    (ℓ : glInverseFunctionals ψ n (principalSeries hϖ n hq z))
    (g : Langlands.GeneralLinear (n + 1) F) :
    (coefficientMap (principalSeries hϖ n hq z) ℓ (sphericalSection hϖ n hq z)).val g =
      ℓ.val (sphericalSection hϖ n hq z) * (inverseSphericalWhittaker hψ.1 hϖ q z).val g :=
  congrFun (coefficientMap_sphericalSection hϖ n hq z hψ ℓ) g

end PrincipalSeries

end Langlands.Conductor
