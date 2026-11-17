import Langlands.Representation.Archimedean.RealRotationFinitePropagation
import Langlands.Representation.Archimedean.RealTailMultiplierPolynomial
import Langlands.Representation.Archimedean.RealBlockFrobeniusMap
import Langlands.Representation.Archimedean.RealStandardFiltration

/-! # Finite propagation for polynomial Fourier multipliers on O(3) -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealPolynomialFourierPropagation

open Polynomial Complex RealKTypeCount RealBlockFourierFinite
open RealOrthogonalUncertainty RealRotationFinitePropagation
open RealOrthogonalUncertainty.IsModeDecomposition

local notation "K3" => Matrix.unitaryGroup (Fin 3) ℝ
local notation "G3" => Langlands.GeneralLinear 3 ℝ

theorem exists_degreeLE {f : G3 → ℂ} (hf : Continuous f)
    (hK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G3) (unitaryCompact ℝ 3)) :
    ∃ N, restrictLinear 3 f ∈ degreeLE 3 N := by
  have hfK : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ 3 =>
      Whittaker.rightTranslation ℂ G3 (k : G3) f)) := hK
  have hle : OrthogonalFinitePolynomial.translateSpan (restrictLinear 3 f) ≤
      (Submodule.span ℂ (Set.range fun k : unitaryCompact ℝ 3 =>
        Whittaker.rightTranslation ℂ G3 (k : G3) f)).map (restrictLinear 3) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨⟨Unitary.toUnits k, k.2⟩, rfl⟩, ?_⟩
    funext x
    show f (Unitary.toUnits x * Unitary.toUnits k) = f (Unitary.toUnits (x * k))
    rw [map_mul]
  have : FiniteDimensional ℂ (OrthogonalFinitePolynomial.translateSpan (restrictLinear 3 f)) :=
    Submodule.finiteDimensional_of_le hle
  exact RealKTypeCount.exists_mem_degreeLE
    (OrthogonalFinitePolynomial.mem_polynomialFunctions_of_finiteDimensional
      (hf.comp continuous_unitary_toUnits))

theorem proj_restrict_apply {N p : ℕ} (hp : p + 1 < 3) (m : ℤ)
    {f : G3 → ℂ} (hN : restrictLinear 3 f ∈ degreeLE 3 N) (x : K3) :
    ((proj N hp m ⟨restrictLinear 3 f, hN⟩ : degreeLE 3 N) : K3 → ℂ) x =
      (2 * (Real.pi : ℂ))⁻¹ * blockFourierCoefficient 3 p m f (Unitary.toUnits x) := by
  rw [proj_coe]
  change (2 * (Real.pi : ℂ))⁻¹ * coeff m (orb p (restrictLinear 3 f) x) = _
  have he : orb p (restrictLinear 3 f) x =
      fun θ => f (blockRotation 3 p θ * Unitary.toUnits x) := by
    funext θ
    rw [orb, restrictLinear_apply, toUnits_rot_mul]
  rw [he, ← blockFourierCoefficient_eq_coeff]

theorem proj_aeval {W : Type*} [AddCommGroup W] [Module ℂ W]
    {a : Module.End ℂ W} {π : ℤ → Module.End ℂ W} {S : Finset ℤ}
    (hM : IsModeDecomposition a π S) (Q : ℂ[X]) (m : ℤ) (v : W) :
    π m (aeval (-I • a) Q v) = Q.eval (m : ℂ) • π m v := by
  have hd : ∀ w : W, π m ((-I • a) w) = (m : ℂ) • π m w := by
    intro w
    rw [LinearMap.smul_apply, map_smul, hM.proj_apply, smul_smul]
    congr 1
    rw [← mul_assoc, neg_mul, I_mul_I]
    simp
  have hpow : ∀ (d : ℕ) (w : W),
      π m (((-I • a) ^ d) w) = (m : ℂ) ^ d • π m w := by
    intro d
    induction d with
    | zero => intro w; simp
    | succ d ih =>
        intro w
        rw [pow_succ', Module.End.mul_apply, hd, ih, smul_smul, pow_succ']
  rw [aeval_eq_sum_range, LinearMap.sum_apply, map_sum, eval_eq_sum_range]
  simp_rw [LinearMap.smul_apply, map_smul, hpow, smul_smul]
  rw [Finset.sum_smul]

theorem mode_bound_aeval_negI {W : Type*} [AddCommGroup W] [Module ℂ W]
    {a b c : Module.End ℂ W} {π : ℤ → Module.End ℂ W} {S : Finset ℤ}
    (hab : a * b - b * a = c) (hca : c * a - a * c = b)
    (hM : IsModeDecomposition a π S) {n : ℕ} {v : W}
    (hv : HasModeBound π n v) (Q : ℂ[X]) :
    HasModeBound π (n + Q.natDegree) (aeval (-I • b) Q v) := by
  have hh := mode_bound_aeval hab hca hM hv (Q.comp (C (-I) * X))
  have hdeg : (Q.comp (C (-I) * X)).natDegree = Q.natDegree := by
    rw [natDegree_comp, natDegree_C_mul (neg_ne_zero.mpr I_ne_zero), natDegree_X, mul_one]
  rw [hdeg, aeval_comp] at hh
  simpa only [map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
    one_mul] using hh

/-- Polynomial multipliers expand the adjacent compact Fourier window by at most their degree. -/
theorem propagation {p q : ℕ} (hpq : q = 0 ∧ p = 1 ∨ q = 1 ∧ p = 0)
    {f g : G3 → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G3) (unitaryCompact ℝ 3))
    (hgK : g ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G3) (unitaryCompact ℝ 3))
    (Q : ℂ[X])
    (hμ : ∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 p j g x =
        Q.eval (j : ℂ) * blockFourierCoefficient 3 p j f x)
    (n : ℕ)
    (hlow : ∀ x ∈ unitaryCompact ℝ 3, ∀ j : ℤ, (n : ℤ) ≤ |j| →
      blockFourierCoefficient 3 q j f x = 0) :
    ∀ x ∈ unitaryCompact ℝ 3, ∀ j : ℤ, ((n + Q.natDegree : ℕ) : ℤ) ≤ |j| →
      blockFourierCoefficient 3 q j g x = 0 := by
  have hp : p + 1 < 3 := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hq : q + 1 < 3 := by rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  obtain ⟨Nf, hNf⟩ := exists_degreeLE hf hfK
  obtain ⟨Ng, hNg⟩ := exists_degreeLE hg hgK
  let N := max Nf Ng
  have hNf' : restrictLinear 3 f ∈ degreeLE 3 N :=
    degreeLE_mono (le_max_left Nf Ng) hNf
  have hNg' : restrictLinear 3 g ∈ degreeLE 3 N :=
    degreeLE_mono (le_max_right Nf Ng) hNg
  let vf : degreeLE 3 N := ⟨restrictLinear 3 f, hNf'⟩
  let vg : degreeLE 3 N := ⟨restrictLinear 3 g, hNg'⟩
  have hproj : ∀ j, proj N hp j vg = Q.eval (j : ℂ) • proj N hp j vf := by
    intro j
    apply Subtype.ext
    funext x
    change ((proj N hp j ⟨restrictLinear 3 g, hNg'⟩ : degreeLE 3 N) : K3 → ℂ) x =
      Q.eval (j : ℂ) *
        ((proj N hp j ⟨restrictLinear 3 f, hNf'⟩ : degreeLE 3 N) : K3 → ℂ) x
    rw [proj_restrict_apply hp j hNg', proj_restrict_apply hp j hNf', hμ j _ x.2]
    ring
  have hvg : vg = aeval (-I • gen N hp) Q vf := by
    rw [← sum_proj_apply N hp vg, ← sum_proj_apply N hp (aeval (-I • gen N hp) Q vf)]
    apply Finset.sum_congr rfl
    intro j _
    rw [hproj, proj_aeval (isModeDecomposition N hp)]
  have hbound : HasModeBound (proj N hq) n vf := by
    intro j hj
    apply Subtype.ext
    funext x
    change ((proj N hq j ⟨restrictLinear 3 f, hNf'⟩ : degreeLE 3 N) : K3 → ℂ) x = 0
    rw [proj_restrict_apply hq j hNf', hlow _ x.2 j hj, mul_zero]
  obtain ⟨c, hab, _, hca⟩ := exists_relations N hpq hq hp
  have hboundg := mode_bound_aeval_negI hab hca (isModeDecomposition N hq) hbound Q
  rw [← hvg] at hboundg
  intro x hx j hj
  let κ : K3 := ⟨(x : Matrix (Fin 3) (Fin 3) ℝ), hx⟩
  have hz := congrFun (congrArg Subtype.val (hboundg j hj)) κ
  change ((proj N hq j ⟨restrictLinear 3 g, hNg'⟩ : degreeLE 3 N) : K3 → ℂ) κ = 0 at hz
  rw [proj_restrict_apply hq j hNg'] at hz
  have hzero : blockFourierCoefficient 3 q j g (Unitary.toUnits κ) = 0 :=
    (mul_eq_zero.mp hz).resolve_left (inv_ne_zero two_pi_ne_zero)
  simpa only [κ, RealKTypeCount.toUnits_mk hx] using hzero

open Langlands.LocalFactor.Archimedean RealBlockFrobeniusMap RealBlockMultiplier
open RealTailMultiplierPolynomial RealStandardFiltration RealBlockJacquet

/-- The actual differential-sign tail has the corresponding adjacent-window propagation. -/
theorem tail_propagation {ds es : List RealBlock} {p q ℓ : ℕ} {ε : ℤ}
    (hpq : q = 0 ∧ p = 1 ∨ q = 1 ∧ p = 0)
    (h : IsBlockFrobData 3 ds es p ε ((-1 : ℂ) ^ ℓ)
      (tailMultiplier ℓ ε ((-1 : ℂ) ^ ℓ)))
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1) (hpar : Even ((ℓ : ℤ) - 1 - ε))
    (f : KF 3 ds) (n : ℕ)
    (hlow : ∀ x ∈ unitaryCompact ℝ 3, ∀ j : ℤ, (n : ℤ) ≤ |j| →
      blockFourierCoefficient 3 q j f x = 0) :
    ∀ x ∈ unitaryCompact ℝ 3, ∀ j : ℤ, ((n + ℓ : ℕ) : ℤ) ≤ |j| →
      blockFourierCoefficient 3 q j (blockFrobMap h f) x = 0 := by
  have hμ : ∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 p j (blockFrobMap h f) x =
        (tailPolynomial ℓ).eval (j : ℂ) * blockFourierCoefficient 3 p j f x := by
    intro j x hx
    rw [blockFourierCoefficient_blockFrobMap h f hx]
    by_cases hj : Even (j - ε)
    · rw [tailPolynomial_eq hℓ hε hpar j hj]
    · rw [blockFourierCoefficient_eq_zero_of_not_even h.lt h.par f hj x, mul_zero, mul_zero]
  simpa only [tailPolynomial_natDegree] using
    propagation hpq (continuous_coe f) (continuous_coe (blockFrobMap h f))
      f.2.2 (blockFrobMap h f).2.2 (tailPolynomial ℓ) hμ n hlow

end Langlands.Archimedean.RealPolynomialFourierPropagation

namespace Langlands.Archimedean

open Polynomial in
/-- Polynomial Fourier multipliers on O(3) have finite propagation in the adjacent window. -/
def RealPolynomialFourierPropagationStatement : Prop :=
  ∀ (p q : ℕ), (q = 0 ∧ p = 1 ∨ q = 1 ∧ p = 0) →
  ∀ f g : Langlands.GeneralLinear 3 ℝ → ℂ, Continuous f → Continuous g →
    f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ))
      (unitaryCompact ℝ 3) →
    g ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ))
      (unitaryCompact ℝ 3) →
  ∀ Q : ℂ[X],
    (∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ 3,
      blockFourierCoefficient 3 p j g x =
        Q.eval (j : ℂ) * blockFourierCoefficient 3 p j f x) →
  ∀ n : ℕ,
    (∀ x ∈ unitaryCompact ℝ 3, ∀ j : ℤ, (n : ℤ) ≤ |j| →
      blockFourierCoefficient 3 q j f x = 0) →
    ∀ x ∈ unitaryCompact ℝ 3, ∀ j : ℤ, ((n + Q.natDegree : ℕ) : ℤ) ≤ |j| →
      blockFourierCoefficient 3 q j g x = 0

theorem realPolynomialFourierPropagation : RealPolynomialFourierPropagationStatement :=
  fun _ _ hpq _ _ hf hg hfK hgK Q hμ n hlow =>
    RealPolynomialFourierPropagation.propagation hpq hf hg hfK hgK Q hμ n hlow

end Langlands.Archimedean
