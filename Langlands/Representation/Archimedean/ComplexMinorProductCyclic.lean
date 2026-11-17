import Langlands.Representation.Archimedean.ComplexMinorMonomialCalculus
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesAnnihilator
import Langlands.Representation.Archimedean.ComplexJacquetChart
import Langlands.Representation.Archimedean.ComplexJacquetTorus
import Langlands.Representation.Archimedean.ComplexJacquetReduction
import Langlands.Representation.Archimedean.ComplexTemperedComplement
import Langlands.Representation.Archimedean.ComplexReverseTransfer

/-!
# Cyclicity of products with minor monomials

Let `v = minorMonomial c d` be the minor monomial `det(g)^d ∏_j Δ_{j+1}(g)^{c_j}` on `GL_n(ℂ)`,
with weights `l_i = minorWeight c d i`. If the characters of `ds` are those of `ds'` twisted by
`z ↦ z^{l_i}` at each position, then multiplication by `v` maps the standard module of `ds'`
into that of `ds`. This file proves (`complexMinorProductCyclic`): if `T` is a `U(n)`-invariant
cyclic vector of the `(𝔤, K)`-module of `ds'`, then `v · T` is a cyclic vector of the
`(𝔤, K)`-module of `ds`.

The proof has two steps.

1. *Upper triangular words.* A `U(n)`-invariant vector is killed by the skew-Hermitian
   directions, and every matrix is the sum of a skew-Hermitian and an upper triangular one, so
   the smallest subspace containing `T` and stable under the upper triangular directions is
   `(𝔤, K)`-stable (`upperClosure_eq_top`), hence everything. For `X` upper triangular,
   `v · R(X) h = R(X)(v h) - c_X v h` (`mulV_lie`), so every `(𝔤, K)`-stable `W ∋ v T` contains
   `v h` for every `h` in the module of `ds'` (`mulV_mem`).
2. *Godement's argument.* If such a `W` were proper, `complexStandardAnnihilator` gives `u` in
   the module of the inverse characters, nonzero at some `k₀ ∈ U(n)`, with `∫_{U(n)} w u = 0`
   for `w ∈ W`. Choosing `h` with `h(κ k₁) = conj(v(κ k₁) u(κ))` on `U(n)` (a Gram-weighted
   conjugate, `ComplexDuality.partner`) and applying this to the translate of `v h` by `k₁`
   gives `∫ |v(κ k₁) u(κ)|² = 0`; with `k₀ k₁` the antidiagonal permutation matrix, where `v`
   does not vanish, this contradicts `u(k₀) ≠ 0` (`eq_top_of_forall_mulV_mem`).
-/

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff Matrix Matrix.Norms.Operator ComplexConjugate TensorProduct

set_option autoImplicit false

-- As in `GKModule`: the charts on units need reduction through the normed-ring instances of
-- matrices.
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped ComplexDuality

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Statement (cyclicity of products with minor monomials).** Let `c : Fin n → ℕ`, `d : ℤ`
and let `ds`, `ds'` be lists of complex characters whose position characters satisfy
`χ_i(z) = z^{l_i} χ'_i(z)` for every position `i < n`, where
`l_i = ComplexMinorProduct.minorWeight c d i = d + ∑_{j : n - (j + 1) ≤ i} c_j`. Let `T` be a
`U(n)`-finite function of the standard module of `ds'` that is fixed by right translation by
`U(n)` and generates the `(𝔤𝔩_n(ℂ), U(n))`-module of `ds'` (every subspace stable under
`U(n)` and `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)` containing `T` is everything). Then the function
`f₀(g) = minorMonomial c d g · T(g)` is a `U(n)`-finite function of the standard module of `ds`
that generates the `(𝔤𝔩_n(ℂ), U(n))`-module of `ds`. -/
def ComplexMinorProductCyclicStatement : Prop :=
  ∀ (n : ℕ) (ds ds' : List ComplexCharacterData) (c : Fin n → ℕ) (d : ℤ),
    (∀ (i : Fin n) (z : ℂˣ), complexPositionCharacter ds i z =
      (z : ℂ) ^ ComplexMinorProduct.minorWeight c d i * complexPositionCharacter ds' i z) →
    ∀ T : kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n),
      (∀ k : Matrix.unitaryGroup (Fin n) ℂ, complexStandardRep n ds' k T = T) →
      (∀ W : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds') (unitaryCompact ℂ n)),
        (∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ w ∈ W, complexStandardRep n ds' k w ∈ W) →
        (∀ (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, complexStandardLie n ds' Z w ∈ W) →
        T ∈ W → W = ⊤) →
      ∃ f₀ : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n),
        (∀ g : Langlands.GeneralLinear n ℂ,
          (f₀ : Langlands.GeneralLinear n ℂ → ℂ) g =
            ComplexLowestKType.minorMonomial c d (g : Matrix (Fin n) (Fin n) ℂ) *
              (T : Langlands.GeneralLinear n ℂ → ℂ) g) ∧
        ∀ W : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)),
          (∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ w ∈ W, complexStandardRep n ds k w ∈ W) →
          (∀ (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, complexStandardLie n ds Z w ∈ W) →
          f₀ ∈ W → W = ⊤

namespace ComplexMinorProduct

open ComplexLowestKType

variable {n : ℕ}

/-! ## Upper triangular closures in `(𝔤, K)`-modules -/

section Closure

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)

/-- The smallest subspace containing `v` and stable under `π(1 ⊗ X)` for every upper
triangular `X`. -/
def upperClosure (v : V) : Submodule ℂ V :=
  sInf {S | v ∈ S ∧ ∀ X : Matrix (Fin n) (Fin n) ℂ, X.IsUpperTriangular →
    ∀ w ∈ S, π (1 ⊗ₜ X) w ∈ S}

theorem mem_upperClosure_self (v : V) : v ∈ upperClosure π v :=
  Submodule.mem_sInf.2 fun _ hS => hS.1

theorem upper_mem_upperClosure (v : V) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.IsUpperTriangular) {w : V} (hw : w ∈ upperClosure π v) :
    π (1 ⊗ₜ X) w ∈ upperClosure π v :=
  Submodule.mem_sInf.2 fun S hS => hS.2 X hX w (Submodule.mem_sInf.1 hw S hS)

theorem upperClosure_le {v : V} {S : Submodule ℂ V} (hv : v ∈ S)
    (hS : ∀ X : Matrix (Fin n) (Fin n) ℂ, X.IsUpperTriangular → ∀ w ∈ S, π (1 ⊗ₜ X) w ∈ S) :
    upperClosure π v ≤ S :=
  sInf_le ⟨hv, hS⟩

/-- If the skew-Hermitian directions kill `v`, the upper triangular closure of `v` is stable
under every direction `π(1 ⊗ Y)`. -/
theorem lie_mem_upperClosure {v : V}
    (hv : ∀ Y : Matrix (Fin n) (Fin n) ℂ, star Y = -Y → π (1 ⊗ₜ Y) v = 0)
    (Y : Matrix (Fin n) (Fin n) ℂ) {w : V} (hw : w ∈ upperClosure π v) :
    π (1 ⊗ₜ Y) w ∈ upperClosure π v := by
  let S' : Submodule ℂ V :=
    { carrier := {w | w ∈ upperClosure π v ∧
        ∀ Y : Matrix (Fin n) (Fin n) ℂ, π (1 ⊗ₜ Y) w ∈ upperClosure π v}
      add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun Y => by
        rw [map_add]
        exact add_mem (ha.2 Y) (hb.2 Y)⟩
      zero_mem' := ⟨zero_mem _, fun Y => by
        rw [map_zero]
        exact zero_mem _⟩
      smul_mem' := fun z w hw => ⟨Submodule.smul_mem _ z hw.1, fun Y => by
        rw [map_smul]
        exact Submodule.smul_mem _ z (hw.2 Y)⟩ }
  have hle : upperClosure π v ≤ S' := by
    refine upperClosure_le π ⟨mem_upperClosure_self π v, fun Y => ?_⟩
      fun X hX w hw => ⟨upper_mem_upperClosure π v hX hw.1, fun Y => ?_⟩
    · rw [← upperPart_add_skewPart Y, TensorProduct.tmul_add, map_add, LinearMap.add_apply,
        hv _ (star_skewPart Y), add_zero]
      exact upper_mem_upperClosure π v (upperPart_isUpperTriangular Y)
        (mem_upperClosure_self π v)
    · have hc := complex_map_commutator π Y X
      have e : π (1 ⊗ₜ Y) (π (1 ⊗ₜ X) w) =
          π (1 ⊗ₜ X) (π (1 ⊗ₜ Y) w) + π (1 ⊗ₜ (Y * X - X * Y)) w := by
        rw [hc, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
        abel
      rw [e]
      exact add_mem (upper_mem_upperClosure π v hX (hw.2 Y)) (hw.2 _)
  exact (hle hw).2 Y

/-- The upper triangular closure is stable under the whole Lie algebra action. -/
theorem lieAll_mem_upperClosure {v : V}
    (hv : ∀ Y : Matrix (Fin n) (Fin n) ℂ, star Y = -Y → π (1 ⊗ₜ Y) v = 0)
    (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) {w : V} (hw : w ∈ upperClosure π v) :
    π Z w ∈ upperClosure π v := by
  induction Z using TensorProduct.inductionOn with
  | tmul z Y =>
      have h1 : z ⊗ₜ[ℝ] Y = z • ((1 : ℂ) ⊗ₜ[ℝ] Y) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, map_smul, LinearMap.smul_apply]
      exact Submodule.smul_mem _ z (lie_mem_upperClosure π hv Y hw)
  | add Z₁ Z₂ h₁ h₂ =>
      rw [map_add, LinearMap.add_apply]
      exact add_mem h₁ h₂

variable {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V}

/-- A `U(n)`-invariant vector is killed by the skew-Hermitian directions. -/
theorem lie_skew_eq_zero (hgk : IsComplexGKModule n ρ π) {v : V} (hv0 : ∀ k, ρ k v = v)
    {Y : Matrix (Fin n) (Fin n) ℂ} (hY : star Y = -Y) : π (1 ⊗ₜ Y) v = 0 := by
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
  have h := hgk.2.2.1 (fun t : ℝ => skewExp (t • Y) (star_real_smul_of_skew hY t)) Y
    (skewExp_zero_smul hY) (hasDerivAt_skewExp_entry hY) v ℓ
  simp only [hv0] at h
  exact h.unique (hasDerivAt_const 0 (ℓ v))

/-- The upper triangular closure of a `U(n)`-invariant vector is `U(n)`-stable. -/
theorem rho_mem_upperClosure (hgk : IsComplexGKModule n ρ π) {v : V} (hv0 : ∀ k, ρ k v = v)
    (k : Matrix.unitaryGroup (Fin n) ℂ) {w : V} (hw : w ∈ upperClosure π v) :
    ρ k w ∈ upperClosure π v := by
  have hle : upperClosure π v ≤ (upperClosure π v).comap (ρ k) := by
    refine upperClosure_le π ?_ fun X _ w hw => ?_
    · rw [Submodule.mem_comap, hv0]
      exact mem_upperClosure_self π v
    · rw [Submodule.mem_comap] at hw ⊢
      rw [hgk.2.2.2 k X w]
      exact lie_mem_upperClosure π (fun Y hY => lie_skew_eq_zero π hgk hv0 hY) _ hw
  exact hle hw

/-- **Upper triangular words span.** If `v` is a `U(n)`-invariant cyclic vector, its upper
triangular closure is everything. -/
theorem upperClosure_eq_top (hgk : IsComplexGKModule n ρ π) {v : V} (hv0 : ∀ k, ρ k v = v)
    (hcyc : ∀ W : Submodule ℂ V, (∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ w ∈ W, ρ k w ∈ W) →
      (∀ (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, π Z w ∈ W) → v ∈ W → W = ⊤) :
    upperClosure π v = ⊤ :=
  hcyc _ (fun k _ hw => rho_mem_upperClosure π hgk hv0 k hw)
    (fun Z _ hw => lieAll_mem_upperClosure π (fun _ hY => lie_skew_eq_zero π hgk hv0 hY) Z hw)
    (mem_upperClosure_self π v)

end Closure

/-! ## Multiplication by the minor monomial -/

/-- The `U(n)`-finite functions of the standard module of `ds`. -/
abbrev MKF (n : ℕ) (ds : List ComplexCharacterData) :
    Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) :=
  kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)

/-- Twisting the position characters by `z ↦ z^{w_i}` multiplies the principal-series
character by `∏_i a_i^{w_i}`. -/
theorem principalSeriesCharacter_eq_prod_mul {χ₁ χ₂ : ℕ → ℂˣ → ℂ} (w : Fin n → ℤ)
    (h : ∀ (i : Fin n) (z : ℂˣ), χ₁ i z = (z : ℂ) ^ w i * χ₂ i z) (a : Fin n → ℂˣ) :
    principalSeriesCharacter ℂ n χ₁ a =
      (∏ i, (a i : ℂ) ^ w i) * principalSeriesCharacter ℂ n χ₂ a := by
  unfold principalSeriesCharacter
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [h]
  ring

/-- Left equivariance of the minor monomial under the Borel subgroup. -/
theorem minorFun_borel_mul (c : Fin n → ℕ) (d : ℤ) (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ)
    (g : Langlands.GeneralLinear n ℂ) :
    minorFun c d ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
        (u : Langlands.GeneralLinear n ℂ) * g) =
      (∏ i, (a i : ℂ) ^ minorWeight c d i) * minorFun c d g := by
  rw [minorFun, ComplexPrincipalSeriesExtension.val_iwasawa,
    minorMonomial_upper_mul c d (ComplexGramFormula.isUpperTriangular_diagonal_mul a u)
      (fun i => by rw [ComplexGramFormula.diagonal_mul_apply_self]; exact (a i).ne_zero)]
  simp_rw [ComplexGramFormula.diagonal_mul_apply_self]
  rfl

/-- The product of the minor monomial with a principal-series function of `χ₂` lies in the
principal series of the twisted characters `χ₁`. -/
theorem mulFun_mem_principalSeries {χ₁ χ₂ : ℕ → ℂˣ → ℂ} (c : Fin n → ℕ) (d : ℤ)
    (h : ∀ (i : Fin n) (z : ℂˣ), χ₁ i z = (z : ℂ) ^ minorWeight c d i * χ₂ i z)
    {f : Langlands.GeneralLinear n ℂ → ℂ} (hf : f ∈ principalSeries ℂ n χ₂) :
    (fun g => minorFun c d g * f g) ∈ principalSeries ℂ n χ₁ := by
  refine ⟨ComplexJacquetLimit.contMDiff_mul_fun (contMDiff_minorFun c d) hf.1, fun a u g => ?_⟩
  change minorFun c d _ * f _ = _ * (minorFun c d g * f g)
  rw [minorFun_borel_mul, hf.2, principalSeriesCharacter_eq_prod_mul _ h]
  ring

theorem mulFun_mem_kFiniteFunctions {χ₁ χ₂ : ℕ → ℂˣ → ℂ} (c : Fin n → ℕ) (d : ℤ)
    (h : ∀ (i : Fin n) (z : ℂˣ), χ₁ i z = (z : ℂ) ^ minorWeight c d i * χ₂ i z)
    {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℂ n χ₂) (unitaryCompact ℂ n)) :
    (fun g => minorFun c d g * f g) ∈
      kFiniteFunctions (principalSeries ℂ n χ₁) (unitaryCompact ℂ n) :=
  Submodule.mem_inf.2 ⟨mulFun_mem_principalSeries c d h (Submodule.mem_inf.1 hf).1,
    mul_mem_kFiniteVectors (minorFun_mem_kFiniteVectors c d) (Submodule.mem_inf.1 hf).2⟩

variable {ds ds' : List ComplexCharacterData} {c : Fin n → ℕ} {d : ℤ}

/-- Multiplication by the minor monomial, from the module of `ds'` to that of `ds`. -/
def mulV (c : Fin n → ℕ) (d : ℤ)
    (hχ : ∀ (i : Fin n) (z : ℂˣ), complexPositionCharacter ds i z =
      (z : ℂ) ^ minorWeight c d i * complexPositionCharacter ds' i z) :
    MKF n ds' →ₗ[ℂ] MKF n ds where
  toFun h := ⟨fun g => minorFun c d g * (h : Langlands.GeneralLinear n ℂ → ℂ) g,
    mulFun_mem_kFiniteFunctions c d hχ h.2⟩
  map_add' h₁ h₂ := Subtype.ext (funext fun g => by
    change minorFun c d g * ((h₁ : Langlands.GeneralLinear n ℂ → ℂ) g +
      (h₂ : Langlands.GeneralLinear n ℂ → ℂ) g) = _ + _
    rw [mul_add])
  map_smul' z h := Subtype.ext (funext fun g => by
    change minorFun c d g * (z * (h : Langlands.GeneralLinear n ℂ → ℂ) g) =
      z * (minorFun c d g * (h : Langlands.GeneralLinear n ℂ → ℂ) g)
    ring)

theorem mulV_coe
    (hχ : ∀ (i : Fin n) (z : ℂˣ), complexPositionCharacter ds i z =
      (z : ℂ) ^ minorWeight c d i * complexPositionCharacter ds' i z) (h : MKF n ds') :
    ((mulV c d hχ h : MKF n ds) : Langlands.GeneralLinear n ℂ → ℂ) =
      fun g => minorFun c d g * (h : Langlands.GeneralLinear n ℂ → ℂ) g :=
  rfl

/-- For `X` upper triangular, `v · R(X) h = R(X)(v h) - c_X · v h`. -/
theorem mulV_lie
    (hχ : ∀ (i : Fin n) (z : ℂˣ), complexPositionCharacter ds i z =
      (z : ℂ) ^ minorWeight c d i * complexPositionCharacter ds' i z)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X.IsUpperTriangular) (h : MKF n ds') :
    mulV c d hχ (complexStandardLie n ds' (1 ⊗ₜ X) h) =
      complexStandardLie n ds (1 ⊗ₜ X) (mulV c d hχ h) - rightCharDeriv c d X • mulV c d hχ h := by
  have h1 : ((complexStandardLie n ds' (1 ⊗ₜ X) h : MKF n ds') :
      Langlands.GeneralLinear n ℂ → ℂ) = rightDerivative (matrixModel ℂ n) X h :=
    principalSeriesLie_one_tmul_apply_coe ℂ n _ X h
  have h2 : ((complexStandardLie n ds (1 ⊗ₜ X) (mulV c d hχ h) : MKF n ds) :
      Langlands.GeneralLinear n ℂ → ℂ) =
        rightDerivative (matrixModel ℂ n) X (mulV c d hχ h) :=
    principalSeriesLie_one_tmul_apply_coe ℂ n _ X _
  apply Subtype.ext
  funext g
  rw [Submodule.coe_sub, Pi.sub_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, h2,
    mulV_coe, mulV_coe, h1,
    ComplexTemperedComplement.rightDerivative_mul_fun (contMDiff_minorFun c d) h.2.1.1,
    rightDerivative_minorFun hX]
  ring

/-- **Step 1.** Every `𝔤`-stable subspace containing `v T` contains `v h` for every `h`, when
the upper triangular closure of `T` is everything. -/
theorem mulV_mem
    (hχ : ∀ (i : Fin n) (z : ℂˣ), complexPositionCharacter ds i z =
      (z : ℂ) ^ minorWeight c d i * complexPositionCharacter ds' i z)
    (W : Submodule ℂ (MKF n ds))
    (hWL : ∀ (Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ), ∀ w ∈ W, complexStandardLie n ds Z w ∈ W)
    {T : MKF n ds'} (hT : mulV c d hχ T ∈ W)
    (htop : upperClosure (complexStandardLie n ds') T = ⊤) (h : MKF n ds') :
    mulV c d hχ h ∈ W := by
  have hle : upperClosure (complexStandardLie n ds') T ≤ W.comap (mulV c d hχ) :=
    upperClosure_le _ hT fun X hX w hw => by
      rw [Submodule.mem_comap] at hw ⊢
      rw [mulV_lie hχ hX]
      exact sub_mem (hWL _ _ hw) (Submodule.smul_mem _ _ hw)
  exact hle (htop ▸ Submodule.mem_top)

/-! ## Godement's argument -/

/-- **Step 2.** A `U(n)`-stable subspace of the module of `ds` containing `v h` for every `h`
in the module of `ds'` is everything. -/
theorem eq_top_of_forall_mulV_mem
    (hχ : ∀ (i : Fin n) (z : ℂˣ), complexPositionCharacter ds i z =
      (z : ℂ) ^ minorWeight c d i * complexPositionCharacter ds' i z)
    (W : Submodule ℂ (MKF n ds))
    (hWK : ∀ (k : Matrix.unitaryGroup (Fin n) ℂ), ∀ w ∈ W, complexStandardRep n ds k w ∈ W)
    (hall : ∀ h : MKF n ds', mulV c d hχ h ∈ W) : W = ⊤ := by
  by_contra hne
  obtain ⟨f, hf⟩ : ∃ f : MKF n ds, f ∉ W := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_top_iff.2 fun f _ => hcon f)
  set W' : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) := W.map (MKF n ds).subtype with hW'
  have hWX : W' ≤ MKF n ds := by
    rintro _ ⟨w, _, rfl⟩
    exact w.2
  have hWK' : ∀ k ∈ unitaryCompact ℂ n, ∀ w ∈ W',
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k w ∈ W' := by
    rintro k hk _ ⟨w, hw, rfl⟩
    refine ⟨complexStandardRep n ds ⟨(k : Matrix (Fin n) (Fin n) ℂ), hk⟩ w, hWK _ w hw, ?_⟩
    have e := principalSeriesRep_apply_coe ℂ n (complexPositionCharacter ds)
      ⟨(k : Matrix (Fin n) (Fin n) ℂ), hk⟩ w
    rw [ComplexReverseTransfer.toUnits_mk] at e
    exact e
  have hfW : (f : Langlands.GeneralLinear n ℂ → ℂ) ∉ W' := by
    rintro ⟨w, hw, hwf⟩
    have hwf' : w = f := Subtype.ext hwf
    exact hf (hwf' ▸ hw)
  obtain ⟨u, hu, ⟨k₀, hk₀⟩, hint⟩ := complexStandardAnnihilator n ds W' f hWX hWK' f.2 hfW
  obtain ⟨s, hs⟩ := ComplexDuality.exists_normSq_complexPositionCharacter ds'
  have hne : ∀ i (z : ℂˣ), complexPositionCharacter ds' i z ≠ 0 := fun i z h0 => by
    have h1 := hs i z
    rw [h0, map_zero] at h1
    exact (Real.rpow_pos_of_pos (Complex.normSq_pos.2 z.ne_zero) _).ne' h1.symm
  -- the translate `k₁` with `k₀ k₁` the antidiagonal permutation matrix
  set κ₀ : Matrix.unitaryGroup (Fin n) ℂ := ComplexJacquetDual.toUnitaryGroup n k₀ with hκ₀
  set k₁ : Matrix.unitaryGroup (Fin n) ℂ := κ₀⁻¹ * revUnitary n with hk₁
  have hk₁mem : (Unitary.toUnits k₁ : Langlands.GeneralLinear n ℂ) ∈ unitaryCompact ℂ n :=
    k₁.2
  have htmem : (Unitary.toUnits k₁⁻¹ : Langlands.GeneralLinear n ℂ) ∈ unitaryCompact ℂ n :=
    k₁⁻¹.2
  set ut := Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
    (Unitary.toUnits k₁⁻¹ : Langlands.GeneralLinear n ℂ) u with hut_def
  have hut : ut ∈ MKF n (ds.map complexCharacterDataInv) :=
    rightTranslation_mem_kFiniteFunctions_complexStandardModule n _ hu htmem
  have hrel : ∀ (i : Fin n) (z : ℂˣ), (complexPositionCharacter ds' i z)⁻¹ =
      (z : ℂ) ^ minorWeight c d i *
        complexPositionCharacter (ds.map complexCharacterDataInv) i z := by
    intro i z
    rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (hne i z), mul_comm ((z : ℂ) ^ _) _, mul_assoc,
      ← hχ i z, complexPositionCharacter_map_inv_mul]
  set F : Langlands.GeneralLinear n ℂ → ℂ := fun g => minorFun c d g * ut g with hF_def
  have hF : F ∈ kFiniteFunctions
      (principalSeries ℂ n fun i z => (complexPositionCharacter ds' i z)⁻¹)
      (unitaryCompact ℂ n) :=
    mulFun_mem_kFiniteFunctions (χ₁ := fun i z => (complexPositionCharacter ds' i z)⁻¹) c d
      hrel hut
  have hH : ComplexDuality.partner s F ∈ MKF n ds' :=
    Submodule.mem_inf.2
      ⟨ComplexDuality.partner_mem_principalSeries (fun i z => mul_inv_cancel₀ (hne i z)) hs
        (Submodule.mem_inf.1 hF).1,
      ComplexDuality.partner_mem_kFiniteVectors s (Submodule.mem_inf.1 hF).2⟩
  set H : MKF n ds' := ⟨_, hH⟩ with hH_def
  have hmem : complexStandardRep n ds k₁ (mulV c d hχ H) ∈ W := hWK k₁ _ (hall H)
  have h0 := hint _ ⟨_, hmem, rfl⟩
  -- the integrand is `|v(κ k₁) u(κ)|²`
  have hpt : ∀ k : unitaryCompact ℂ n,
      ((MKF n ds).subtype (complexStandardRep n ds k₁ (mulV c d hχ H)))
          (k : Langlands.GeneralLinear n ℂ) * u k =
        ((Complex.normSq (minorFun c d ((k : Langlands.GeneralLinear n ℂ) * Unitary.toUnits k₁) *
          u k) : ℝ) : ℂ) := by
    intro k
    have e := principalSeriesRep_apply_coe ℂ n (complexPositionCharacter ds) k₁ (mulV c d hχ H)
    rw [Submodule.coe_subtype, e]
    have hku : (k : Langlands.GeneralLinear n ℂ) * Unitary.toUnits k₁ ∈ unitaryCompact ℂ n :=
      mul_mem k.2 hk₁mem
    have hFk : F ((k : Langlands.GeneralLinear n ℂ) * Unitary.toUnits k₁) =
        minorFun c d ((k : Langlands.GeneralLinear n ℂ) * Unitary.toUnits k₁) * u k := by
      change minorFun c d _ * u ((k : Langlands.GeneralLinear n ℂ) * Unitary.toUnits k₁ *
        Unitary.toUnits k₁⁻¹) = _
      rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    change minorFun c d ((k : Langlands.GeneralLinear n ℂ) * Unitary.toUnits k₁) *
      ComplexDuality.partner s F ((k : Langlands.GeneralLinear n ℂ) * Unitary.toUnits k₁) *
        u k = _
    rw [ComplexDuality.partner, ComplexDuality.gramWeight_unitary s hku, hFk,
      Complex.ofReal_one, one_mul, Complex.star_def, Complex.normSq_eq_conj_mul_self]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_complex_ofReal,
    Complex.ofReal_eq_zero] at h0
  have hcont : Continuous fun k : unitaryCompact ℂ n =>
      Complex.normSq (minorFun c d ((k : Langlands.GeneralLinear n ℂ) * Unitary.toUnits k₁) *
        u k) := by
    have hv : Continuous (minorFun c d) := (contMDiff_minorFun c d).continuous
    have huc : Continuous u := ComplexDuality.continuous_of_mem_kFiniteFunctions hu
    exact Complex.continuous_normSq.comp
      ((hv.comp (continuous_subtype_val.mul continuous_const)).mul
        (huc.comp continuous_subtype_val))
  have hk₀r : (k₀ : Langlands.GeneralLinear n ℂ) * Unitary.toUnits k₁ =
      Unitary.toUnits (revUnitary n) := by
    have e0 : (k₀ : Langlands.GeneralLinear n ℂ) = Unitary.toUnits κ₀ := Units.ext rfl
    rw [e0, ← map_mul, hk₁, mul_inv_cancel_left]
  have hpos := ComplexDuality.integral_unitaryHaar_pos hcont
    (fun k => Complex.normSq_nonneg _) (k := k₀) (by
      rw [hk₀r]
      refine (Complex.normSq_pos.2 (mul_ne_zero ?_ hk₀)).ne'
      exact minorMonomial_revUnitary_ne_zero c d)
  exact hpos.ne' h0

end ComplexMinorProduct

open ComplexMinorProduct

/-- **Cyclicity of products with minor monomials.** -/
theorem complexMinorProductCyclic : ComplexMinorProductCyclicStatement := by
  intro n ds ds' c d hχ T hT hcyc
  refine ⟨mulV c d hχ T, fun g => rfl, fun W hWK hWL hW => ?_⟩
  have htop := upperClosure_eq_top (complexStandardLie n ds')
    (isComplexGKModule_complexStandardModule n ds') hT hcyc
  exact eq_top_of_forall_mulV_mem hχ W hWK fun h => mulV_mem hχ W hWL hW htop h

end Langlands.Archimedean
