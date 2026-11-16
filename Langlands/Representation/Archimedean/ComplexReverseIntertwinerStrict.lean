import Langlands.Representation.Archimedean.ComplexReverseTransfer
import Langlands.Representation.Archimedean.ComplexReverseRecursion
import Langlands.Representation.Archimedean.ComplexStrictLanglandsQuotient
import Langlands.Representation.Archimedean.ComplexJacquetNonvanishing
import Langlands.Representation.Archimedean.ComplexPermutationSwap
import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientReduction

/-!
# Intertwiners to the reversed standard module: the strictly ordered case

Let `ds` be a list of `n` complex characters whose exponents have strictly decreasing real parts
and `T` a `(𝔤, K)`-intertwiner from the `U(n)`-finite functions of the standard module of `ds`
to those of the standard module of `ds.reverse`. Then `T` vanishes on every proper
`(𝔤, K)`-submodule `W` (`le_ker_of_isStrictlyOrdered`).

Proof. Let `χ`, `ψ` be the position characters of `ds` and `ds.reverse`, and let `f` be a
`U(n)`-finite function of the principal series of `χ` with nonzero Jacquet integral
`Λ_n(f) ≠ 0`. Put `v = f ∘ σ` with the twist `σ(g) = w₀ (gᵀ)⁻¹`; it lies in the principal
series of `ψ⁻¹`. Let `u` be its pairing transpose: `⟨u, h⟩ = ⟨v, T h⟩`. For `w ∈ W` and all `g`,
`∫ u(κ g) w(κ) dκ = ∫ w(κ g⁻¹) u(κ) dκ = ∫ (T w)(κ g⁻¹) v(κ) dκ = ∫ (T w ∘ σ)(κ gᵀ) f(κ) dκ`
(the `GL_n(ℂ)`-invariance of the pairing, the transfer identity, and the invariance of the Haar
measure of `U(n)` under `σ`). The recursion along the Jacquet integral gives
`u(1) Λ_n(w) = (T w)(w₀) Λ_n(f)`. Since `W` is proper, `Λ_n(w) = 0`, so `(T w)(w₀) = 0`.
Applying this to the translates `R(w₀ k) w ∈ W` gives `(T w)(k) = 0` for `k ∈ U(n)`, so
`T w = 0`.
-/

noncomputable section

open MeasureTheory Matrix

open scoped TensorProduct Matrix.Norms.Operator Manifold ContDiff

namespace Langlands.Archimedean

set_option autoImplicit false

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

namespace ComplexReverseIntertwinerStrict

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean ComplexPartialJacquet
  ComplexReverseTwist ComplexStandardHomTransposeProof ComplexStrictLanglandsQuotient

/-! ## Position characters of the reversed list -/

/-- The position characters are multiplicative in the inverse. -/
theorem complexPositionCharacter_inv : ∀ (ds : List ComplexCharacterData) (i : ℕ) (z : ℂˣ),
    complexPositionCharacter ds i z⁻¹ = (complexPositionCharacter ds i z)⁻¹
  | [], _, _ => by simp [complexPositionCharacter]
  | d :: _, 0, z => by
      change ((d.character z⁻¹ : ℂˣ) : ℂ) = ((d.character z : ℂˣ) : ℂ)⁻¹
      rw [map_inv, Units.val_inv_eq_inv_val]
  | _ :: ds, p + 1, z => complexPositionCharacter_inv ds p z

/-- The position character of `ds.reverse` at `n - 1 - j` is that of `ds` at `j`. -/
theorem complexPositionCharacter_reverse {n : ℕ} {ds : List ComplexCharacterData}
    (hn : ds.length = n) (j : Fin n) :
    complexPositionCharacter ds.reverse (Fin.rev j : Fin n) = complexPositionCharacter ds j := by
  subst hn
  have hj : (j : ℕ) < ds.length := j.2
  have hr : ((Fin.rev j : Fin ds.length) : ℕ) < ds.reverse.length := by
    rw [List.length_reverse]
    exact (Fin.rev j).2
  rw [ComplexPermutation.complexPositionCharacter_eq_get _ _ hr,
    ComplexPermutation.complexPositionCharacter_eq_get _ _ hj]
  simp only [List.get_eq_getElem, List.getElem_reverse, Fin.val_rev]
  have : ds.length - 1 - (ds.length - ((j : ℕ) + 1)) = (j : ℕ) := by omega
  simp only [this]

/-! ## The strictly ordered case -/

/-- **Intertwiners to the reversed standard module, strictly ordered case.** Let `ds` be a list
of `n` complex characters whose exponents have strictly decreasing real parts, `T` a
`(𝔤, K)`-intertwiner from the `U(n)`-finite functions of the standard module of `ds` to those of
the standard module of `ds.reverse`, and `W` a proper `(𝔤, K)`-submodule. Then `W ≤ ker T`. -/
theorem le_ker_of_isStrictlyOrdered (n : ℕ) (ds : List ComplexCharacterData)
    (T : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ]
      kFiniteFunctions (complexStandardModule n ds.reverse) (unitaryCompact ℂ n))
    (W : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)))
    (hn : ds.length = n) (hord : IsStrictlyOrdered ds)
    (hT : IsComplexStandardIntertwining n (complexStandardRep n ds.reverse)
      (complexStandardLie n ds.reverse) ds T)
    (hW : IsGKSubmodule (complexStandardRep n ds) (complexStandardLie n ds) W) (hW' : W ≠ ⊤) :
    W ≤ LinearMap.ker T := by
  subst hn
  have hχ := isPhasePower ds
  have hψ := isPhasePower ds.reverse
  have he := isStrictlyDominant hord
  have hTK : ∀ (k : Matrix.unitaryGroup (Fin ds.length) ℂ)
      (f : kFiniteFunctions (principalSeries ℂ ds.length (complexPositionCharacter ds)) (unitaryCompact ℂ ds.length)),
      T (principalSeriesRep ℂ ds.length (complexPositionCharacter ds) k f) = principalSeriesRep ℂ ds.length (complexPositionCharacter ds.reverse) k (T f) :=
    fun k f => map_complexStandardRep hT k f
  have hTX : ∀ (X : Matrix (Fin ds.length) (Fin ds.length) ℂ)
      (f : kFiniteFunctions (principalSeries ℂ ds.length (complexPositionCharacter ds)) (unitaryCompact ℂ ds.length)),
      T (principalSeriesLie ℂ ds.length (complexPositionCharacter ds) (1 ⊗ₜ X) f) =
        principalSeriesLie ℂ ds.length (complexPositionCharacter ds.reverse) (1 ⊗ₜ X) (T f) :=
    fun X f => map_complexStandardLie hT X f
  -- the characters of the twisted functions
  have hA : ∀ (j : Fin ds.length) (z : ℂˣ), dualChar (complexPositionCharacter ds.reverse) j z =
      complexPositionCharacter ds (Fin.rev j) z⁻¹ := by
    intro j z
    have h := complexPositionCharacter_reverse rfl (Fin.rev j)
    rw [Fin.rev_rev] at h
    simp only [dualChar, h, complexPositionCharacter_inv]
  have hB : ∀ (j : Fin ds.length) (z : ℂˣ), dualChar (complexPositionCharacter ds) j z =
      complexPositionCharacter ds.reverse (Fin.rev j) z⁻¹ := by
    intro j z
    simp only [dualChar, complexPositionCharacter_reverse rfl j, complexPositionCharacter_inv]
  -- the Jacquet integral vanishes on `W`
  have hJW : ∀ w ∈ W, ComplexJacquetDual.jacquet ds.length
      (w : Langlands.GeneralLinear ds.length ℂ → ℂ) = 0 := by
    obtain ⟨⟨g, hgS⟩, hgW⟩ : ∃ g : kFiniteFunctions (complexStandardModule ds.length ds) (unitaryCompact ℂ ds.length), g ∉ W := by
      by_contra hcon
      exact hW' (eq_top_iff.mpr fun g _ => by_contra fun h => hcon ⟨g, h⟩)
    have hWX : W.map (kFiniteFunctions (complexStandardModule ds.length ds) (unitaryCompact ℂ ds.length)).subtype ≤
        kFiniteFunctions (principalSeries ℂ ds.length (complexPositionCharacter ds)) (unitaryCompact ℂ ds.length) := by
      rintro _ ⟨w, -, rfl⟩
      exact w.2
    have hWK : ∀ k ∈ unitaryCompact ℂ ds.length, ∀ w ∈ W.map (kFiniteFunctions (complexStandardModule ds.length ds) (unitaryCompact ℂ ds.length)).subtype,
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear ds.length ℂ) k w ∈
          W.map (kFiniteFunctions (complexStandardModule ds.length ds) (unitaryCompact ℂ ds.length)).subtype := by
      intro k hk _ hw
      obtain ⟨w, hwW, rfl⟩ := hw
      refine ⟨complexStandardRep ds.length ds ⟨(k : Matrix (Fin ds.length) (Fin ds.length) ℂ),
        hk⟩ w, hW.1 _ w hwW, ?_⟩
      change ((complexStandardRep ds.length ds _ w : kFiniteFunctions (complexStandardModule ds.length ds) (unitaryCompact ℂ ds.length)) :
        Langlands.GeneralLinear ds.length ℂ → ℂ) = _
      rw [principalSeriesRep_apply_coe, ComplexReverseTransfer.toUnits_mk hk]
      rfl
    have hWD : ∀ (X : Matrix (Fin ds.length) (Fin ds.length) ℂ), ∀ w ∈ W.map (kFiniteFunctions (complexStandardModule ds.length ds) (unitaryCompact ℂ ds.length)).subtype,
        rightDerivative (matrixModel ℂ ds.length) X w ∈ W.map (kFiniteFunctions (complexStandardModule ds.length ds) (unitaryCompact ℂ ds.length)).subtype := by
      intro X _ hw
      obtain ⟨w, hwW, rfl⟩ := hw
      exact ⟨complexStandardLie ds.length ds (1 ⊗ₜ X) w, hW.2 _ w hwW,
        principalSeriesLie_one_tmul_apply_coe ℂ ds.length (complexPositionCharacter ds) X w⟩
    have hgW' : g ∉ W.map (kFiniteFunctions (complexStandardModule ds.length ds) (unitaryCompact ℂ ds.length)).subtype := by
      rintro ⟨w, hwW, hw⟩
      apply hgW
      have : w = ⟨g, hgS⟩ := Subtype.ext hw
      rw [← this]
      exact hwW
    intro w hw
    exact (ComplexJacquetKernel.jacquet_eq_zero_of_proper hχ he (W.map (kFiniteFunctions (complexStandardModule ds.length ds) (unitaryCompact ℂ ds.length)).subtype) hWX hWK hWD
      hgS hgW' ⟨w, hw, rfl⟩).2
  -- a vector with nonzero Jacquet integral, and its twist
  obtain ⟨f, hf, hf0⟩ := ComplexJacquetNonvanishing.exists_jacquet_ne_zero hχ he
    (complexPositionCharacter_phase ds)
  set v : kFiniteFunctions (principalSeries ℂ ds.length
        (dualChar (complexPositionCharacter ds.reverse)))
      (unitaryCompact ℂ ds.length) := ⟨twistLin ds.length f, twistLin_mem_kFiniteFunctions hA hf⟩
    with hvdef
  obtain ⟨u, huv⟩ := ComplexReverseTransfer.exists_pairing_transpose hχ T hTK v
  -- `(T w)(w₀) = 0` for `w ∈ W`
  have hw0 : ∀ w ∈ W, (T w : Langlands.GeneralLinear ds.length ℂ → ℂ) (w0GL ds.length) = 0 := by
    intro w hw
    have hx₂ := twistLin_mem_kFiniteFunctions hB (T w).2
    have hM : ∀ g : Langlands.GeneralLinear ds.length ℂ,
        ∫ κ, (u : Langlands.GeneralLinear ds.length ℂ → ℂ)
            ((κ : Langlands.GeneralLinear ds.length ℂ) * g) *
          (w : Langlands.GeneralLinear ds.length ℂ → ℂ) κ ∂ComplexDuality.unitaryHaar ds.length =
        ∫ κ, twistLin ds.length (T w : Langlands.GeneralLinear ds.length ℂ → ℂ)
            ((κ : Langlands.GeneralLinear ds.length ℂ) * transposeGL g) *
          f κ ∂ComplexDuality.unitaryHaar ds.length := by
      intro g
      have h1 := ComplexReverseTransfer.integral_mul_transfer hχ hψ T hTK hTX v u huv w g⁻¹
      have h2 := ComplexReverseRecursion.integral_mul_swap hχ w.2.1 u.2.1 g⁻¹
      have h3 := integral_mul_inv_eq_twist
        (ComplexDuality.continuous_of_mem_kFiniteFunctions (T w).2)
        (ComplexDuality.continuous_of_mem_kFiniteFunctions v.2) g
      rw [inv_inv] at h2
      rw [← h2, ← h1, h3]
      refine integral_congr_ae (ae_of_all _ fun κ => ?_)
      show (T w : Langlands.GeneralLinear ds.length ℂ → ℂ)
          (ComplexReverseTwist.twist ((κ : Langlands.GeneralLinear ds.length ℂ) * transposeGL g)) *
          f (ComplexReverseTwist.twist (ComplexReverseTwist.twist (κ : Langlands.GeneralLinear ds.length ℂ))) =
        (T w : Langlands.GeneralLinear ds.length ℂ → ℂ)
          (ComplexReverseTwist.twist ((κ : Langlands.GeneralLinear ds.length ℂ) * transposeGL g)) * f κ
      rw [ComplexReverseTwist.twist_twist]
    have hrec := ComplexReverseRecursion.mul_jacquet_eq_of_transpose ds.length hχ he u.2 w.2 hx₂
      hf hM
    rw [hJW w hw, mul_zero] at hrec
    have h0 := (mul_eq_zero.mp hrec.symm).resolve_right hf0
    rwa [twistLin_apply, ComplexReverseTwist.twist_one] at h0
  intro w hw
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  refine ComplexDuality.eq_zero_of_mem_principalSeries_of_eqOn (T w).2.1 fun k hk => ?_
  have hk' : w0GL ds.length * k ∈ unitaryCompact ℂ ds.length := mul_mem w0GL_mem hk
  have h := hw0 _ (hW.1 ⟨((w0GL ds.length * k : Langlands.GeneralLinear ds.length ℂ) :
    Matrix (Fin ds.length) (Fin ds.length) ℂ), hk'⟩ w hw)
  rw [hTK, principalSeriesRep_apply_coe, ComplexReverseTransfer.toUnits_mk hk'] at h
  change (T w : Langlands.GeneralLinear ds.length ℂ → ℂ)
    (w0GL ds.length * (w0GL ds.length * k)) = 0 at h
  rwa [← mul_assoc, w0GL_mul_self, one_mul] at h

end ComplexReverseIntertwinerStrict

open Langlands.LocalFactor.Archimedean

/-- **Intertwiners to the reversed standard module, strictly ordered case.** For a list `ds` of
`n` complex characters whose exponents have strictly decreasing real parts, every
`(𝔤, K)`-intertwiner `T` from the `U(n)`-finite functions of the standard module of `ds` to those
of the standard module of `ds.reverse` vanishes on every proper `(𝔤, K)`-submodule `W`. -/
def ComplexStrictReverseIntertwinerKernelStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData)
    (T : kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →ₗ[ℂ]
      kFiniteFunctions (complexStandardModule n ds.reverse) (unitaryCompact ℂ n))
    (W : Submodule ℂ (kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n))),
    ds.length = n → ComplexStrictLanglandsQuotient.IsStrictlyOrdered ds →
      IsComplexStandardIntertwining n (complexStandardRep n ds.reverse)
        (complexStandardLie n ds.reverse) ds T →
        IsGKSubmodule (complexStandardRep n ds) (complexStandardLie n ds) W → W ≠ ⊤ →
          W ≤ LinearMap.ker T

theorem complexStrictReverseIntertwinerKernel : ComplexStrictReverseIntertwinerKernelStatement :=
  fun n ds T W hn hord hT hW hW' =>
    ComplexReverseIntertwinerStrict.le_ker_of_isStrictlyOrdered n ds T W hn hord hT hW hW'

end Langlands.Archimedean
