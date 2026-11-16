import Langlands.Representation.Archimedean.RealReverseRecursion
import Langlands.Representation.Archimedean.RealReverseTransfer
import Langlands.Representation.Archimedean.RealCharacterLanglandsQuotient

/-!
# Intertwiners to the reversed standard module (character blocks)

For a list `ds` of real character blocks in Langlands order (ties allowed), every
`(𝔤, K)`-intertwiner `T` from the `O(n)`-finite functions of the standard module of `ds` to those
of the standard module of `ds.reverse` vanishes on every proper `(𝔤, K)`-submodule `W`, assuming
the two block statements `RealBlockChartIntegrableStatement`,
`RealBlockParabolicIntegrationStatement` and the tempered irreducibility statement
`RealTemperedStandardIrreducibleStatement`.

Let `f` be a test vector with nonzero block Jacquet functional, `v = f ∘ twist` (an
`O(n)`-finite function of the principal series of the inverse characters of `ds.reverse`) and
`u` its pairing transpose under `T`. For `w ∈ W` the coefficient `g ↦ ∫ u(κ g) w(κ) dκ` equals
`g ↦ ∫ (T w)(twist(κ gᵀ)) f(κ) dκ`, and it lies in `nullCoeff` of the annihilator of `W`. The
transposed-coefficient recursion `RealReverseRecursion.jac_eq_zero_of_transpose` then gives
`(T w)(w₀) = 0` for all `w ∈ W`, hence `T w = 0`.
-/

noncomputable section

open MeasureTheory Matrix

open scoped TensorProduct Matrix Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

namespace RealCharacterReverseKernel

open Langlands.LocalFactor.Archimedean RealStrictCharacterLanglandsQuotient
  RealCharacterLanglandsQuotient RealBlockFunctional RealBlockNonvanishing RealReverseRecursion
  RealReverseTwist RealReverseTransfer JacquetKernel RealPrincipalSeriesDuality PartialJacquet
  Langlands.GeneralLinear GramFormula JacquetDual MaximalParabolicIntegration

attribute [local instance] measurableSpaceK

/-! ## Position characters of character lists -/

theorem realRank_eq_length : ∀ {ds : List RealBlock}, IsCharacterList ds →
    realRank ds = ds.length
  | [], _ => rfl
  | b :: ds, h => by
      obtain ⟨c, rfl⟩ := h b List.mem_cons_self
      have ih := realRank_eq_length (ds := ds) fun b hb => h b (List.mem_cons_of_mem _ hb)
      change 1 + realRank ds = ds.length + 1
      rw [ih, add_comm]

theorem realPositionCharacter_inv : ∀ {ds : List RealBlock}, IsCharacterList ds →
    ∀ (l : ℕ) (z : ℝˣ), realPositionCharacter ds l z⁻¹ = (realPositionCharacter ds l z)⁻¹
  | [], _, _, _ => by simp [realPositionCharacter]
  | b :: ds, h, 0, z => by
      obtain ⟨c, rfl⟩ := h b List.mem_cons_self
      change ((c.character z⁻¹ : ℂˣ) : ℂ) = ((c.character z : ℂˣ) : ℂ)⁻¹
      rw [map_inv, Units.val_inv_eq_inv_val]
  | b :: ds, h, l + 1, z => by
      obtain ⟨c, rfl⟩ := h b List.mem_cons_self
      exact realPositionCharacter_inv (fun b hb => h b (List.mem_cons_of_mem _ hb)) l z

theorem realPositionCharacter_append : ∀ {A : List RealBlock}, IsCharacterList A →
    ∀ (B : List RealBlock) (l : ℕ), realPositionCharacter (A ++ B) l =
      if l < A.length then realPositionCharacter A l else realPositionCharacter B (l - A.length)
  | [], _, B, l => by simp
  | b :: A, h, B, 0 => by
      obtain ⟨c, rfl⟩ := h b List.mem_cons_self
      simp only [List.length_cons, Nat.zero_lt_succ, ite_true]
      rfl
  | b :: A, h, B, l + 1 => by
      obtain ⟨c, rfl⟩ := h b List.mem_cons_self
      change realPositionCharacter (A ++ B) l = _
      rw [realPositionCharacter_append (fun b hb => h b (List.mem_cons_of_mem _ hb)) B l]
      simp only [List.length_cons, Nat.add_lt_add_iff_right, Nat.add_sub_add_right]
      rfl

theorem realPositionCharacter_reverse : ∀ {ds : List RealBlock}, IsCharacterList ds →
    ∀ l : ℕ, l < ds.length →
      realPositionCharacter ds.reverse l = realPositionCharacter ds (ds.length - 1 - l)
  | [], _, l, hl => absurd hl (Nat.not_lt_zero _)
  | b :: ds, h, l, hl => by
      obtain ⟨c, rfl⟩ := h b List.mem_cons_self
      have hds : IsCharacterList ds := fun b hb => h b (List.mem_cons_of_mem _ hb)
      have hrev : IsCharacterList ds.reverse := fun b hb => hds b (List.mem_reverse.mp hb)
      rw [List.reverse_cons, realPositionCharacter_append hrev, List.length_reverse]
      simp only [List.length_cons] at hl ⊢
      split_ifs with hlt
      · rw [realPositionCharacter_reverse hds l hlt]
        have e : ds.length + 1 - 1 - l = (ds.length - 1 - l) + 1 := by omega
        rw [e]
        rfl
      · have hl' : l = ds.length := by omega
        subst hl'
        rw [Nat.sub_self, show ds.length + 1 - 1 - ds.length = 0 by omega]
        rfl

/-! ## The test vector -/

/-- **The test vector.** For a Langlands-ordered list of character blocks there is an
`O(n)`-finite function `f` of the principal series of the position characters such that, for
all `(𝔤, K)`-stable spaces `U ≠ 0` and `X` of `O(n)`-finite functions of the principal series of
the inverse characters, if every `g ↦ ∫ x(κ gᵀ) f(κ) dκ` (`x ∈ X`) lies in `nullCoeff` of `U`,
then every `x ∈ X` vanishes at `1`. -/
theorem exists_testVector (hT1 : RealBlockChartIntegrableStatement)
    (hT3 : RealBlockParabolicIntegrationStatement)
    (htemp : RealTemperedStandardIrreducibleStatement) {n : ℕ} {ds : List RealBlock}
    (hn : realRank ds = n) (hchar : IsCharacterList ds) (hord : IsRealLanglandsOrdered ds) :
    ∃ f ∈ kFiniteFunctions (principalSeries ℝ n (realPositionCharacter ds)) (unitaryCompact ℝ n),
      ∀ {U X : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)},
      U ≤ kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds)))
        (unitaryCompact ℝ n) →
      (∀ κ ∈ unitaryCompact ℝ n, ∀ u ∈ U,
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) κ u ∈ U) →
      (∀ (Y : Matrix (Fin n) (Fin n) ℝ), ∀ u ∈ U, rightDerivative (matrixModel ℝ n) Y u ∈ U) →
      U ≠ ⊥ →
      X ≤ kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds)))
        (unitaryCompact ℝ n) →
      (∀ κ ∈ unitaryCompact ℝ n, ∀ x ∈ X,
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) κ x ∈ X) →
      (∀ (Y : Matrix (Fin n) (Fin n) ℝ), ∀ x ∈ X, rightDerivative (matrixModel ℝ n) Y x ∈ X) →
      (∀ x ∈ X, (fun g => coeff x f (transposeGL g)) ∈
        nullCoeff (realPositionCharacter ds) U) →
      ∀ x ∈ X, x 1 = 0 := by
  have hχ := isSignedPower ds
  obtain ⟨p, hp⟩ := exists_signs ds
  obtain ⟨ks, hdim, hks⟩ := exists_blocks (realPositionExponent ds) (realRank ds)
    (exponent_ord hchar hord)
  have hn' : dim ks = n := hdim.trans hn
  subst hn'
  obtain ⟨av, L, -, hne⟩ := exists_jac_testVector_ne_zero hT1 ks p hχ hp hks
  have hf := testVector_mem (n := dim ks) hχ hp av L
  refine ⟨_, hf, fun hU hUK hUD hU0 hX hXK hXD hH x hx => ?_⟩
  have h := jac_eq_zero_of_transpose hT1 hT3 (realTiedIrreducible htemp) ks p hχ hp hks hU hUK
    hUD hU0 hX hXK hXD hf hH x hx
  exact (mul_eq_zero.mp h).resolve_right hne

end RealCharacterReverseKernel

open RealCharacterReverseKernel

/-- **Statement (intertwiners to the reversed module, character blocks), assuming
`RealBlockChartIntegrableStatement`, `RealBlockParabolicIntegrationStatement` and
`RealTemperedStandardIrreducibleStatement`.** Let `ds` be a list of real character blocks
(characters `sgn^ε |·|^t` of `GL_1(ℝ)`) of total rank `n` in Langlands order (real parts of the
exponents non-increasing). Every `(𝔤, K)`-intertwiner from the `O(n)`-finite functions of the
standard module of `ds` to those of the standard module of `ds.reverse` vanishes on every
proper `(𝔤, K)`-submodule. -/
def RealCharacterReverseKernelStatement : Prop :=
  RealBlockChartIntegrableStatement → RealBlockParabolicIntegrationStatement →
  RealTemperedStandardIrreducibleStatement →
  ∀ (n : ℕ) (ds : List RealBlock)
    (T : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      kFiniteFunctions (realStandardModule n ds.reverse) (unitaryCompact ℝ n))
    (W : Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))),
    realRank ds = n → RealStrictCharacterLanglandsQuotient.IsCharacterList ds →
      IsRealLanglandsOrdered ds →
      IsRealStandardIntertwiner n (realStandardRep n ds.reverse) (realStandardLie n ds.reverse)
        ds T →
        IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) W → W ≠ ⊤ →
          W ≤ LinearMap.ker T

open Langlands.LocalFactor.Archimedean RealStrictCharacterLanglandsQuotient RealReverseRecursion
  RealReverseTwist RealReverseTransfer JacquetKernel PartialJacquet JacquetDual
  MaximalParabolicIntegration GramFormula RealPrincipalSeriesDuality in
theorem realCharacterReverseKernel : RealCharacterReverseKernelStatement := by
  intro hT1 hT3 htemp n ds T W hn hchar hord hT hW hWtop
  have hχ := isSignedPower ds
  have hψ := isSignedPower ds.reverse
  have hcharr : IsCharacterList ds.reverse := fun b hb => hchar b (List.mem_reverse.mp hb)
  have hlen : ds.length = n := (realRank_eq_length hchar).symm.trans hn
  have hrevj : ∀ j : Fin n, realPositionCharacter ds.reverse (Fin.rev j) =
      realPositionCharacter ds j := by
    intro j
    rw [realPositionCharacter_reverse hchar _ (by rw [hlen]; exact (Fin.rev j).isLt)]
    congr 1
    rw [Fin.val_rev]
    omega
  have hrev1 : ∀ (j : Fin n) (z : ℝˣ), dualChar (realPositionCharacter ds.reverse) j z =
      realPositionCharacter ds (Fin.rev j) z⁻¹ := by
    intro j z
    rw [← hrevj (Fin.rev j), Fin.rev_rev, realPositionCharacter_inv hcharr]
    rfl
  have hrev2 : ∀ (j : Fin n) (z : ℝˣ), dualChar (realPositionCharacter ds) j z =
      realPositionCharacter ds.reverse (Fin.rev j) z⁻¹ := by
    intro j z
    rw [hrevj j, realPositionCharacter_inv hchar]
    rfl
  obtain ⟨f, hf, hkey⟩ := exists_testVector hT1 hT3 htemp hn hchar hord
  let S := kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)
  let Sr := kFiniteFunctions (realStandardModule n ds.reverse) (unitaryCompact ℝ n)
  have hS : ∀ w : S, (w : Langlands.GeneralLinear n ℝ → ℂ) ∈
      kFiniteFunctions (principalSeries ℝ n (realPositionCharacter ds)) (unitaryCompact ℝ n) :=
    fun w => mem_kFiniteFunctions_principalSeries w.2
  have hSr : ∀ w : Sr, (w : Langlands.GeneralLinear n ℝ → ℂ) ∈
      kFiniteFunctions (principalSeries ℝ n (realPositionCharacter ds.reverse))
        (unitaryCompact ℝ n) :=
    fun w => mem_kFiniteFunctions_principalSeries w.2
  -- the proper submodule `W`, as a space of functions
  set W' : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) := W.map S.subtype with hW'def
  have hWX : W' ≤ kFiniteFunctions (principalSeries ℝ n (realPositionCharacter ds))
      (unitaryCompact ℝ n) := by
    rintro _ ⟨w, -, rfl⟩
    exact hS w
  have hWK : ∀ k ∈ unitaryCompact ℝ n, ∀ w ∈ W',
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k w ∈ W' := by
    rintro k hk _ ⟨w, hwW, rfl⟩
    refine ⟨realStandardRep n ds ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ w, hW.1 _ w hwW, ?_⟩
    change ((realStandardRep n ds _ w : S) : Langlands.GeneralLinear n ℝ → ℂ) = _
    rw [realStandardRep_apply_coe, toUnits_mk]
    rfl
  have hWD : ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ w ∈ W',
      rightDerivative (matrixModel ℝ n) X w ∈ W' := by
    rintro X _ ⟨w, hwW, rfl⟩
    exact ⟨realStandardLie n ds (1 ⊗ₜ X) w, hW.2 _ w hwW,
      realStandardLie_one_tmul_apply_coe n ds X w⟩
  obtain ⟨⟨g, hgS⟩, hgW⟩ : ∃ g : S, g ∉ W := by
    by_contra hcon
    exact hWtop (eq_top_iff.mpr fun g _ => by_contra fun h => hcon ⟨g, h⟩)
  have hgW' : g ∉ W' := by
    rintro ⟨w, hwW, hw⟩
    apply hgW
    have : w = ⟨g, hgS⟩ := Subtype.ext hw
    rw [← this]
    exact hwW
  -- the annihilator `U` of `W`
  set U := annihilator (realPositionCharacter ds) W' hWX with hUdef
  have hU := annihilator_le W' hWX
  have hUK := annihilator_rightTranslation W' hWX hWK
  have hUD := annihilator_rightDerivative hχ W' hWX hWD
  have hU0 := annihilator_ne_bot hχ W' hWX hWK (hS ⟨g, hgS⟩) hgW'
  -- the twisted image `X` of `W`
  set X : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) :=
    ((W.map T).map Sr.subtype).map (twistLin n) with hXdef
  have hX : X ≤ kFiniteFunctions (principalSeries ℝ n (dualChar (realPositionCharacter ds)))
      (unitaryCompact ℝ n) := by
    rintro _ ⟨_, ⟨_, ⟨w, -, rfl⟩, rfl⟩, rfl⟩
    exact twistLin_mem_kFiniteFunctions hrev2 (hSr (T w))
  have hXK : ∀ k ∈ unitaryCompact ℝ n, ∀ x ∈ X,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k x ∈ X := by
    rintro k hk _ ⟨_, ⟨_, ⟨w, hwW, rfl⟩, rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨realStandardRep n ds ⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ w,
      hW.1 _ w hwW, rfl⟩, rfl⟩, ?_⟩
    change twistLin n ((T (realStandardRep n ds _ w) : Sr) : Langlands.GeneralLinear n ℝ → ℂ) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k
        (twistLin n ((T w : Sr) : Langlands.GeneralLinear n ℝ → ℂ))
    rw [rightTranslation_twistLin _ hk, hT.map_realStandardRep, realStandardRep_apply_coe,
      toUnits_mk]
  have hXD : ∀ (Y : Matrix (Fin n) (Fin n) ℝ), ∀ x ∈ X,
      rightDerivative (matrixModel ℝ n) Y x ∈ X := by
    rintro Y _ ⟨_, ⟨_, ⟨w, hwW, rfl⟩, rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨realStandardLie n ds (1 ⊗ₜ (-Yᵀ)) w, hW.2 _ w hwW, rfl⟩, rfl⟩, ?_⟩
    change twistLin n ((T (realStandardLie n ds _ w) : Sr) : Langlands.GeneralLinear n ℝ → ℂ) =
      rightDerivative (matrixModel ℝ n) Y
        (twistLin n ((T w : Sr) : Langlands.GeneralLinear n ℝ → ℂ))
    rw [rightDerivative_twistLin (hSr (T w)).1.1 Y, hT.map_realStandardLie,
      realStandardLie_one_tmul_apply_coe]
  -- the coefficient identity
  have hv : twistLin n f ∈ kFiniteFunctions
      (principalSeries ℝ n (dualChar (realPositionCharacter ds.reverse))) (unitaryCompact ℝ n) :=
    twistLin_mem_kFiniteFunctions hrev1 hf
  obtain ⟨u, hu, huv⟩ := exists_pairing_transpose hχ T hT hv
  have hH : ∀ x ∈ X, (fun g => coeff x f (transposeGL g)) ∈
      nullCoeff (realPositionCharacter ds) U := by
    rintro _ ⟨_, ⟨_, ⟨w, hwW, rfl⟩, rfl⟩, rfl⟩
    have hfun : (fun g => coeff (twistLin n (Sr.subtype (T w))) f (transposeGL g)) =
        coeff u (w : Langlands.GeneralLinear n ℝ → ℂ) := by
      funext g
      have h1 := integral_mul_inv_eq_twist ((T w : Sr) : Langlands.GeneralLinear n ℝ → ℂ)
        (twistLin n f) g
      have h2 := integral_mul_transfer hχ hψ T hT hv hu huv w g⁻¹
      have h3 := integral_mul_inv_swap hχ hu.1 (hS w).1 g
      simp only [twistLin_apply, RealReverseTwist.twist_twist] at h1 h2
      change ∫ κ, ((T w : Sr) : Langlands.GeneralLinear n ℝ → ℂ)
          (RealReverseTwist.twist ((κ : Langlands.GeneralLinear n ℝ) * transposeGL g)) * f κ
          ∂haarK n =
        ∫ κ, u ((κ : Langlands.GeneralLinear n ℝ) * g) * (w : Langlands.GeneralLinear n ℝ → ℂ) κ
          ∂haarK n
      rw [← h1, h2, h3]
    rw [hfun]
    exact Submodule.subset_span ⟨u, w, hu, hS w, fun u' hu' => hu'.2 _ ⟨w, hwW, rfl⟩, rfl⟩
  have hzero := hkey hU hUK hUD hU0 hX hXK hXD hH
  -- conclusion: `(T w)(w₀ k) = 0` for all `k ∈ O(n)`, so `T w = 0`
  intro w hw
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  change ((T w : Sr) : Langlands.GeneralLinear n ℝ → ℂ) = 0
  refine eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact (hSr (T w)).1 fun κ hκ => ?_
  have hk : w0GL n * κ ∈ unitaryCompact ℝ n := mul_mem w0GL_mem hκ
  have hx := hzero _ ⟨_, ⟨_, ⟨realStandardRep n ds ⟨_, hk⟩ w, hW.1 _ w hw, rfl⟩, rfl⟩, rfl⟩
  change ((T (realStandardRep n ds _ w) : Sr) : Langlands.GeneralLinear n ℝ → ℂ)
    (RealReverseTwist.twist 1) = 0 at hx
  rw [hT.map_realStandardRep, realStandardRep_apply_coe, toUnits_mk, RealReverseTwist.twist_one,
    TranslateFinite.rightTranslation_apply, ← mul_assoc, w0GL_mul_self, one_mul] at hx
  exact hx

end Langlands.Archimedean
