import Langlands.Global.Factors.CuspidalPairCompletedEquationReduction
import Langlands.Global.Factors.RelativeWeilLocalEulerBridge
import Langlands.Representation.Unramified.StandardHeckeSum
import Langlands.Representation.Unitary.Basic
import Langlands.Automorphic.CuspidalUnitaryLocalUnitarityProof
import Langlands.Automorphic.IrreducibleCentralCharacterStatement
import Langlands.Automorphic.HeckeTwist.CuspidalSpectralTwist
import Langlands.Automorphic.HeckeTwist.FiniteSlice
import Langlands.Automorphic.HeckeTwist.FiniteLocalTransport
import Langlands.Automorphic.LocalDeterminantCharacter

/-!
# Reduction of the cuspidal Satake bound to the existence of central characters

This module proves `Langlands.Global.CuspidalSatakeBoundReductionStatement`:
`OperatorRealization.IrreducibleCentralCharacterStatement` implies
`CuspidalSatakeBoundStatement` (theorem `Langlands.Global.cuspidalSatakeBoundReduction`).

* Local part (`Langlands.Unramified`): on a unitarizable unramified representation with
  spherical Hecke spectrum `s`, each standard Hecke eigenvalue is bounded by the number of
  left cosets in its double coset (Cauchy–Schwarz for the invariant form), this number is at
  most `q ^ (m * m + m)`, and a root bound for the Euler polynomial gives
  `‖α‖ ≤ q ^ (m * m + 2 * m)` for every Satake parameter `α`, `m = r + 1`
  (`norm_le_of_hasSphericalHeckeSpectrum`).
* Global part (`Langlands.Global.CuspidalSatakeBound`): if `T` has central character `ω`,
  the twist of `T` by the Hecke character `‖ω‖ ^ (-1 / m)` has a unitary central character,
  so its local components are unitarizable (`cuspidalUnitaryLocalUnitarity`) and satisfy the
  local bound; the twist multiplies the Satake parameters by `χ(ϖ_v)`, of norm `q_v ^ (-β)`,
  and the finitely many extra exceptional places are absorbed into the exponent
  (`exists_hasSatakeBound`).

See the paired Markdown for provenance.
-/

noncomputable section

namespace Langlands.Unramified.SatakeBound

open Correspondence MeasureTheory MinusculeCosets Polynomial

universe uF uV

section Form

variable {G : Type*} [Monoid G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}

/-- Cauchy–Schwarz for an invariant positive form: `‖⟪v, ρ g v⟫‖ ≤ re ⟪v, v⟫`. -/
theorem norm_inner_apply_le (b : InvariantPositiveForm ρ) (g : G) (v : V) :
    ‖b.inner v (ρ g v)‖ ≤ (b.inner v v).re := by
  let c : PreInnerProductSpace.Core ℂ V := b.toInnerProductCore.toCore
  let _ : Inner ℂ V := InnerProductSpace.Core.toPreInner'
  have h := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) v (ρ g v)
  have hs := InnerProductSpace.Core.norm_inner_symm (𝕜 := ℂ) (ρ g v) v
  change ‖b.inner v (ρ g v)‖ * ‖b.inner (ρ g v) v‖ ≤
    (b.inner v v).re * (b.inner (ρ g v) (ρ g v)).re at h
  change ‖b.inner (ρ g v) v‖ = ‖b.inner v (ρ g v)‖ at hs
  rw [hs, b.invariant g v v] at h
  have h0 : 0 ≤ (b.inner v v).re := b.re_inner_nonneg v
  exact (mul_self_le_mul_self_iff (norm_nonneg _) h0).mpr h

/-- Linearity of an invariant positive form in the second variable, for scalars. -/
theorem inner_smul_right (b : InvariantPositiveForm ρ) (v w : V) (c : ℂ) :
    b.inner v (c • w) = c * b.inner v w := by
  let c' : PreInnerProductSpace.Core ℂ V := b.toInnerProductCore.toCore
  let _ : Inner ℂ V := InnerProductSpace.Core.toPreInner'
  exact InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ) v w

/-- Additivity of an invariant positive form in the second variable, for finite sums. -/
theorem inner_sum_right (b : InvariantPositiveForm ρ) (v : V) {ι : Type*} (t : Finset ι)
    (f : ι → V) : b.inner v (∑ i ∈ t, f i) = ∑ i ∈ t, b.inner v (f i) := by
  let c' : PreInnerProductSpace.Core ℂ V := b.toInnerProductCore.toCore
  let _ : Inner ℂ V := InnerProductSpace.Core.toPreInner'
  let φ : V →+ ℂ :=
    { toFun := fun w => b.inner v w
      map_zero' := InnerProductSpace.Core.inner_zero_right (𝕜 := ℂ) v
      map_add' := InnerProductSpace.Core.inner_add_right (𝕜 := ℂ) v }
  exact map_sum φ f t

/-- A nonzero vector has positive norm square. -/
theorem re_inner_self_pos (b : InvariantPositiveForm ρ) {v : V} (hv : v ≠ 0) :
    0 < (b.inner v v).re := by
  let c' : PreInnerProductSpace.Core ℂ V := b.toInnerProductCore.toCore
  let _ : Inner ℂ V := InnerProductSpace.Core.toPreInner'
  refine lt_of_le_of_ne (b.re_inner_nonneg v) (fun h => hv (b.definite v ?_))
  have him := InnerProductSpace.Core.inner_self_im (𝕜 := ℂ) v
  change (b.inner v v).im = 0 at him
  exact Complex.ext (by simpa using h.symm) (by simpa using him)

/-- If `c • v = ∑ ρ(g_a) v` for a nonzero `v`, then `‖c‖` is at most the number of terms. -/
theorem norm_le_card_of_smul_eq_sum (b : InvariantPositiveForm ρ) {v : V} (hv : v ≠ 0)
    {ι : Type*} [Fintype ι] (g : ι → G) (c : ℂ) (h : c • v = ∑ a, ρ (g a) v) :
    ‖c‖ ≤ Fintype.card ι := by
  have hpos := re_inner_self_pos b hv
  have key : ‖c‖ * (b.inner v v).re ≤ (Fintype.card ι : ℝ) * (b.inner v v).re := by
    calc ‖c‖ * (b.inner v v).re ≤ ‖c‖ * ‖b.inner v v‖ :=
          mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (norm_nonneg _)
      _ = ‖b.inner v (c • v)‖ := by rw [inner_smul_right, norm_mul]
      _ = ‖∑ a, b.inner v (ρ (g a) v)‖ := by rw [h, inner_sum_right]
      _ ≤ ∑ a, ‖b.inner v (ρ (g a) v)‖ := norm_sum_le _ _
      _ ≤ ∑ _a : ι, (b.inner v v).re :=
          Finset.sum_le_sum fun a _ => norm_inner_apply_le b (g a) v
      _ = (Fintype.card ι : ℝ) * (b.inner v v).re := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact le_of_mul_le_mul_right key hpos

end Form

section CosetCount

/-- The number of labelled coset representatives is at most `q ^ (m * m + m)`. -/
theorem card_cosetIndex_le (Λ : Type*) [Fintype Λ] (hΛ : 2 ≤ Fintype.card Λ) (m i : ℕ)
    [Fintype (CosetIndex Λ m i)] :
    Fintype.card (CosetIndex Λ m i) ≤ Fintype.card Λ ^ (m * m + m) := by
  classical
  have hc : Fintype.card (CosetIndex Λ m i) =
      ∑ S : {S : Finset (Fin m) // S.card = i}, Fintype.card (RadicalPairs S.1 → Λ) := by
    convert Fintype.card_sigma (α := fun S : {S : Finset (Fin m) // S.card = i} =>
      RadicalPairs S.1 → Λ)
  rw [hc]
  calc ∑ S : {S : Finset (Fin m) // S.card = i}, Fintype.card (RadicalPairs S.1 → Λ)
        ≤ ∑ _S : {S : Finset (Fin m) // S.card = i}, Fintype.card Λ ^ (m * m) := by
        refine Finset.sum_le_sum fun S _ => ?_
        rw [Fintype.card_fun]
        refine Nat.pow_le_pow_right (by omega) ?_
        calc Fintype.card (RadicalPairs S.1) ≤ Fintype.card (Fin m × Fin m) :=
              Fintype.card_subtype_le _
          _ = m * m := by simp
    _ = Fintype.card {S : Finset (Fin m) // S.card = i} * Fintype.card Λ ^ (m * m) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ 2 ^ m * Fintype.card Λ ^ (m * m) := by
        refine Nat.mul_le_mul_right _ ?_
        calc Fintype.card {S : Finset (Fin m) // S.card = i}
              ≤ Fintype.card (Finset (Fin m)) := Fintype.card_subtype_le _
          _ = 2 ^ m := by simp
    _ ≤ Fintype.card Λ ^ m * Fintype.card Λ ^ (m * m) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hΛ m)
    _ = Fintype.card Λ ^ (m * m + m) := by rw [← pow_add, add_comm]

end CosetCount

section Roots

/-- A root bound from coefficient bounds: if every coefficient of the Euler polynomial of
`s` has norm at most `B`, then every parameter `α ∈ s` has `‖α‖ ≤ max 1 (n * B)`. -/
theorem norm_le_of_mem_of_coeff_le {n : ℕ} (s : Eigenvalues n) {α : ℂˣ}
    (hα : α ∈ (s : Multiset ℂˣ)) (B : ℝ)
    (hB : ∀ k, ‖(Eigenvalues.eulerPolynomial s).coeff k‖ ≤ B) :
    ‖(α : ℂ)‖ ≤ max 1 (n * B) := by
  rcases le_or_gt ‖(α : ℂ)‖ 1 with h1 | h1
  · exact le_max_of_le_left h1
  refine le_max_of_le_right ?_
  set y : ℂ := (α : ℂ)⁻¹ with hy
  have hα0 : (α : ℂ) ≠ 0 := α.ne_zero
  have hny : ‖y‖ = ‖(α : ℂ)‖⁻¹ := by rw [hy, norm_inv]
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hy1 : ‖y‖ ≤ 1 := by
    rw [hny]
    exact inv_le_one_of_one_le₀ h1.le
  have hroot : (Eigenvalues.eulerPolynomial s).eval y = 0 := by
    rw [Eigenvalues.eulerPolynomial, Polynomial.eval_multiset_prod]
    apply Multiset.prod_eq_zero
    rw [Multiset.map_map]
    refine Multiset.mem_map.2 ⟨α, hα, ?_⟩
    simp [hy, hα0]
  rw [Polynomial.eval_eq_sum_range, Eigenvalues.eulerPolynomial_natDegree,
    Finset.sum_range_succ'] at hroot
  have hc0 : (Eigenvalues.eulerPolynomial s).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Eigenvalues.eulerPolynomial_eval_zero]
  rw [hc0, pow_zero, mul_one] at hroot
  have hsum : (1 : ℝ) ≤ n * B * ‖y‖ := by
    have h1' : (1 : ℂ) = -∑ k ∈ Finset.range n,
        (Eigenvalues.eulerPolynomial s).coeff (k + 1) * y ^ (k + 1) := by
      linear_combination hroot
    calc (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
      _ = ‖∑ k ∈ Finset.range n,
          (Eigenvalues.eulerPolynomial s).coeff (k + 1) * y ^ (k + 1)‖ := by
          rw [h1', norm_neg]
      _ ≤ ∑ k ∈ Finset.range n,
          ‖(Eigenvalues.eulerPolynomial s).coeff (k + 1) * y ^ (k + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range n, B * ‖y‖ := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, norm_pow]
          exact mul_le_mul (hB _) (pow_le_of_le_one hy0 hy1 (Nat.succ_ne_zero k))
            (by positivity) ((norm_nonneg _).trans (hB 0))
      _ = n * B * ‖y‖ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]
  have hprod : ‖(α : ℂ)‖ * ‖y‖ = 1 := by
    rw [hny, mul_inv_cancel₀ (norm_ne_zero_iff.2 hα0)]
  calc ‖(α : ℂ)‖ = ‖(α : ℂ)‖ * 1 := (mul_one _).symm
    _ ≤ ‖(α : ℂ)‖ * (n * B * ‖y‖) := mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = n * B * (‖(α : ℂ)‖ * ‖y‖) := by ring
    _ = n * B := by rw [hprod, mul_one]

end Roots

end Langlands.Unramified.SatakeBound

namespace Langlands.Unramified

open Correspondence MeasureTheory MinusculeCosets

universe uF' uV'

section LocalBound

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF'} p)

local instance satakeFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance satakeFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance satakeFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance satakeGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopology n
local instance satakeGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopologicalGroup n
local instance satakeGeneralLinearT2 (n : ℕ) : T2Space (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearT2Space n
local instance satakeGeneralLinearMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance satakeGeneralLinearBorel (n : ℕ) :
    BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩

/-- On a unitarizable irreducible admissible representation with spherical Hecke spectrum
`s`, each standard Hecke scalar is bounded by the number of left cosets in its double coset. -/
theorem norm_standardHeckeScalar_le_card {r : ℕ} (A : AutomorphicObject.{uF', uV'} F r.succPNat)
    (b : InvariantPositiveForm A.obj.representation) {s : Eigenvalues (r + 1)}
    (hs : HasSphericalHeckeSpectrum F A s) (i : Fin (r + 2)) :
    ‖standardHeckeScalar F s i‖ ≤
      Fintype.card (CosetIndex F.canonicalTopologicalData.ResidueField (r + 1) i.val) := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hs.1
  let w : fixedVectors A.obj.representation (sphericalSubgroup F r) := ⟨x, hx⟩
  have h1 := congrArg Subtype.val (hs.2 i w)
  have h2 := standardHecke_cornerAction_eq_sum F A.obj.representation A.obj.isSmooth i w
  exact SatakeBound.norm_le_card_of_smul_eq_sum b hx0 _ _ (h1.symm.trans h2)

/-- The residue cardinality is at least two. -/
theorem two_le_residueCardinality :
    2 ≤ F.canonicalTopologicalData.residueCardinality := by
  rw [PadicField.TopologicalData.residueCardinality, Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- The Satake parameters of a unitarizable representation with spherical Hecke spectrum `s`
have norm at most `q ^ (m * m + 2 * m)`, where `q` is the residue cardinality and
`m = r + 1`. -/
theorem norm_le_of_hasSphericalHeckeSpectrum {r : ℕ}
    (A : AutomorphicObject.{uF', uV'} F r.succPNat) (hU : IsUnitarizable A.obj.representation)
    {s : Eigenvalues (r + 1)} (hs : HasSphericalHeckeSpectrum F A s) {α : ℂˣ}
    (hα : α ∈ (s : Multiset ℂˣ)) :
    ‖(α : ℂ)‖ ≤ (F.canonicalTopologicalData.residueCardinality : ℝ) ^
      ((r + 1) * (r + 1) + 2 * (r + 1)) := by
  obtain ⟨b⟩ := hU
  set q := F.canonicalTopologicalData.residueCardinality with hq
  have hq2 : 2 ≤ q := two_le_residueCardinality F
  have hcard : Fintype.card F.canonicalTopologicalData.ResidueField = q := by
    rw [hq, PadicField.TopologicalData.residueCardinality, Nat.card_eq_fintype_card]
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hcoeff : ∀ k, ‖(Eigenvalues.eulerPolynomial s).coeff k‖ ≤ (q : ℝ) ^ ((r + 1) * (r + 1) + (r + 1)) := by
    intro k
    rcases le_or_gt k (r + 1) with hk | hk
    · let i : Fin (r + 2) := ⟨k, by omega⟩
      have h1 := norm_standardHeckeScalar_le_card F A b hs i
      have h2 := SatakeBound.card_cosetIndex_le F.canonicalTopologicalData.ResidueField
        (by rw [hcard]; exact hq2) (r + 1) i.val
      rw [hcard] at h2
      have h2' : (Fintype.card (CosetIndex F.canonicalTopologicalData.ResidueField (r + 1)
          i.val) : ℝ) ≤ (q : ℝ) ^ ((r + 1) * (r + 1) + (r + 1)) := by exact_mod_cast h2
      have h3 : ‖standardHeckeScalar F s i‖ ≤ (q : ℝ) ^ ((r + 1) * (r + 1) + (r + 1)) :=
        h1.trans h2'
      have hsq : (1 : ℝ) ≤ Real.sqrt q := Real.one_le_sqrt.2 hqR
      have h4 : ‖standardHeckeScalar F s i‖ =
          Real.sqrt q ^ (k * (r + 1 - k)) * ‖(Eigenvalues.eulerPolynomial s).coeff k‖ := by
        rw [standardHeckeScalar, elementaryCoefficient, norm_mul, norm_mul, norm_pow, norm_pow,
          norm_neg, norm_one, one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
      calc ‖(Eigenvalues.eulerPolynomial s).coeff k‖
          ≤ Real.sqrt q ^ (k * (r + 1 - k)) * ‖(Eigenvalues.eulerPolynomial s).coeff k‖ :=
            le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hsq)
        _ ≤ (q : ℝ) ^ ((r + 1) * (r + 1) + (r + 1)) := h4 ▸ h3
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by
        rw [Eigenvalues.eulerPolynomial_natDegree]; exact hk), norm_zero]
      positivity
  have hroot := SatakeBound.norm_le_of_mem_of_coeff_le s hα _ hcoeff
  refine hroot.trans (max_le (one_le_pow₀ hqR) ?_)
  have hmq : ((r + 1 : ℕ) : ℝ) ≤ (q : ℝ) ^ (r + 1) := by
    have h2m : ((r + 1 : ℕ) : ℝ) ≤ 2 ^ (r + 1) := by exact_mod_cast (Nat.lt_two_pow_self).le
    exact h2m.trans (pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hq2) (r + 1))
  calc ((r + 1 : ℕ) : ℝ) * (q : ℝ) ^ ((r + 1) * (r + 1) + (r + 1)) ≤ (q : ℝ) ^ (r + 1) * (q : ℝ) ^ ((r + 1) * (r + 1) + (r + 1)) :=
        mul_le_mul_of_nonneg_right hmq (by positivity)
    _ = (q : ℝ) ^ ((r + 1) * (r + 1) + 2 * (r + 1)) := by rw [← pow_add]; ring_nf

end LocalBound

end Langlands.Unramified

namespace Langlands.Global

open NumberField CuspidalPairFunctionalEquation
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)

universe u uQ

namespace CuspidalSatakeBound

/-- The Hecke character `x ↦ ‖ω x‖ ^ a`, for a Hecke character `ω` and a real `a`. -/
def normRpow {K : Type*} [Field K] [NumberField K] (ω : HeckeCharacter K) (a : ℝ) :
    HeckeCharacter K where
  toFun x := Units.mk0 (((‖(ω x : ℂ)‖ ^ a : ℝ)) : ℂ) (by
    have h : 0 < ‖(ω x : ℂ)‖ := norm_pos_iff.2 (ω x).ne_zero
    exact_mod_cast (Real.rpow_pos_of_pos h a).ne')
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp only [map_mul, Units.val_mul, norm_mul, Units.val_mk0]
    rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    push_cast
    ring
  continuous_toFun := by
    have hc : Continuous fun x => ‖((ω x : ℂˣ) : ℂ)‖ :=
      (Units.continuous_val.comp ω.continuous).norm
    have hpos : ∀ x, ‖((ω x : ℂˣ) : ℂ)‖ ≠ 0 := fun x => norm_ne_zero_iff.2 (ω x).ne_zero
    have hr : Continuous fun x => (((‖((ω x : ℂˣ) : ℂ)‖ ^ a : ℝ)) : ℂ) :=
      Complex.continuous_ofReal.comp (hc.rpow_const fun x => Or.inl (hpos x))
    refine Units.continuous_iff.2 ⟨hr, ?_⟩
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
    refine hr.inv₀ fun x => ?_
    have h : 0 < ‖(ω x : ℂ)‖ := norm_pos_iff.2 (ω x).ne_zero
    exact_mod_cast (Real.rpow_pos_of_pos h a).ne'

@[simp] theorem normRpow_apply {K : Type*} [Field K] [NumberField K] (ω : HeckeCharacter K)
    (a : ℝ) (x : IdeleClasses K) :
    ((normRpow ω a x : ℂˣ) : ℂ) = (((‖(ω x : ℂ)‖ ^ a : ℝ)) : ℂ) := rfl

/-- `‖ω x‖ ^ (-1 / n) ^ n * ω x` has norm one. -/
theorem norm_normRpow_pow_mul {K : Type*} [Field K] [NumberField K] (ω : HeckeCharacter K)
    (n : ℕ) (hn : n ≠ 0) (x : IdeleClasses K) :
    ‖(((normRpow ω (-1 / (n : ℝ)) ^ n * ω) x : ℂˣ) : ℂ)‖ = 1 := by
  have h : 0 < ‖(ω x : ℂ)‖ := norm_pos_iff.2 (ω x).ne_zero
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [ContinuousMonoidHom.mul_apply, ContinuousMonoidHom.pow_apply, Units.val_mul,
    Units.val_pow_eq_pow_val, norm_mul, norm_pow, normRpow_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg h.le _), ← Real.rpow_natCast, ← Real.rpow_mul h.le,
    div_mul_cancel₀ _ hn', Real.rpow_neg_one, inv_mul_cancel₀ h.ne']

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- With a unitary central character, the Satake parameters at every place outside the
exceptional set of a presentation satisfy `‖α‖ ≤ q_v ^ (m * m + 2 * m)`, `m = r + 1`. -/
theorem norm_le_of_hasUnitaryCentralCharacter {r : ℕ} {T : CuspidalOperatorRealization F r}
    (hT : ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T)
    (Q : CuspidalSpectralPresentation.{u, uQ} T) (v : FinitePlace F) (hv : v ∉ Q.exceptional)
    {α : ℂˣ}
    (hα : α ∈ ((Q.spectralSystem.eigenvalues v hv : Unramified.Eigenvalues (r + 1)) :
      Multiset ℂˣ)) :
    ‖(α : ℂ)‖ ≤ (residueCardinality v : ℝ) ^ ((r + 1) * (r + 1) + 2 * (r + 1)) := by
  have hI : (Q.localComponent v).IsIrreducible :=
    (Q.presentation.localComponent_isIrreducible_iff Q.finiteSlice.nonzero v).mpr
      (Q.unramified.irreducible v hv)
  have hA : (Q.localComponent v).IsAdmissible :=
    (Q.presentation.localComponent_isAdmissible_iff Q.finiteSlice.nonzero v).mpr
      (Q.unramified.admissible v hv)
  have hU := Automorphic.cuspidalUnitaryLocalUnitarity.{u, uQ} F r T hT Q v hI hA
  have hs : Unramified.HasSphericalHeckeSpectrum (CompletionPadic.padicField v)
      ((Q.localComponent v).padicObject hI hA) (Q.spectralSystem.eigenvalues v hv) :=
    Q.hasSpectrum v hv
  exact Unramified.norm_le_of_hasSphericalHeckeSpectrum _ _ hU hs hα

omit [CompactSpace (AdeleQuotient F)] in
/-- The values of a Hecke character at the chosen uniformizers have norm `q_v ^ (-β)` for a
single real `β`. -/
theorem exists_norm_finiteUniformizerValue (χ : HeckeCharacter F) :
    ∃ β : ℝ, ∀ v : FinitePlace F,
      ‖(χ.finiteUniformizerValue v : ℂ)‖ = (residueCardinality v : ℝ) ^ (-β) := by
  obtain ⟨β, hβ⟩ := HeckeEulerProduct.exists_norm_finiteComponent_uniformizer χ
  refine ⟨β, fun v => ?_⟩
  have h := hβ v
  rw [CompletionPadic.topologicalData_eq_canonicalTopologicalData] at h
  rw [CuspidalPairEulerConvergence.residueCardinality_eq_absNorm]
  exact h

/-- If `T` has central character `ω`, the twist of `T` by `‖ω‖ ^ (-1 / (r + 1))` has a
unitary central character. -/
theorem hasUnitaryCentralCharacter_heckeDeterminantTwist {r : ℕ}
    (T : CuspidalOperatorRealization F r) (ω : HeckeCharacter F) (hω : T.HasCentralCharacter ω) :
    ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter
      (T.heckeDeterminantTwist (normRpow ω (-1 / ((r + 1 : ℕ) : ℝ)))) := by
  refine ⟨normRpow ω (-1 / ((r + 1 : ℕ) : ℝ)) ^ (r + 1) * ω,
    norm_normRpow_pow_mul ω (r + 1) (Nat.succ_ne_zero r), ?_⟩
  change (T.realization.heckeDeterminantTwist _).toFiniteRealization.HasCentralCharacter _
  rw [OperatorRealization.toFiniteRealization_heckeDeterminantTwist]
  exact T.realization.toFiniteRealization.heckeDeterminantTwist_hasCentralCharacter _ ω hω

/-- A cuspidal realization with a central character satisfies the Satake bound in every
spectral presentation. -/
theorem exists_hasSatakeBound {r : ℕ} (T : CuspidalOperatorRealization F r)
    (ω : HeckeCharacter F) (hω : T.HasCentralCharacter ω)
    (P : CuspidalSpectralPresentation.{u, uQ} T) : ∃ C : ℝ, HasSatakeBound P C := by
  classical
  set χ := normRpow ω (-1 / ((r + 1 : ℕ) : ℝ)) with hχ
  have hT' := hasUnitaryCentralCharacter_heckeDeterminantTwist T ω hω
  let Q := P.heckeDeterminantTwist χ
  obtain ⟨β, hβ⟩ := exists_norm_finiteUniformizerValue χ
  set N : ℕ := (r + 1) * (r + 1) + 2 * (r + 1) with hN
  let c : FinitePlace F → ℝ := fun v =>
    if hv : v ∈ P.exceptional then 0 else
      (((P.spectralSystem.eigenvalues v hv : Unramified.Eigenvalues (r + 1)) :
        Multiset ℂˣ).map fun α : ℂˣ => |Real.logb (residueCardinality v) ‖(α : ℂ)‖|).sum
  have hc0 : ∀ v, 0 ≤ c v := by
    intro v
    simp only [c]
    split_ifs
    · exact le_rfl
    · refine Multiset.sum_nonneg fun x hx => ?_
      obtain ⟨a, _, rfl⟩ := Multiset.mem_map.1 hx
      exact abs_nonneg _
  refine ⟨max ((N : ℝ) + β) (∑ v ∈ Q.exceptional, c v), fun v hv α hα => ?_⟩
  have hq2 : (2 : ℝ) ≤ residueCardinality v := by
    exact_mod_cast CuspidalPairEulerConvergence.two_le_residueCardinality v
  have hq0 : (0 : ℝ) < residueCardinality v := by linarith
  have hq1 : (1 : ℝ) ≤ residueCardinality v := by linarith
  have hα0 : 0 < ‖(α : ℂ)‖ := norm_pos_iff.2 α.ne_zero
  by_cases hvQ : v ∈ Q.exceptional
  · have hlog : ‖(α : ℂ)‖ = (residueCardinality v : ℝ) ^
        Real.logb (residueCardinality v) ‖(α : ℂ)‖ :=
      (Real.rpow_logb hq0 (by linarith) hα0).symm
    have h1 : Real.logb (residueCardinality v) ‖(α : ℂ)‖ ≤ c v := by
      have hcv : c v = (((P.spectralSystem.eigenvalues v hv : Unramified.Eigenvalues (r + 1)) :
          Multiset ℂˣ).map fun α : ℂˣ => |Real.logb (residueCardinality v) ‖(α : ℂ)‖|).sum :=
        by simp only [c, hv, ↓reduceDIte]
      rw [hcv]
      exact (le_abs_self _).trans (Multiset.single_le_sum (fun x hx => by
        obtain ⟨a, _, rfl⟩ := Multiset.mem_map.1 hx
        exact abs_nonneg _) _ (Multiset.mem_map_of_mem _ hα))
    have h2 : c v ≤ ∑ w ∈ Q.exceptional, c w :=
      Finset.single_le_sum (f := c) (fun w _ => hc0 w) hvQ
    rw [hlog]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (h1.trans (h2.trans (le_max_right _ _)))
  · have hmem : χ.finiteUniformizerValue v * α ∈
        ((Q.spectralSystem.eigenvalues v hvQ : Unramified.Eigenvalues (r + 1)) :
          Multiset ℂˣ) :=
      Multiset.mem_map_of_mem _ hα
    have hb := norm_le_of_hasUnitaryCentralCharacter hT' Q v hvQ hmem
    rw [Units.val_mul, norm_mul, hβ v, ← hN] at hb
    have hqN : (residueCardinality v : ℝ) ^ N = (residueCardinality v : ℝ) ^ (N : ℝ) :=
      (Real.rpow_natCast _ N).symm
    rw [hqN] at hb
    calc ‖(α : ℂ)‖ = (residueCardinality v : ℝ) ^ β *
          ((residueCardinality v : ℝ) ^ (-β) * ‖(α : ℂ)‖) := by
          rw [← mul_assoc, ← Real.rpow_add hq0, add_neg_cancel, Real.rpow_zero, one_mul]
      _ ≤ (residueCardinality v : ℝ) ^ β * (residueCardinality v : ℝ) ^ (N : ℝ) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (residueCardinality v : ℝ) ^ ((N : ℝ) + β) := by
          rw [Real.rpow_add hq0, mul_comm]
      _ ≤ (residueCardinality v : ℝ) ^ max ((N : ℝ) + β) (∑ w ∈ Q.exceptional, c w) :=
          Real.rpow_le_rpow_of_exponent_le hq1 (le_max_left _ _)

end CuspidalSatakeBound

/-- Reduction of `CuspidalSatakeBoundStatement` to the existence of central characters of
irreducible operator realizations (`OperatorRealization.IrreducibleCentralCharacterStatement`). -/
def CuspidalSatakeBoundReductionStatement : Prop :=
  OperatorRealization.IrreducibleCentralCharacterStatement.{u} →
    CuspidalSatakeBoundStatement.{u, uQ}

theorem cuspidalSatakeBoundReduction : CuspidalSatakeBoundReductionStatement.{u, uQ} := by
  intro hcc F _ _ _ r T P _
  obtain ⟨ω, hω, -⟩ := hcc F (r + 1) T.realization T.irreducible
  exact CuspidalSatakeBound.exists_hasSatakeBound T ω hω P

end Langlands.Global
