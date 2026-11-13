import Langlands.Shimura.LevelHeckeAlgebra
import Langlands.Algebra.UnitalSeparationProof

/-! # The positive involution of the Hecke algebra of a compact open subgroup

For a compact open subgroup `K` of a topological group `G`, the Hecke algebra
`ℂ[G/K]^K` (`Langlands.Shimura.LevelHecke.LevelHeckeAlgebra`) carries the
involution `a* (g K) = conj (a (g⁻¹ K))`. It is anti-multiplicative and positive:
`(a * a*)(K) = ∑_{z} |a z|²`. With the unital separation lemma (Renard B.III), every
element lying in all maximal left ideals vanishes when `G/K` is countable.
-/

noncomputable section

open Langlands.Induction
open scoped ComplexConjugate

universe uG

namespace Langlands.Shimura.LevelHecke.LevelHeckeAlgebra

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable (K : OpenSubgroup G)

/-- The function on the cosets `G ⧸ K` underlying an element of the Hecke algebra. -/
def coeffs (a : LevelHeckeAlgebra ℂ K.toSubgroup) : G ⧸ K.toSubgroup →₀ ℂ :=
  (a : HeckeSpace ℂ K.toSubgroup K.toSubgroup).1

variable {K}

theorem ext_coeffs {a b : LevelHeckeAlgebra ℂ K.toSubgroup} (h : coeffs K a = coeffs K b) :
    a = b :=
  Subtype.ext h

@[simp] theorem coeffs_zero : coeffs K (0 : LevelHeckeAlgebra ℂ K.toSubgroup) = 0 := rfl

/-- The coefficients are invariant under the left action of `K`. -/
theorem coeffs_smul (a : LevelHeckeAlgebra ℂ K.toSubgroup) {k : G} (hk : k ∈ K)
    (z : G ⧸ K.toSubgroup) : coeffs K a (k • z) = coeffs K a z := by
  have h : permRep ℂ K.toSubgroup k⁻¹ (coeffs K a) = coeffs K a :=
    (a : HeckeSpace ℂ K.toSubgroup K.toSubgroup).property ⟨k⁻¹, K.toSubgroup.inv_mem hk⟩
  have h2 := DFunLike.congr_fun h z
  rw [permutation_apply, inv_inv] at h2
  exact h2

theorem coeffs_mk_mul (a : LevelHeckeAlgebra ℂ K.toSubgroup) {k : G} (hk : k ∈ K) (g : G) :
    coeffs K a ((k * g : G) : G ⧸ K.toSubgroup) = coeffs K a (g : G ⧸ K.toSubgroup) := by
  change coeffs K a (k • (g : G ⧸ K.toSubgroup)) = _
  exact coeffs_smul a hk _

/-- The value at `(out q)⁻¹ • z` only depends on the coset `q`. -/
theorem coeffs_out_inv_smul (b : LevelHeckeAlgebra ℂ K.toSubgroup) (h : G)
    (z : G ⧸ K.toSubgroup) :
    coeffs K b ((Quotient.out (h : G ⧸ K.toSubgroup) : G)⁻¹ • z) = coeffs K b (h⁻¹ • z) := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K.toSubgroup h
  rw [hk, mul_inv_rev, mul_smul, coeffs_smul b (K.toSubgroup.inv_mem k.2)]

/-- The convolution formula, as a finite sum over the support of the left factor. -/
theorem coeffs_mul_sum (a b : LevelHeckeAlgebra ℂ K.toSubgroup) (z : G ⧸ K.toSubgroup) :
    coeffs K (a * b) z =
      ∑ q ∈ (coeffs K a).support,
        coeffs K a q * coeffs K b ((Quotient.out q : G)⁻¹ • z) :=
  heckeMul_apply K.toSubgroup K.toSubgroup K.toSubgroup a b z

/-- The convolution formula `(a * b)(z) = ∑ᶠ_q a(q) b((out q)⁻¹ z)`. -/
theorem coeffs_mul (a b : LevelHeckeAlgebra ℂ K.toSubgroup) (z : G ⧸ K.toSubgroup) :
    coeffs K (a * b) z =
      ∑ᶠ q : G ⧸ K.toSubgroup, coeffs K a q * coeffs K b ((Quotient.out q : G)⁻¹ • z) := by
  rw [coeffs_mul_sum, finsum_eq_sum_of_support_subset _ (s := (coeffs K a).support)]
  intro q hq
  rw [Function.mem_support] at hq
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h
  apply hq
  rw [h, zero_mul]

theorem support_mul_finite (a : LevelHeckeAlgebra ℂ K.toSubgroup) (f : G ⧸ K.toSubgroup → ℂ) :
    (Function.support fun q => coeffs K a q * f q).Finite := by
  refine (coeffs K a).support.finite_toSet.subset fun q hq => ?_
  rw [Function.mem_support] at hq
  rw [Finset.mem_coe, Finsupp.mem_support_iff]
  intro h
  apply hq
  rw [h, zero_mul]

/-! ## The involution -/

/-- The function `z ↦ conj (a ((out z)⁻¹ K))`. -/
def involutionFun (a : LevelHeckeAlgebra ℂ K.toSubgroup) (z : G ⧸ K.toSubgroup) : ℂ :=
  conj (coeffs K a (((Quotient.out z : G)⁻¹ : G) : G ⧸ K.toSubgroup))

theorem involutionFun_mk (a : LevelHeckeAlgebra ℂ K.toSubgroup) (g : G) :
    involutionFun a (g : G ⧸ K.toSubgroup) = conj (coeffs K a ((g⁻¹ : G) : G ⧸ K.toSubgroup)) := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K.toSubgroup g
  unfold involutionFun
  rw [hk, mul_inv_rev, coeffs_mk_mul a (K.toSubgroup.inv_mem k.2)]

variable [IsTopologicalGroup G]

/-- Orbits of a compact open subgroup on `G ⧸ K` are finite. -/
theorem finite_orbit (hK : IsCompact (K : Set G)) (g : G) :
    (MulAction.orbit K.toSubgroup ((g : G) : G ⧸ K.toSubgroup)).Finite := by
  have : Finite (HeckeCosets (⟨K, hK⟩ : CompactOpenLevel G) ⟨K, hK⟩ g) :=
    finite_heckeCosets _ _ g
  exact (Set.finite_range (cosetPoint (⟨K, hK⟩ : CompactOpenLevel G) ⟨K, hK⟩ g)).subset
    fun z hz => (mem_range_cosetPoint (⟨K, hK⟩ : CompactOpenLevel G) ⟨K, hK⟩ g z).mpr hz

theorem involutionFun_support_finite (hK : IsCompact (K : Set G))
    (a : LevelHeckeAlgebra ℂ K.toSubgroup) : (Function.support (involutionFun a)).Finite := by
  refine (Set.Finite.biUnion (coeffs K a).support.finite_toSet
    fun q _ => finite_orbit hK ((Quotient.out q : G)⁻¹)).subset ?_
  intro z hz
  rw [Function.mem_support] at hz
  have hq : (((Quotient.out z : G)⁻¹ : G) : G ⧸ K.toSubgroup) ∈ (coeffs K a).support := by
    rw [Finsupp.mem_support_iff]
    intro h
    apply hz
    rw [involutionFun, h, map_zero]
  refine Set.mem_biUnion hq ?_
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K.toSubgroup ((Quotient.out z : G)⁻¹)
  rw [MulAction.mem_orbit_iff]
  refine ⟨k, ?_⟩
  change (k : G) • ((((Quotient.out
      ((((Quotient.out z : G)⁻¹ : G) : G ⧸ K.toSubgroup)) : G))⁻¹ : G) : G ⧸ K.toSubgroup) = z
  rw [hk, mul_inv_rev, inv_inv, MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel, one_mul]
  exact QuotientGroup.out_eq' z

variable (hK : IsCompact (K : Set G))

/-- The involution `a* (g K) = conj (a (g⁻¹ K))` of the Hecke algebra of `K`. -/
def involution (a : LevelHeckeAlgebra ℂ K.toSubgroup) : LevelHeckeAlgebra ℂ K.toSubgroup :=
  (⟨Finsupp.ofSupportFinite (involutionFun a) (involutionFun_support_finite hK a), fun k => by
    ext z
    change permutation ℂ G (G ⧸ K.toSubgroup) ℂ (k : G)
      (Finsupp.ofSupportFinite (involutionFun a) (involutionFun_support_finite hK a)) z =
        Finsupp.ofSupportFinite (involutionFun a) (involutionFun_support_finite hK a) z
    rw [permutation_apply]
    change involutionFun a _ = involutionFun a _
    induction z using QuotientGroup.induction_on with
    | H g =>
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, involutionFun_mk, involutionFun_mk,
        mul_inv_rev, inv_inv, QuotientGroup.mk_mul_of_mem _ k.2]⟩ :
    HeckeSpace ℂ K.toSubgroup K.toSubgroup)

theorem coeffs_involution (a : LevelHeckeAlgebra ℂ K.toSubgroup) (z : G ⧸ K.toSubgroup) :
    coeffs K (involution hK a) z = involutionFun a z := rfl

theorem coeffs_involution_mk (a : LevelHeckeAlgebra ℂ K.toSubgroup) (g : G) :
    coeffs K (involution hK a) (g : G ⧸ K.toSubgroup) =
      conj (coeffs K a ((g⁻¹ : G) : G ⧸ K.toSubgroup)) :=
  involutionFun_mk a g

theorem involution_involution (a : LevelHeckeAlgebra ℂ K.toSubgroup) :
    involution hK (involution hK a) = a := by
  apply ext_coeffs
  ext z
  induction z using QuotientGroup.induction_on with
  | H g =>
    rw [coeffs_involution_mk, coeffs_involution_mk, inv_inv, Complex.conj_conj]

theorem involution_zero : involution hK (0 : LevelHeckeAlgebra ℂ K.toSubgroup) = 0 := by
  apply ext_coeffs
  ext z
  induction z using QuotientGroup.induction_on with
  | H g => simp only [coeffs_involution_mk, coeffs_zero, Finsupp.zero_apply, map_zero]

/-- The involution is anti-multiplicative. -/
theorem involution_mul (a b : LevelHeckeAlgebra ℂ K.toSubgroup) :
    involution hK (a * b) = involution hK b * involution hK a := by
  apply ext_coeffs
  ext z
  induction z using QuotientGroup.induction_on with
  | H g =>
    rw [coeffs_involution_mk, coeffs_mul, coeffs_mul,
      map_finsum _ (support_mul_finite a _),
      ← finsum_comp_equiv (MulAction.toPerm g⁻¹ : G ⧸ K.toSubgroup ≃ G ⧸ K.toSubgroup)]
    refine finsum_congr fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H h =>
      change conj (coeffs K a (g⁻¹ • (h : G ⧸ K.toSubgroup)) *
          coeffs K b ((Quotient.out (g⁻¹ • (h : G ⧸ K.toSubgroup)) : G)⁻¹ •
            ((g⁻¹ : G) : G ⧸ K.toSubgroup))) =
        coeffs K (involution hK b) (h : G ⧸ K.toSubgroup) *
          coeffs K (involution hK a)
            ((Quotient.out (h : G ⧸ K.toSubgroup) : G)⁻¹ • (g : G ⧸ K.toSubgroup))
      rw [MulAction.Quotient.smul_mk, smul_eq_mul]
      rw [coeffs_out_inv_smul, coeffs_out_inv_smul, MulAction.Quotient.smul_mk,
        MulAction.Quotient.smul_mk, smul_eq_mul, smul_eq_mul, coeffs_involution_mk,
        coeffs_involution_mk]
      simp only [mul_inv_rev, inv_inv, mul_inv_cancel_right]
      rw [map_mul, mul_comm]

theorem involution_pow_of_involution_eq (y : LevelHeckeAlgebra ℂ K.toSubgroup)
    (hy : involution hK y = y) (m : ℕ) : involution hK (y ^ (m + 1)) = y ^ (m + 1) := by
  induction m with
  | zero => rw [zero_add, pow_one, hy]
  | succ m ih => rw [pow_succ, involution_mul, ih, hy, ← pow_succ', pow_succ]

/-- Positivity: `(a * a*)(K) = ∑_z |a z|²`, so `a * a* = 0` forces `a = 0`. -/
theorem eq_zero_of_mul_involution_eq_zero (a : LevelHeckeAlgebra ℂ K.toSubgroup)
    (h : a * involution hK a = 0) : a = 0 := by
  have h1 := congrArg (fun x => coeffs K x ((1 : G) : G ⧸ K.toSubgroup)) h
  simp only [coeffs_zero, Finsupp.zero_apply] at h1
  rw [coeffs_mul_sum] at h1
  have hterm : ∀ q : G ⧸ K.toSubgroup,
      coeffs K a q * coeffs K (involution hK a)
          ((Quotient.out q : G)⁻¹ • ((1 : G) : G ⧸ K.toSubgroup)) =
        (Complex.normSq (coeffs K a q) : ℂ) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [coeffs_out_inv_smul, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
        coeffs_involution_mk, inv_inv, Complex.mul_conj]
  simp only [hterm] at h1
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun q _ => Complex.normSq_nonneg _] at h1
  apply ext_coeffs
  rw [coeffs_zero]
  ext q
  rw [Finsupp.zero_apply]
  by_contra hq
  exact hq (Complex.normSq_eq_zero.mp (h1 q (Finsupp.mem_support_iff.mpr hq)))

/-- A self-adjoint nilpotent element vanishes. -/
theorem eq_zero_of_isNilpotent_of_involution_eq (y : LevelHeckeAlgebra ℂ K.toSubgroup)
    (hy : involution hK y = y) (hn : IsNilpotent y) : y = 0 := by
  obtain ⟨n, hn⟩ := hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · rw [pow_zero] at hn
        rw [← mul_one y, hn, mul_zero]
      · rwa [pow_one] at hn
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      have hm : y ^ ((m + 1) / 2 + 1) = 0 := by
        apply eq_zero_of_mul_involution_eq_zero hK
        rw [involution_pow_of_involution_eq hK y hy, ← pow_add]
        exact pow_eq_zero_of_le (by omega) hn
      exact ih ((m + 1) / 2 + 1) (by omega) hm

omit [IsTopologicalGroup G] in
/-- The Hecke algebra of `K` has at most countable dimension when `G ⧸ K` is countable. -/
theorem rank_le_aleph0 [Countable (G ⧸ K.toSubgroup)] :
    Module.rank ℂ (LevelHeckeAlgebra ℂ K.toSubgroup) ≤ Cardinal.aleph0 := by
  have h1 : Module.rank ℂ (HeckeSpace ℂ K.toSubgroup K.toSubgroup) ≤
      Module.rank ℂ (G ⧸ K.toSubgroup →₀ ℂ) := Submodule.rank_le _
  rw [rank_finsupp_self] at h1
  exact h1.trans (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0)

include hK in
/-- An element of the Hecke algebra of a compact open subgroup of countable index lying in
every maximal left ideal vanishes. -/
theorem eq_zero_of_forall_mem_isCoatom [Countable (G ⧸ K.toSubgroup)]
    (b : LevelHeckeAlgebra ℂ K.toSubgroup)
    (hb : ∀ I : Submodule (LevelHeckeAlgebra ℂ K.toSubgroup) (LevelHeckeAlgebra ℂ K.toSubgroup),
      IsCoatom I → b ∈ I) : b = 0 := by
  set y := involution hK b * b with hy_def
  have hy_mem : ∀ I : Submodule (LevelHeckeAlgebra ℂ K.toSubgroup)
      (LevelHeckeAlgebra ℂ K.toSubgroup), IsCoatom I → y ∈ I :=
    fun I hI => I.smul_mem (involution hK b) (hb I hI)
  have hy_inv : involution hK y = y := by
    rw [hy_def, involution_mul, involution_involution]
  have hy_nil : IsNilpotent y := by
    by_contra hn
    obtain ⟨I, hI, _, hne⟩ :=
      Langlands.Renard.unitalSeparation (LevelHeckeAlgebra ℂ K.toSubgroup) rank_le_aleph0 y hn
    apply hne
    rw [← LinearMap.map_smul, smul_eq_mul, mul_one]
    exact (Submodule.Quotient.mk_eq_zero I).mpr (hy_mem I hI)
  have hy0 := eq_zero_of_isNilpotent_of_involution_eq hK y hy_inv hy_nil
  have hb0 : involution hK b = 0 := by
    apply eq_zero_of_mul_involution_eq_zero hK
    rw [involution_involution]
    exact hy0
  rw [← involution_involution hK b, hb0, involution_zero]

end Langlands.Shimura.LevelHecke.LevelHeckeAlgebra
