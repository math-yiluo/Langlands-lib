import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Field.ZMod
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm
import Langlands.ClassField.Global.LocalUnitPowers
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.KummerExtension
import Mathlib.NumberTheory.NumberField.Completion.Ramification

/-! # Kummer theory for one radical of prime degree -/

namespace Langlands.Global.Arithmetic.KummerRadical

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- If `x ≠ 0` and `x ^ p ∈ K`, then every automorphism `σ` of `L/K` multiplies `x` by a power
of a primitive `p`-th root of unity of `K`. -/
theorem exists_apply_eq_pow_mul {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (σ : L ≃ₐ[K] L) {x : L} (hx : x ^ p ∈ Set.range (algebraMap K L)) (hx0 : x ≠ 0) :
    ∃ j < p, σ x = algebraMap K L ζ ^ j * x := by
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) p :=
    hζ.map_of_injective (algebraMap K L).injective
  obtain ⟨y, hy⟩ := hx
  have hxp : x ^ p ≠ 0 := pow_ne_zero p hx0
  have h1 : (σ x / x) ^ p = 1 := by
    rw [div_pow, ← map_pow, ← hy, AlgEquiv.commutes, hy, div_self hxp]
  obtain ⟨j, hj, hj'⟩ := hζL.eq_pow_of_pow_eq_one h1
  exact ⟨j, hj, by rw [hj', div_mul_cancel₀ _ hx0]⟩

/-- **Kummer theory for one radical.** Let `L/K` be Galois of prime degree `p`, let `K` contain a
primitive `p`-th root of unity, and let `α ∈ L ∖ K` with `α ^ p ∈ K`. Then every `γ ∈ L` with
`γ ^ p ∈ K` is `c · α ^ k` for some `c ∈ K` and `k : ℕ`. -/
theorem exists_eq_algebraMap_mul_pow {p : ℕ} [hp : Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) [FiniteDimensional K L] [IsGalois K L]
    (hcard : Nat.card (L ≃ₐ[K] L) = p) {α γ : L}
    (hα : α ^ p ∈ Set.range (algebraMap K L)) (hαK : α ∉ Set.range (algebraMap K L))
    (hγ : γ ^ p ∈ Set.range (algebraMap K L)) :
    ∃ (k : ℕ) (c : K), γ = algebraMap K L c * α ^ k := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hζL : IsPrimitiveRoot (algebraMap K L ζ) p :=
    hζ.map_of_injective (algebraMap K L).injective
  by_cases hγ0 : γ = 0
  · exact ⟨0, 0, by simp [hγ0]⟩
  have hα0 : α ≠ 0 := fun h => hαK ⟨0, by rw [h, map_zero]⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : L ≃ₐ[K] L, σ α ≠ α := by
    by_contra h
    push Not at h
    exact hαK ((IsGalois.mem_range_algebraMap_iff_fixed α).2 h)
  have hσ1 : σ ≠ 1 := fun h => hσ (by rw [h]; rfl)
  obtain ⟨j, hjp, hj⟩ := exists_apply_eq_pow_mul hζ σ hα hα0
  obtain ⟨i, -, hi⟩ := exists_apply_eq_pow_mul hζ σ hγ hγ0
  have hj0 : (j : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hdvd
    obtain rfl : j = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hjp
    exact hσ (by rw [hj, pow_zero, one_mul])
  set k : ℕ := ((j : ZMod p)⁻¹ * i).val with hk
  have hjk : ((j * k : ℕ) : ZMod p) = i := by
    rw [Nat.cast_mul, hk, ZMod.natCast_zmod_val, ← mul_assoc, mul_inv_cancel₀ hj0, one_mul]
  have key : ∀ a : ℕ, algebraMap K L ζ ^ a = algebraMap K L ζ ^ (a % p) := fun a => by
    conv_lhs => rw [← Nat.mod_add_div a p]
    rw [pow_add, pow_mul, hζL.pow_eq_one, one_pow, mul_one]
  have hpow : algebraMap K L ζ ^ (j * k) = algebraMap K L ζ ^ i := by
    rw [ZMod.natCast_eq_natCast_iff'] at hjk
    rw [key (j * k), hjk, ← key i]
  set δ := γ / α ^ k with hδ
  have hσδ : σ δ = δ := by
    rw [hδ, map_div₀, map_pow, hi, hj, mul_pow, ← pow_mul, hpow]
    exact mul_div_mul_left γ (α ^ k) (pow_ne_zero i (hζL.ne_zero (NeZero.ne p)))
  have hfix : ∀ τ : L ≃ₐ[K] L, τ δ = δ := by
    intro τ
    have hmem : σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) δ := hσδ
    have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (L ≃ₐ[K] L) δ :=
      Subgroup.zpowers_le.2 hmem
    have hτ : τ ∈ Subgroup.zpowers σ := by
      rw [zpowers_eq_top_of_prime_card hcard hσ1]
      exact Subgroup.mem_top τ
    exact hle hτ
  obtain ⟨c, hc⟩ := (IsGalois.mem_range_algebraMap_iff_fixed δ).2 hfix
  refine ⟨k, c, ?_⟩
  rw [hc, hδ, div_mul_cancel₀ _ (pow_ne_zero k hα0)]

/-- Elements of `K` that become `p`-th powers in `L = K(α)`, `α ^ p = a`, lie in `a ^ ℕ · K ^ p`. -/
theorem exists_eq_pow_mul_pow_of_eq_pow {p : ℕ} [hp : Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) [FiniteDimensional K L] [IsGalois K L]
    (hcard : Nat.card (L ≃ₐ[K] L) = p) {α : L} {a : K} (hα : α ^ p = algebraMap K L a)
    (hαK : α ∉ Set.range (algebraMap K L)) {b : K} {γ : L} (hγ : γ ^ p = algebraMap K L b) :
    ∃ (k : ℕ) (c : K), b = a ^ k * c ^ p := by
  obtain ⟨k, c, hc⟩ := exists_eq_algebraMap_mul_pow hζ hcard ⟨a, hα.symm⟩ hαK ⟨b, hγ.symm⟩
  refine ⟨k, c, (algebraMap K L).injective ?_⟩
  rw [← hγ, hc, mul_pow, ← pow_mul, mul_comm k p, pow_mul, hα, map_mul, map_pow, map_pow,
    mul_comm]

section LocalSplitting

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- **Local splitting of a radical extension.** Let `L = K(β)` with `β ^ p = a ∈ K` and `K`
containing a primitive `p`-th root of unity. If `a` is a `p`-th power in `K_v`, then every
completion `L_w` with `w ∣ v` has degree one over `K_v`. -/
theorem finrank_adicCompletion_eq_one {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {β : L} (hβ : Algebra.adjoin K {β} = ⊤) {a : K} (hβa : β ^ p = algebraMap K L a)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    {c : v.adicCompletion K} (hc : c ^ p = algebraMap K (v.adicCompletion K) a) :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) = 1 := by
  rw [← Subalgebra.bot_eq_top_iff_finrank_eq_one]
  apply Langlands.Global.AdelicFunctoriality.subalgebra_eq_top_of_algebraMap_mem v w
  have hK : ∀ k : K, algebraMap L (w.adicCompletion L) (algebraMap K L k) ∈
      (⊥ : Subalgebra (v.adicCompletion K) (w.adicCompletion L)) := fun k => by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K (v.adicCompletion K)]
    exact Subalgebra.algebraMap_mem _ _
  have hb : algebraMap L (w.adicCompletion L) β ∈
      (⊥ : Subalgebra (v.adicCompletion K) (w.adicCompletion L)) := by
    set b := algebraMap L (w.adicCompletion L) β
    set c' := algebraMap (v.adicCompletion K) (w.adicCompletion L) c
    have hbc : b ^ p = c' ^ p := by
      rw [← map_pow, hβa, ← map_pow, hc, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
    by_cases hc0 : c' = 0
    · rw [hc0, zero_pow (NeZero.ne p)] at hbc
      rw [pow_eq_zero_iff (NeZero.ne p) |>.1 hbc]
      exact Subalgebra.zero_mem _
    have hζw : IsPrimitiveRoot (algebraMap K (w.adicCompletion L) ζ) p :=
      hζ.map_of_injective (algebraMap K (w.adicCompletion L)).injective
    have h1 : (b / c') ^ p = 1 := by rw [div_pow, hbc, div_self (pow_ne_zero p hc0)]
    obtain ⟨i, -, hi⟩ := hζw.eq_pow_of_pow_eq_one h1
    have : b = algebraMap K (w.adicCompletion L) ζ ^ i * c' := by
      rw [hi, div_mul_cancel₀ _ hc0]
    rw [this, IsScalarTower.algebraMap_apply K (v.adicCompletion K)]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ _) _)
      (Subalgebra.algebraMap_mem _ _)
  intro y
  have hy : y ∈ Algebra.adjoin K {β} := hβ ▸ Algebra.mem_top
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    rw [hx]; exact hb
  | algebraMap k => exact hK k
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact Subalgebra.mul_mem _ hx hy

/-- Conversely, if some completion `L_w` with `w ∣ v` has degree one over `K_v`, then
`a = β ^ p` is a `p`-th power in `K_v`. -/
theorem exists_pow_eq_of_finrank_eq_one {p : ℕ} {β : L} {a : K} (hβa : β ^ p = algebraMap K L a)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (h : Module.finrank (v.adicCompletion K) (w.adicCompletion L) = 1) :
    ∃ c : v.adicCompletion K, c ^ p = algebraMap K (v.adicCompletion K) a := by
  have hbot := Subalgebra.bot_eq_top_iff_finrank_eq_one.2 h
  have hmem : algebraMap L (w.adicCompletion L) β ∈
      (⊥ : Subalgebra (v.adicCompletion K) (w.adicCompletion L)) := hbot ▸ Algebra.mem_top
  obtain ⟨c, hc⟩ := Algebra.mem_bot.1 hmem
  refine ⟨c, (algebraMap (v.adicCompletion K) (w.adicCompletion L)).injective ?_⟩
  rw [map_pow, hc, ← map_pow, hβa, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

end LocalSplitting

section Unramified

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- **Hensel's lemma for `p`-th roots.** If `p` is a unit of `O_v` and the residue of a unit
`a ∈ O_v` is a `p`-th power in the residue field, then `a` is a `p`-th power in `O_v`. -/
theorem exists_pow_eq_of_residue_pow_eq (v : HeightOneSpectrum (𝓞 K)) {p : ℕ}
    (hp : IsUnit (p : v.adicCompletionIntegers K)) {a : v.adicCompletionIntegers K}
    (ha : IsUnit a) {b : v.adicCompletionIntegers K}
    (hb : residue _ b ^ p = residue _ a) :
    ∃ c : v.adicCompletionIntegers K, c ^ p = a := by
  have := Langlands.ClassField.Global.isAdicComplete_adicCompletionIntegers v
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero] at hp
    exact not_isUnit_zero hp
  have hb0 : IsUnit b := by
    rw [← residue_ne_zero_iff_isUnit]
    intro h
    rw [h, zero_pow hp0, eq_comm, residue_eq_zero_iff] at hb
    exact (mem_maximalIdeal _).1 hb ha
  obtain ⟨c, hc, -⟩ := HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers K))
    (X ^ p - C a) (monic_X_pow_sub_C a hp0) b
    (by
      rw [← residue_eq_zero_iff, eval_sub, eval_pow, eval_X, eval_C, map_sub, map_pow, hb,
        sub_self])
    (by
      rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul, eval_C,
        eval_pow, eval_X]
      exact (hp.mul (hb0.pow _)).map _)
  refine ⟨c, ?_⟩
  rw [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hc
  exact hc

/-- **Radicals of units are unramified away from `p`.** Let `L/K` be Galois of prime degree `p`,
let `K` contain a primitive `p`-th root of unity, and let `L = K(β)` with `β ^ p = a ∈ K`. At a
finite place `v` where `p` is a unit and `a` has valuation one, every place `w ∣ v` has
ramification index one. -/
theorem ramificationIdx_eq_one_of_valued_eq_one {p : ℕ} [hp : Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) [IsGalois K L] (hdeg : Module.finrank K L = p)
    {β : L} (hβ : Algebra.adjoin K {β} = ⊤) {a : K} (hβa : β ^ p = algebraMap K L a)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (hpv : IsUnit (p : v.adicCompletionIntegers K))
    (hav : Valued.v (algebraMap K (v.adicCompletion K) a) = 1) :
    w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hdvd := Langlands.Global.AdelicFunctoriality.localDegree_dvd v w
  rw [hdeg, Langlands.Global.AdelicFunctoriality.localDegree_eq] at hdvd
  have hef0 : w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) ≠ 0 := by
    rintro h
    rw [h, zero_dvd_iff] at hdvd
    exact hp.out.ne_zero hdvd
  by_cases hc : ∃ c : v.adicCompletion K, c ^ p = algebraMap K (v.adicCompletion K) a
  · obtain ⟨c, hc⟩ := hc
    have h1 := finrank_adicCompletion_eq_one hζ hβ hβa v w hc
    rw [Langlands.Global.AdelicFunctoriality.localDegree_eq] at h1
    exact Nat.eq_one_of_mul_eq_one_right h1
  -- Otherwise the residue degree is at least `p`.
  let R := v.adicCompletionIntegers K
  let S := w.adicCompletionIntegers L
  let a' : R := ⟨algebraMap K (v.adicCompletion K) a, hav.le⟩
  have ha' : IsUnit a' := adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hav
  have hnot : ∀ b : ResidueField R, b ^ p ≠ residue R a' := by
    intro b hb
    obtain ⟨b, rfl⟩ := residue_surjective b
    obtain ⟨c, hc'⟩ := exists_pow_eq_of_residue_pow_eq v hpv ha' (b := b) hb
    exact hc ⟨c, by rw [← SubmonoidClass.coe_pow, hc']⟩
  set β' := algebraMap L (w.adicCompletion L) β with hβ'
  have hβ'p : β' ^ p = Langlands.Global.AdelicFunctoriality.FiniteExtension.completionMap v w
      (a' : v.adicCompletion K) := by
    rw [hβ', ← map_pow, hβa,
      ← Langlands.Global.AdelicFunctoriality.FiniteExtension.completionMap_coe v w a]
  have hβv : Valued.v β' = 1 := by
    have h := congrArg Valued.v hβ'p
    rw [map_pow, Langlands.Global.AdelicFunctoriality.FiniteExtension.valuation_completionMap]
      at h
    change _ = Valued.v (algebraMap K (v.adicCompletion K) a) ^ _ at h
    rw [hav, one_pow] at h
    exact (pow_eq_one_iff_of_nonneg zero_le (NeZero.ne p)).1 h
  let b' : S := ⟨β', hβv.le⟩
  have hb'p : residue S b' ^ p = algebraMap (ResidueField R) (ResidueField S) (residue R a') := by
    rw [IsLocalRing.ResidueField.algebraMap_residue, ← map_pow]
    congr 1
    exact Subtype.ext hβ'p
  have hirr := X_pow_sub_C_irreducible_of_prime hp.out hnot
  have hmin := minpoly.eq_of_irreducible_of_monic hirr
    (x := residue S b') (by rw [map_sub, map_pow, aeval_X, aeval_C, hb'p, sub_self])
    (monic_X_pow_sub_C _ hp.out.ne_zero)
  have hi : (maximalIdeal S).inertiaDeg R =
      Module.finrank (ResidueField R) (ResidueField S) :=
    Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal R) (maximalIdeal S)
  rw [Langlands.Global.AdelicFunctoriality.FiniteExtension.completionIntegers_inertiaDeg] at hi
  have hf0 : w.asIdeal.inertiaDeg (𝓞 K) ≠ 0 := right_ne_zero_of_mul hef0
  have : FiniteDimensional (ResidueField R) (ResidueField S) :=
    Module.finite_of_finrank_pos (by rw [← hi]; exact Nat.pos_of_ne_zero hf0)
  have hpf : p ≤ w.asIdeal.inertiaDeg (𝓞 K) := by
    have h := minpoly.natDegree_le (A := ResidueField R) (residue S b')
    rwa [← hmin, natDegree_X_pow_sub_C, ← hi] at h
  have he0 : w.asIdeal.ramificationIdx (𝓞 K) ≠ 0 := left_ne_zero_of_mul hef0
  have hle := Nat.le_of_dvd hp.out.pos hdvd
  have : w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) ≤
      1 * w.asIdeal.inertiaDeg (𝓞 K) := by omega
  have := Nat.le_of_mul_le_mul_right this (Nat.pos_of_ne_zero hf0)
  omega

/-- **Units are norms from an unramified radical.** Under the hypotheses of
`ramificationIdx_eq_one_of_valued_eq_one`, every unit of `K_v` of valuation one is the local norm
of a unit of `L_w` of valuation one. -/
theorem exists_localNorm_eq_of_valued_eq_one {p : ℕ} [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) [IsGalois K L] (hdeg : Module.finrank K L = p)
    {β : L} (hβ : Algebra.adjoin K {β} = ⊤) {a : K} (hβa : β ^ p = algebraMap K L a)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (hpv : IsUnit (p : v.adicCompletionIntegers K))
    (hav : Valued.v (algebraMap K (v.adicCompletion K) a) = 1)
    (u : (v.adicCompletion K)ˣ) (hu : Valued.v (u : v.adicCompletion K) = 1) :
    ∃ c : (w.adicCompletion L)ˣ, Valued.v (c : w.adicCompletion L) = 1 ∧
      Langlands.Global.AdelicFunctoriality.FiniteExtension.localNorm v w c = u :=
  Langlands.Global.AdelicFunctoriality.FiniteExtension.exists_localNorm_eq_of_ramificationIdx_eq_one
    v w (ramificationIdx_eq_one_of_valued_eq_one hζ hdeg hβ hβa v w hpv hav) u hu

end Unramified

section Norms

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.Global.AdelicFunctoriality.FiniteExtension
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- At a finite place where the completion has degree one, every unit of `K_v` is the local
norm of a unit of `L_w`. -/
theorem exists_localNorm_eq_of_finrank_eq_one (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (h : Module.finrank (v.adicCompletion K) (w.adicCompletion L) = 1)
    (u : (v.adicCompletion K)ˣ) :
    ∃ c : (w.adicCompletion L)ˣ, localNorm v w (c : w.adicCompletion L) = u := by
  refine ⟨Units.map (completionMap v w).toMonoidHom u, ?_⟩
  change localNorm v w (completionMap v w u) = u
  rw [localNorm_algebraMap, h, pow_one]

/-- In a Galois extension of degree `p`, the `p`-th power of every unit of `K_v` is the local
norm of a unit of `L_w`. -/
theorem exists_localNorm_eq_pow [IsGalois K L] {p : ℕ} (hdeg : Module.finrank K L = p)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (u : (v.adicCompletion K)ˣ) :
    ∃ c : (w.adicCompletion L)ˣ, localNorm v w (c : w.adicCompletion L) =
      ((u ^ p : (v.adicCompletion K)ˣ) : v.adicCompletion K) := by
  obtain ⟨m, hm⟩ := Langlands.Global.AdelicFunctoriality.localDegree_dvd v w
  refine ⟨Units.map (completionMap v w).toMonoidHom (u ^ m), ?_⟩
  change localNorm v w (completionMap v w ((u ^ m : (v.adicCompletion K)ˣ) :
    v.adicCompletion K)) = _
  rw [localNorm_algebraMap, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← pow_mul,
    mul_comm m, ← hm, hdeg]

end Norms

section Archimedean

open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding
open scoped NumberField.LiesOver ComplexConjugate

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- If `K` has a real place and contains a primitive `p`-th root of unity with `p ≠ 0`, then
`p ∣ 2`. -/
theorem dvd_two_of_isReal {p : ℕ} (hp : p ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (v : InfinitePlace K) (hv : v.IsReal) : p ∣ 2 := by
  have h := hζ.map_of_injective (embedding_of_isReal hv).injective
  apply h.dvd_of_pow_eq_one
  set r := embedding_of_isReal hv ζ
  have hr : |r| ^ p = 1 := by rw [pow_abs, h.pow_eq_one, abs_one]
  have hr1 : |r| = 1 := (pow_eq_one_iff_of_nonneg (abs_nonneg r) hp).1 hr
  rw [← sq_abs, hr1, one_pow]

/-- If `K` has a real place and contains a primitive `p`-th root of unity for a prime `p`, then
`p = 2`. -/
theorem eq_two_of_isReal {p : ℕ} [hp : Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (v : InfinitePlace K) (hv : v.IsReal) : p = 2 :=
  (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1
    (dvd_two_of_isReal hp.out.ne_zero hζ v hv)

/-- **Real places of a quadratic radical extension.** Let `L = K(β)` with `β ^ 2 = a ∈ K`. If
`v` is a real place of `K` at which `a` is a square in `K_v`, then every place `w ∣ v` is real. -/
theorem isReal_of_sq_eq (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]
    (hv : v.IsReal) {β : L} (hβ : Algebra.adjoin K {β} = ⊤) {a : K}
    (hβa : β ^ 2 = algebraMap K L a) {c : v.Completion}
    (hc : c ^ 2 = algebraMap K v.Completion a) : w.IsReal := by
  have hvr : ∀ k : K, conj (v.embedding k) = v.embedding k := fun k =>
    RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp (isReal_iff.mp hv)) k
  have hcomp : ∀ k : K, w.embedding (algebraMap K L k) = v.embedding k := by
    intro k
    rcases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v with h | h
    · exact RingHom.congr_fun h k
    · have h' := congrArg conj (RingHom.congr_fun h k)
      rw [RingHom.comp_apply, conjugate_coe_eq, Complex.conj_conj, hvr k] at h'
      exact h'
  set s := InfinitePlace.Completion.extensionEmbeddingOfIsReal hv c
  have hs : ((s : ℂ)) ^ 2 = v.embedding a := by
    have h1 := congrArg (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv) hc
    rw [map_pow] at h1
    rw [← Complex.ofReal_pow, h1, ← embedding_of_isReal_apply hv a]
    congr 1
    rw [InfinitePlace.Completion.algebraMap_apply]
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv _
  have hβr : conj (w.embedding β) = w.embedding β := by
    have h2 : (w.embedding β) ^ 2 = (s : ℂ) ^ 2 := by
      rw [← map_pow, hβa, hcomp, hs]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h3 | h3
    · rw [h3, Complex.conj_ofReal]
    · rw [h3, map_neg, Complex.conj_ofReal]
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  ext y
  rw [conjugate_coe_eq]
  have hy : y ∈ Algebra.adjoin K {β} := hβ ▸ Algebra.mem_top
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    rw [hx]; exact hβr
  | algebraMap k => rw [hcomp, hvr]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

/-- **Archimedean splitting of a radical extension.** Let `K` contain a primitive `p`-th root of
unity for a prime `p`, and let `L = K(β)` with `β ^ p = a ∈ K`. If `a` is a `p`-th power in
`K_v` at an infinite place `v`, then every place `w ∣ v` is unramified over `K`. -/
theorem isUnramified_of_pow_eq {p : ℕ} [Fact p.Prime] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v] {β : L}
    (hβ : Algebra.adjoin K {β} = ⊤) {a : K} (hβa : β ^ p = algebraMap K L a)
    {c : v.Completion} (hc : c ^ p = algebraMap K v.Completion a) : w.IsUnramified K := by
  rcases v.isReal_or_isComplex with hv | hv
  · obtain rfl := eq_two_of_isReal hζ v hv
    exact (isReal_of_sq_eq v w hv hβ hβa hc).isUnramified K
  · exact isUnramified_iff.mpr (Or.inr (by rw [LiesOver.comap_eq w v]; exact hv))

open Langlands.Global.AdelicFunctoriality.InfiniteExtension
open scoped Langlands.Global.AdelicFunctoriality.InfiniteExtension

/-- At an unramified infinite place every unit of `K_v` is a local norm. -/
theorem exists_infinite_localNorm_eq_of_isUnramified (v : InfinitePlace K) (w : InfinitePlace L)
    [w.LiesOver v] (h : w.IsUnramified K) (u : (v.Completion)ˣ) :
    ∃ c : (w.Completion)ˣ, localNorm v w (c : w.Completion) = u := by
  refine ⟨Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom u, ?_⟩
  change localNorm v w (NumberField.LiesOver.completionMap (u : v.Completion)) = u
  rw [localNorm_algebraMap, h.finrank_eq_one v, pow_one]

/-- If `K` contains a primitive `p`-th root of unity for a prime `p`, then at every infinite
place the `p`-th power of every unit of `K_v` is a local norm. -/
theorem exists_infinite_localNorm_eq_pow {p : ℕ} [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (v : InfinitePlace K) (w : InfinitePlace L) [w.LiesOver v]
    (u : (v.Completion)ˣ) :
    ∃ c : (w.Completion)ˣ, localNorm v w (c : w.Completion) =
      ((u ^ p : (v.Completion)ˣ) : v.Completion) := by
  rcases w.isUnramified_or_isRamified K with h | h
  · exact exists_infinite_localNorm_eq_of_isUnramified v w h (u ^ p)
  · obtain rfl := eq_two_of_isReal hζ v (IsRamified.liesOver_isReal_under w v h)
    refine ⟨Units.map (NumberField.LiesOver.completionMap (v := v) (w := w)).toMonoidHom u, ?_⟩
    change localNorm v w (NumberField.LiesOver.completionMap (u : v.Completion)) = _
    rw [localNorm_algebraMap, h.finrank_eq_two v, Units.val_pow_eq_pow_val]

end Archimedean

section RadicalExtension

open Polynomial

variable (K : Type*) [Field K]

/-- The radical extension `K(x^{1/p}) = K[X] / (X ^ p - x)`; it is a field when `X ^ p - x` is
irreducible. -/
abbrev radicalExtension (p : ℕ) (x : K) : Type _ := AdjoinRoot (X ^ p - C x)

/-- The distinguished `p`-th root of `x` in `radicalExtension K p x`. -/
noncomputable def radicalRoot (p : ℕ) (x : K) : radicalExtension K p x :=
  AdjoinRoot.root (X ^ p - C x)

variable {K}

theorem radicalRoot_pow (p : ℕ) (x : K) :
    radicalRoot K p x ^ p = algebraMap K (radicalExtension K p x) x := by
  have h := AdjoinRoot.eval₂_root (X ^ p - C x)
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
  exact h

theorem adjoin_radicalRoot (p : ℕ) (x : K) :
    Algebra.adjoin K {radicalRoot K p x} = ⊤ :=
  AdjoinRoot.adjoinRoot_eq_top

/-- For a prime `p`, `X ^ p - x` is irreducible as soon as `x` is not a `p`-th power. -/
theorem irreducible_of_forall_pow_ne {p : ℕ} (hp : p.Prime) {x : K} (hx : ∀ b : K, b ^ p ≠ x) :
    Irreducible (X ^ p - C x) :=
  X_pow_sub_C_irreducible_of_prime hp hx

variable {p : ℕ} {x : K} [hirr : Fact (Irreducible (X ^ p - C x))]

theorem finrank_radicalExtension : Module.finrank K (radicalExtension K p x) = p := by
  have hp : p ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C hirr.out
  rw [(AdjoinRoot.powerBasis hirr.out.ne_zero).finrank, AdjoinRoot.powerBasis_dim,
    natDegree_X_pow_sub_C]

instance : Module.Finite K (radicalExtension K p x) :=
  (AdjoinRoot.powerBasis hirr.out.ne_zero).finite

theorem isGalois_radicalExtension {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    IsGalois K (radicalExtension K p x) := by
  have hp : p ≠ 0 := ne_zero_of_irreducible_X_pow_sub_C hirr.out
  have hne : (primitiveRoots p K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (Nat.pos_of_ne_zero hp)).2 hζ⟩
  have := isSplittingField_AdjoinRoot_X_pow_sub_C hne hirr.out
  exact isGalois_of_isSplittingField_X_pow_sub_C hne hirr.out _

theorem numberField_radicalExtension [NumberField K] : NumberField (radicalExtension K p x) :=
  NumberField.of_module_finite K _

end RadicalExtension

end Langlands.Global.Arithmetic.KummerRadical
