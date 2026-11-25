import Langlands.GaloisCohomology.Local.EulerCharacteristic.Additive
import Langlands.GaloisCohomology.Local.Arithmetic.Units
import Langlands.GaloisCohomology.Local.Arithmetic.NormalLattice
import Langlands.GaloisCohomology.Local.Arithmetic.Ramification
import Langlands.GaloisCohomology.Local.Arithmetic.Integers
import Langlands.ClassFieldTheory.Local.LocalFieldOrder

/-!
# Units of a finite Galois extension of local fields as a Galois module

For a finite Galois extension `F/E` of nonarchimedean local fields and a prime `l` invertible in
`F`, the value of an additive function (in the sense of `Additive.lean`) on the units `Fˣ` is
computed: `g(Fˣ) = g(ℤ) + n · g(𝔽_l[G])` where `|𝒪[E]/l| = lⁿ`. The proof compares `𝒪[F]ˣ` with
a deep unit group `U^k`, `U^k` with `𝓂^k` (logarithm-free: `U^k/(U^k)^l ≅ 𝓂^k/l𝓂^k` for large
`k`), and `𝓂^k` with a lattice spanned by a normal basis, which is free over `𝒪[E][G]`.
-/

noncomputable section

universe u

namespace Langlands.GaloisCohomology.Local

-- from UnitsPower.lean
section UnitsPower
open ValuativeRel IsLocalRing Polynomial

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem one_add_pow_prime_eq {p : ℕ} (hp : p.Prime) {z : 𝒪[K]} (hz : z ∈ 𝓂[K]) :
    ∃ y ∈ 𝓂[K], (1 + z) ^ p = 1 + z ^ p + p * z * (1 + y) := by
  rw [add_comm (1 : 𝒪[K]) z, add_pow_prime_eq hp z 1]
  set r := ∑ k ∈ Finset.Ioo 0 p, z ^ (k - 1) * 1 ^ (p - k - 1) * ((p.choose k / p : ℕ) : 𝒪[K])
  refine ⟨r - 1, ?_, by ring⟩
  rw [← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
  have hz' : residue 𝒪[K] z = 0 := (residue_eq_zero_iff _).mpr hz
  simp only [r, map_sum, map_mul, map_pow, hz', one_pow, map_natCast, mul_one]
  rw [Finset.sum_eq_single 1]
  · simp [Nat.div_self hp.pos]
  · intro k hk hk1
    have : k - 1 ≠ 0 := by simp at hk; omega
    simp [zero_pow this]
  · intro h
    exact absurd (by simp; exact hp.one_lt) h

variable {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {p : ℕ} (hp : p.Prime) {e : ℕ} {ε : 𝒪[K]ˣ}
  (hpe : (p : 𝒪[K]) = ϖ ^ e * ε)
include hϖ hp hpe

theorem one_add_pow_sub_one_eq {j : ℕ} (hj : e + 1 ≤ j) (x : 𝒪[K]) :
    ∃ w : 𝒪[K], (1 + ϖ ^ j * x) ^ p - 1 = ϖ ^ (j + e) * (ε * x + ϖ * w) := by
  have hj1 : 1 ≤ j := by omega
  obtain ⟨y, hy, h⟩ := one_add_pow_prime_eq hp (z := ϖ ^ j * x)
    (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (uniformizer_mem_maximalIdeal hϖ) j hj1))
  obtain ⟨t, rfl⟩ := (mem_maximalIdeal_iff_dvd hϖ).mp hy
  have h2 : 2 * j ≤ p * j := Nat.mul_le_mul_right j hp.two_le
  obtain ⟨m, hm⟩ : ∃ m, p * j = j + e + 1 + m := ⟨p * j - (j + e + 1), by omega⟩
  refine ⟨ϖ ^ m * x ^ p + ε * x * t, ?_⟩
  have hpow : (ϖ ^ j * x) ^ p = ϖ ^ (j + e + 1 + m) * x ^ p := by
    rw [mul_pow, ← pow_mul, mul_comm j p, hm]
  rw [h, hpow, hpe]
  ring

theorem pow_mem_unitFiltration {j : ℕ} (hj : e + 1 ≤ j) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K j) : u ^ p ∈ unitFiltration K (j + e) := by
  obtain ⟨a, ha⟩ := exists_sub_one_eq_mul hϖ ⟨u, hu⟩
  obtain ⟨w, hw⟩ := one_add_pow_sub_one_eq hϖ hp hpe hj a
  rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ, Units.val_pow_eq_pow_val,
    show (u : 𝒪[K]) = 1 + ϖ ^ j * a by simp only at ha; rw [← ha]; ring, hw]
  exact dvd_mul_right _ _

theorem pow_mem_unitFiltration_succ_iff {j : ℕ} (hj : e + 1 ≤ j) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K j) :
    u ^ p ∈ unitFiltration K (j + e + 1) ↔ u ∈ unitFiltration K (j + 1) := by
  obtain ⟨a, ha⟩ := exists_sub_one_eq_mul hϖ ⟨u, hu⟩
  obtain ⟨w, hw⟩ := one_add_pow_sub_one_eq hϖ hp hpe hj a
  have hu' : (u : 𝒪[K]) = 1 + ϖ ^ j * a := by simp only at ha; rw [← ha]; ring
  rw [mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ, Units.val_pow_eq_pow_val, hu', hw,
    mem_unitFiltration, mem_maximalIdeal_pow_iff hϖ, hu', add_sub_cancel_left, pow_succ,
    pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero),
    mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero), dvd_add_left (dvd_mul_right ϖ w),
    Units.dvd_mul_left]

theorem eq_one_of_mem_unitFiltration_of_pow_eq_one {k : ℕ} (hk : e + 1 ≤ k) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K k) (h : u ^ p = 1) : u = 1 := by
  have hall : ∀ n, u ∈ unitFiltration K (k + n) := by
    intro n
    induction n with
    | zero => simpa using hu
    | succ n ih =>
      have := (pow_mem_unitFiltration_succ_iff hϖ hp hpe (by omega) ih).mp
        (by rw [h]; exact one_mem _)
      simpa [add_assoc] using this
  have h0 : (u : 𝒪[K]) - 1 = 0 := by
    refine eq_zero_of_forall_pow_dvd hϖ fun N => ?_
    have := unitFiltration_antitone K (Nat.le_add_left N k) (hall N)
    exact (mem_maximalIdeal_pow_iff hϖ).mp (mem_unitFiltration.mp this)
  ext
  simpa [sub_eq_zero] using h0

end UnitsPower

-- from UnitsLattice.lean
section UnitsLattice
open ValuativeRel IsLocalRing

section Galois

variable (E F : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F]

attribute [local instance] integerAction integerUnitsAction

variable {E F}

theorem coe_integer_smul (σ : F ≃ₐ[E] F) (x : 𝒪[F]) : ((σ • x : 𝒪[F]) : F) = σ (x : F) :=
  rfl

theorem coe_integerUnits_smul (σ : F ≃ₐ[E] F) (u : 𝒪[F]ˣ) :
    ((σ • u : 𝒪[F]ˣ) : 𝒪[F]) = σ • (u : 𝒪[F]) :=
  rfl

theorem smul_mem_maximalIdeal (σ : F ≃ₐ[E] F) {x : 𝒪[F]} (hx : x ∈ 𝓂[F]) : σ • x ∈ 𝓂[F] := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro h
  apply hx
  have := h.map (MulSemiringAction.toRingHom (F ≃ₐ[E] F) 𝒪[F] σ⁻¹)
  simpa [MulSemiringAction.toRingHom_apply, smul_smul] using this

theorem smul_mem_maximalIdeal_pow (σ : F ≃ₐ[E] F) {k : ℕ} {x : 𝒪[F]} (hx : x ∈ 𝓂[F] ^ k) :
    σ • x ∈ 𝓂[F] ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨a, rfl⟩ := (mem_maximalIdeal_pow_iff hϖ).mp hx
  rw [smul_mul', smul_pow']
  exact Ideal.mul_mem_right _ _
    (Ideal.pow_mem_pow (smul_mem_maximalIdeal σ (uniformizer_mem_maximalIdeal hϖ)) k)

theorem smul_mem_unitFiltration (σ : F ≃ₐ[E] F) {k : ℕ} {u : 𝒪[F]ˣ}
    (hu : u ∈ unitFiltration F k) : σ • u ∈ unitFiltration F k := by
  rw [mem_unitFiltration, coe_integerUnits_smul, ← smul_one σ, ← smul_sub]
  · exact smul_mem_maximalIdeal_pow σ hu

end Galois

section ModN

variable {G : Type*} [AddCommGroup G]

theorem mem_range_lsmul_iff {n : ℕ} {x : G} :
    x ∈ LinearMap.range (LinearMap.lsmul ℤ G n) ↔ ∃ y : G, n • y = x := by
  simp [LinearMap.mem_range, natCast_zsmul]

end ModN

section Filtration

variable (E F : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F]

attribute [local instance] integerAction integerUnitsAction

noncomputable abbrev unitFiltrationAction (k : ℕ) :
    MulDistribMulAction (F ≃ₐ[E] F) (unitFiltration F k) where
  smul σ u := ⟨σ • (u : 𝒪[F]ˣ), smul_mem_unitFiltration σ u.2⟩
  one_smul u := Subtype.ext (one_smul _ (u : 𝒪[F]ˣ))
  mul_smul σ τ u := Subtype.ext (mul_smul σ τ (u : 𝒪[F]ˣ))
  smul_mul σ u v := Subtype.ext (smul_mul' σ (u : 𝒪[F]ˣ) v)
  smul_one σ := Subtype.ext (smul_one σ)

variable {F} in

noncomputable def maxPow (F : Type*) [Field F] [ValuativeRel F] (k : ℕ) : AddSubgroup 𝒪[F] :=
  (𝓂[F] ^ k).toAddSubgroup

noncomputable abbrev maxPowAction (k : ℕ) : DistribMulAction (F ≃ₐ[E] F) (maxPow F k) :=
  subgroupDistribMulAction (maxPow F k) fun σ _ hx ↦ smul_mem_maximalIdeal_pow σ hx

attribute [local instance] unitFiltrationAction maxPowAction

variable {E F}

theorem coe_maxPow_smul (σ : F ≃ₐ[E] F) {k : ℕ} (x : maxPow F k) :
    ((σ • x : maxPow F k) : 𝒪[F]) = σ • (x : 𝒪[F]) :=
  rfl

variable {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {p : ℕ} {e : ℕ} {ε : 𝒪[F]ˣ}
  (hpe : (p : 𝒪[F]) = ϖ ^ e * ε)
include hϖ hpe

theorem mem_maximalIdeal_pow_add_iff {k : ℕ} {x : 𝒪[F]} :
    x ∈ 𝓂[F] ^ (k + e) ↔ ∃ y ∈ 𝓂[F] ^ k, x = p * y := by
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := (mem_maximalIdeal_pow_iff hϖ).mp h
    refine ⟨ϖ ^ k * a * ((ε⁻¹ : 𝒪[F]ˣ) : 𝒪[F]), ?_, ?_⟩
    · rw [mem_maximalIdeal_pow_iff hϖ, mul_assoc]
      exact dvd_mul_right _ _
    · rw [hpe]
      have := ε.mul_inv
      linear_combination (-(ϖ ^ (k + e)) * a) * this
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨b, rfl⟩ := (mem_maximalIdeal_pow_iff hϖ).mp hy
    rw [mem_maximalIdeal_pow_iff hϖ, hpe]
    exact ⟨ε * b, by ring⟩

omit hϖ hpe [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem sub_one_mem_maxPow {k : ℕ} (u : unitFiltration F k) :
    ((u : 𝒪[F]ˣ) : 𝒪[F]) - 1 ∈ maxPow F k :=
  u.2

noncomputable def unitToModN {k : ℕ} (hk : e ≤ k) :
    Additive (unitFiltration F k) →+ ModN (maxPow F k) p where
  toFun u := Submodule.Quotient.mk ⟨((u.toMul : 𝒪[F]ˣ) : 𝒪[F]) - 1, sub_one_mem_maxPow u.toMul⟩
  map_zero' := by
    rw [Submodule.Quotient.mk_eq_zero]
    have h : (⟨_, sub_one_mem_maxPow (Additive.toMul (0 : Additive (unitFiltration F k)))⟩ :
        maxPow F k) = 0 := by
      ext; simp
    exact h ▸ Submodule.zero_mem _
  map_add' u v := by
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq, mem_range_lsmul_iff]
    obtain ⟨a, ha⟩ := exists_sub_one_eq_mul hϖ u.toMul
    obtain ⟨b, hb⟩ := exists_sub_one_eq_mul hϖ v.toMul
    obtain ⟨m, rfl⟩ : ∃ m, k = e + m := ⟨k - e, by omega⟩
    have hy : ϖ ^ (e + m) * (ϖ ^ m * a * b * ((ε⁻¹ : 𝒪[F]ˣ) : 𝒪[F])) ∈ 𝓂[F] ^ (e + m) := by
      rw [mem_maximalIdeal_pow_iff hϖ]
      exact dvd_mul_right _ _
    refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
    simp only [AddSubgroup.coe_nsmul, AddSubgroup.coe_sub, AddSubgroup.coe_add, toMul_add,
      Subgroup.coe_mul, Units.val_mul, nsmul_eq_mul]
    have h1 : ((u.toMul : 𝒪[F]ˣ) : 𝒪[F]) = 1 + ϖ ^ (e + m) * a := by
      rw [← ha]; ring
    have h2 : ((v.toMul : 𝒪[F]ˣ) : 𝒪[F]) = 1 + ϖ ^ (e + m) * b := by
      rw [← hb]; ring
    rw [h1, h2, hpe]
    have := ε.mul_inv
    linear_combination (ϖ ^ (e + m) * (ϖ ^ e * (ϖ ^ m * a * b))) * this

omit hϖ hpe in
variable (ϖ) in
theorem unitToModN_apply (hϖ : Irreducible ϖ) (hpe : (p : 𝒪[F]) = ϖ ^ e * ε) {k : ℕ} (hk : e ≤ k)
    (u : Additive (unitFiltration F k)) :
    unitToModN hϖ hpe hk u =
      Submodule.Quotient.mk ⟨((u.toMul : 𝒪[F]ˣ) : 𝒪[F]) - 1, sub_one_mem_maxPow u.toMul⟩ :=
  rfl

theorem unitToModN_surjective {k : ℕ} (hk : e + 1 ≤ k) :
    Function.Surjective (unitToModN hϖ hpe (Nat.le_of_succ_le hk)) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hx : (x : 𝒪[F]) ∈ 𝓂[F] := Ideal.pow_le_self (by omega) x.2
  have hu := isUnit_unit_add (η := 1) hx
  have hmem : hu.unit ∈ unitFiltration F k := by
    rw [mem_unitFiltration, IsUnit.unit_spec, Units.val_one, add_sub_cancel_left]
    exact x.2
  refine ⟨Additive.ofMul ⟨hu.unit, hmem⟩, ?_⟩
  rw [unitToModN_apply]
  congr 1
  ext
  simp

theorem unitToModN_eq_zero_iff (hp : p.Prime) {k : ℕ} (hk : e + 1 ≤ k)
    (u : Additive (unitFiltration F k)) :
    unitToModN hϖ hpe (Nat.le_of_succ_le hk) u = 0 ↔
      u ∈ LinearMap.range (LinearMap.lsmul ℤ (Additive (unitFiltration F k)) p) := by
  rw [unitToModN_apply, Submodule.Quotient.mk_eq_zero, mem_range_lsmul_iff, mem_range_lsmul_iff]
  constructor
  · rintro ⟨y, hy⟩
    have hy' : ((u.toMul : 𝒪[F]ˣ) : 𝒪[F]) - 1 = p * (y : 𝒪[F]) := by
      have := congrArg Subtype.val hy
      simpa [nsmul_eq_mul] using this.symm
    have h1 : (u.toMul : 𝒪[F]ˣ) ∈ unitFiltration F (k + e) :=
      (mem_maximalIdeal_pow_add_iff hϖ hpe).mpr ⟨y, y.2, hy'⟩
    obtain ⟨v, hv, hvp⟩ := exists_pow_eq_of_mem_unitFiltration hϖ hp hpe hk h1
    refine ⟨Additive.ofMul ⟨v, hv⟩, ?_⟩
    apply Additive.toMul.injective
    ext
    simp [hvp]
  · rintro ⟨v, rfl⟩
    have h1 : ((v.toMul : 𝒪[F]ˣ)) ^ p ∈ unitFiltration F (k + e) :=
      pow_mem_unitFiltration hϖ hp hpe hk v.toMul.2
    obtain ⟨y, hy, hyp⟩ := (mem_maximalIdeal_pow_add_iff hϖ hpe).mp h1
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    simp only [AddSubgroup.coe_nsmul, nsmul_eq_mul, toMul_nsmul, SubmonoidClass.coe_pow,
      Units.val_pow_eq_pow_val] at hyp ⊢
    exact hyp.symm

omit hϖ hpe in
variable (ϖ) in

theorem unitToModN_smul (hϖ : Irreducible ϖ) (hpe : (p : 𝒪[F]) = ϖ ^ e * ε) {k : ℕ}
    (hk : e ≤ k) (σ : F ≃ₐ[E] F) (u : Additive (unitFiltration F k)) :
    unitToModN hϖ hpe hk (σ • u) =
      modNRep (F ≃ₐ[E] F) (maxPow F k) p σ (unitToModN hϖ hpe hk u) := by
  rw [unitToModN_apply, unitToModN_apply, modNRep_mk]
  congr 1
  ext
  rw [coe_maxPow_smul, smul_sub, smul_one]
  rfl

end Filtration

section Lattice

variable {E F : Type*} [Field E] [ValuativeRel E] [Field F] [ValuativeRel F] [Algebra E F]
  [FiniteDimensional E F]

variable (E) in

noncomputable def normalSub (θ : F) : AddSubgroup 𝒪[F] :=
  (normalLattice (1 : 𝒪[E]) θ 0).toAddSubgroup.comap (𝒪[F].subtype : 𝒪[F] →+* F).toAddMonoidHom

omit [FiniteDimensional E F] in
theorem mem_normalSub {θ : F} {x : 𝒪[F]} :
    x ∈ normalSub E θ ↔ (x : F) ∈ normalLattice (1 : 𝒪[E]) θ 0 :=
  Iff.rfl

omit [ValuativeRel F] [FiniteDimensional E F] in

theorem normalLattice_zero_eq (π : 𝒪[E]) (θ : F) :
    normalLattice π θ 0 = normalLattice (1 : 𝒪[E]) θ 0 := by
  simp [normalLattice]

omit [ValuativeRel F] in
theorem sum_smul_mem_normalLattice {θ : F} (c : (F ≃ₐ[E] F) → 𝒪[E]) :
    ∑ σ, c σ • σ θ ∈ normalLattice (1 : 𝒪[E]) θ 0 :=
  (mem_normalLattice_iff 1 θ).mpr ⟨c, by simp⟩

variable [TopologicalSpace E] [IsNonarchimedeanLocalField E] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [ValuativeExtension E F]

attribute [local instance] integerAction integerUnitsAction

noncomputable abbrev normalSubAction (θ : F) : DistribMulAction (F ≃ₐ[E] F) (normalSub E θ) :=
  subgroupDistribMulAction (normalSub E θ) fun σ x hx ↦ by
    rw [mem_normalSub, coe_integer_smul]
    exact algEquiv_mem_normalLattice 1 θ σ hx

attribute [local instance] normalSubAction

theorem coe_normalSub_smul {θ : F} (σ : F ≃ₐ[E] F) (x : normalSub E θ) :
    (((σ • x : normalSub E θ) : 𝒪[F]) : F) = σ ((x : 𝒪[F]) : F) :=
  rfl

variable {θ : F} (hθ : LinearIndependent E fun σ : F ≃ₐ[E] F ↦ σ θ)
  (hθO : ∀ σ : F ≃ₐ[E] F, σ θ ∈ 𝒪[F])

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] in
include hθO in
theorem sum_smul_mem_integer (c : (F ≃ₐ[E] F) → 𝒪[E]) : ∑ σ, c σ • σ θ ∈ 𝒪[F] :=
  mem_integer_of_mem_normalLattice 1 θ hθO (sum_smul_mem_normalLattice c)

noncomputable def normalSubOfCoeff : ((F ≃ₐ[E] F) → 𝒪[E]) →+ normalSub E θ where
  toFun c := ⟨⟨∑ σ, c σ • σ θ, sum_smul_mem_integer hθO c⟩, sum_smul_mem_normalLattice c⟩
  map_zero' := by ext; simp
  map_add' c d := by ext; simp [add_smul, Finset.sum_add_distrib]

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] in
theorem coe_normalSubOfCoeff (c : (F ≃ₐ[E] F) → 𝒪[E]) :
    ((normalSubOfCoeff hθO c : 𝒪[F]) : F) = ∑ σ, c σ • σ θ :=
  rfl

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] in
include hθ in
theorem normalSubOfCoeff_bijective : Function.Bijective (normalSubOfCoeff hθO) := by
  constructor
  · intro c d h
    have := congrArg (fun x : normalSub E θ ↦ ((x : 𝒪[F]) : F)) h
    exact coeff_injective θ hθ this
  · intro x
    obtain ⟨c, hc⟩ := (mem_normalLattice_iff 1 θ).mp (mem_normalSub.mp x.2)
    refine ⟨c, ?_⟩
    ext
    rw [coe_normalSubOfCoeff, ← hc]
    simp

noncomputable def normalSubEquiv : ((F ≃ₐ[E] F) → 𝒪[E]) ≃+ normalSub E θ :=
  AddEquiv.ofBijective (normalSubOfCoeff hθO) (normalSubOfCoeff_bijective hθ hθO)

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] in
theorem normalSubEquiv_apply (c : (F ≃ₐ[E] F) → 𝒪[E]) :
    normalSubEquiv hθ hθO c = normalSubOfCoeff hθO c :=
  rfl

theorem smul_normalSubOfCoeff (τ : F ≃ₐ[E] F) (c : (F ≃ₐ[E] F) → 𝒪[E]) :
    τ • normalSubOfCoeff hθO c = normalSubOfCoeff hθO (fun σ ↦ c (τ⁻¹ * σ)) := by
  ext
  rw [coe_normalSub_smul, coe_normalSubOfCoeff, coe_normalSubOfCoeff]
  have := algEquiv_smul_sum (1 : 𝒪[E]) θ τ 0 c
  simpa using this

end Lattice

section Regular

variable {Γ O : Type*} [Fintype Γ] [AddCommGroup O] {p n : ℕ}
  (b : Module.Basis (Fin n) (ZMod p) (ModN O p))

noncomputable def coeffToRegular : (Γ → O) →+ (Fin n → MonoidAlgebra (ZMod p) Γ) where
  toFun c i := ∑ σ, MonoidAlgebra.single σ (b.repr (Submodule.Quotient.mk (c σ)) i)
  map_zero' := by
    funext i
    simp
  map_add' c d := by
    funext i
    simp [Finset.sum_add_distrib, MonoidAlgebra.single_add]

theorem coeff_coeffToRegular (c : Γ → O) (i : Fin n) (τ : Γ) :
    (coeffToRegular b c i).coeff τ = b.repr (Submodule.Quotient.mk (c τ)) i := by
  classical
  simp [coeffToRegular, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem coeffToRegular_eq_zero_iff (c : Γ → O) :
    coeffToRegular b c = 0 ↔ c ∈ LinearMap.range (LinearMap.lsmul ℤ (Γ → O) p) := by
  rw [mem_range_lsmul_iff]
  constructor
  · intro h
    have h0 : ∀ τ, (Submodule.Quotient.mk (c τ) : ModN O p) = 0 := by
      intro τ
      apply b.repr.injective
      ext i
      have := congrArg (fun x ↦ (x i).coeff τ) h
      simpa [coeff_coeffToRegular] using this
    choose y hy using fun τ ↦ (mem_range_lsmul_iff).mp ((Submodule.Quotient.mk_eq_zero _).mp (h0 τ))
    exact ⟨y, funext fun τ ↦ by simpa using hy τ⟩
  · rintro ⟨y, rfl⟩
    funext i
    apply MonoidAlgebra.coeff_injective
    ext τ
    rw [coeff_coeffToRegular]
    simp

variable (Γ) in
theorem coeffToRegular_surjective : Function.Surjective (coeffToRegular (Γ := Γ) b) := by
  intro f
  choose c hc using fun τ : Γ ↦ Submodule.Quotient.mk_surjective _
    (b.repr.symm ((Finsupp.equivFunOnFinite (α := Fin n)).symm fun i ↦ (f i).coeff τ))
  refine ⟨c, ?_⟩
  funext i
  apply MonoidAlgebra.coeff_injective
  ext τ
  rw [coeff_coeffToRegular, hc τ]
  simp

theorem coeffToRegular_perm [Group Γ] (τ : Γ) (c : Γ → O) :
    coeffToRegular b (fun σ ↦ c (τ⁻¹ * σ)) =
      piRep (Fin n) (Representation.leftRegular (ZMod p) Γ) τ (coeffToRegular b c) := by
  classical
  funext i
  apply MonoidAlgebra.coeff_injective
  ext ρ
  rw [piRep_apply, coeff_coeffToRegular]
  simp only [coeffToRegular, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum,
    Representation.ofMulAction_single, smul_eq_mul, MonoidAlgebra.coeff_sum,
    MonoidAlgebra.coeff_single, Finset.sum_apply', Finsupp.single_apply]
  rw [Finset.sum_eq_single (τ⁻¹ * ρ)]
  · simp
  · intro σ _ hσ
    refine ite_eq_right_iff.mpr fun h => absurd ?_ hσ
    rw [← h]
    group
  · simp

end Regular

end UnitsLattice

-- from ModNEquivOfSurjectiveApplyModNRep.lean
section ModNEquiv
open ValuativeRel IsLocalRing

section MonoidAlgebra

instance finite_monoidAlgebra {R M : Type*} [Semiring R] [Finite R] [Finite M] :
    Finite (MonoidAlgebra R M) :=
  Finite.of_injective (fun x : MonoidAlgebra R M ↦ (x.coeff : M → R))
    (fun _ _ h ↦ MonoidAlgebra.coeff_injective (DFunLike.coe_injective h))

end MonoidAlgebra

section ModNEquiv

variable {n : ℕ} {A X : Type*} [AddCommGroup A] [AddCommGroup X] [Module (ZMod n) X]

noncomputable def modNEquivOfSurjective (φ : A →+ X) (hs : Function.Surjective φ)
    (hker : ∀ a, φ a = 0 ↔ a ∈ LinearMap.range (LinearMap.lsmul ℤ A n)) :
    ModN A n ≃ₗ[ZMod n] X :=
  LinearEquiv.ofBijective
    (((LinearMap.range (LinearMap.lsmul ℤ A n)).liftQ φ.toIntLinearMap
      fun a ha ↦ LinearMap.mem_ker.mpr ((hker a).mpr ha)).toAddMonoidHom.toZModLinearMap n)
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact (Submodule.Quotient.mk_eq_zero _).mpr ((hker a).mp hx),
    fun x ↦ by
      obtain ⟨a, ha⟩ := hs x
      exact ⟨Submodule.Quotient.mk a, ha⟩⟩

theorem modNEquivOfSurjective_mk (φ : A →+ X) (hs : Function.Surjective φ)
    (hker : ∀ a, φ a = 0 ↔ a ∈ LinearMap.range (LinearMap.lsmul ℤ A n)) (a : A) :
    modNEquivOfSurjective φ hs hker (Submodule.Quotient.mk a) = φ a :=
  rfl

theorem modNEquivOfSurjective_apply_modNRep {Γ : Type*} [Group Γ] [DistribMulAction Γ A]
    (ρ : Representation (ZMod n) Γ X) (φ : A →+ X) (hs : Function.Surjective φ)
    (hker : ∀ a, φ a = 0 ↔ a ∈ LinearMap.range (LinearMap.lsmul ℤ A n))
    (hφ : ∀ (γ : Γ) (a : A), φ (γ • a) = ρ γ (φ a)) (γ : Γ) (x : ModN A n) :
    modNEquivOfSurjective φ hs hker (modNRep Γ A n γ x) =
      ρ γ (modNEquivOfSurjective φ hs hker x) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [modNRep_mk, modNEquivOfSurjective_mk, modNEquivOfSurjective_mk]
  exact hφ γ a

end ModNEquiv

section Int

abbrev trivialIntAction (Γ : Type*) [Monoid Γ] : DistribMulAction Γ (ULift.{u} ℤ) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

theorem finite_modN_uliftInt (l : ℕ) [NeZero l] : Finite (ModN (ULift.{u} ℤ) l) := by
  let e : ULift.{u} ℤ ≃+ ℤ := AddEquiv.ulift
  let b : Module.Basis Unit ℤ (ULift.{u} ℤ) :=
    (Module.Basis.singleton Unit ℤ).map e.symm.toIntLinearEquiv
  exact Finite.of_equiv _ (ModN.basis (n := l) b).equivFun.symm.toEquiv

theorem finite_torsN_uliftInt (l : ℕ) [NeZero l] : Finite (TorsN (ULift.{u} ℤ) l) := by
  have : Subsingleton (TorsN (ULift.{u} ℤ) l) := ⟨fun x y ↦ by
    have hx := (mem_ker_lsmul_iff l (x : ULift.{u} ℤ)).mp x.2
    have hy := (mem_ker_lsmul_iff l (y : ULift.{u} ℤ)).mp y.2
    have h0 : ∀ z : ULift.{u} ℤ, l • z = 0 → z = 0 := fun z hz ↦ by
      have h := congrArg (AddEquiv.ulift : ULift.{u} ℤ ≃+ ℤ) hz
      rw [map_nsmul, map_zero, nsmul_eq_mul, mul_eq_zero] at h
      rcases h with h | h
      · exact absurd h (by exact_mod_cast NeZero.ne l)
      · exact AddEquiv.ulift.injective (h.trans (map_zero _).symm)
    exact Subtype.ext ((h0 _ hx).trans (h0 _ hy).symm)⟩
  infer_instance

end Int

section Valuation

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The normalized order `Fˣ → ℤ` (the Library's `normalizedUnitOrder`), with values in
`ULift ℤ`. -/
noncomputable def ordHom : Additive Fˣ →+ ULift.{u} ℤ :=
  (AddEquiv.ulift.symm : ℤ ≃+ ULift.{u} ℤ).toAddMonoidHom.comp
    (ClassFieldTheory.Local.normalizedUnitOrder F)

variable {F}

theorem ordHom_apply (x : Additive Fˣ) :
    ordHom F x = ULift.up (ClassFieldTheory.Local.normalizedUnitOrder F x) :=
  rfl

theorem ordHom_surjective : Function.Surjective (ordHom F) := by
  intro m
  obtain ⟨x, hx⟩ := ClassFieldTheory.Local.normalizedUnitOrder_surjective F m.down
  exact ⟨x, by rw [ordHom_apply, hx]⟩

theorem ordHom_exact : Function.Exact (integerUnitsMap F).toAdditive (ordHom F) := by
  intro x
  rw [ordHom_apply]
  constructor
  · intro h
    have h0 : ClassFieldTheory.Local.normalizedUnitOrder F x = 0 := congrArg ULift.down h
    have h1 : valuation F ((x.toMul : Fˣ) : F) = 1 :=
      (ClassFieldTheory.Local.normalizedUnitOrder_eq_zero_iff F x.toMul).mp h0
    obtain ⟨u, hu⟩ := mem_range_integerUnitsMap_iff.mpr h1
    exact ⟨Additive.ofMul u, by rw [MonoidHom.toAdditive_apply_apply, toMul_ofMul, hu]; rfl⟩
  · rintro ⟨u, rfl⟩
    apply ULift.ext
    exact (ClassFieldTheory.Local.normalizedUnitOrder_eq_zero_iff F _).mpr
      (valuation_integerUnitsMap u.toMul)

end Valuation

section Subgroup

theorem finite_quotient_range_toAdditive {G : Type*} [CommGroup G] (H : Subgroup G)
    [H.FiniteIndex] : Finite (Additive G ⧸ (H.subtype.toAdditive).range) := by
  have h : (H.subtype.toAdditive).range = H.toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_range]
    change _ ↔ x.toMul ∈ H
    constructor
    · rintro ⟨a, rfl⟩
      exact a.toMul.2
    · intro hx
      exact ⟨Additive.ofMul ⟨x.toMul, hx⟩, rfl⟩
  rw [h]
  have : H.toAddSubgroup.FiniteIndex :=
    ⟨by rw [Subgroup.index_toAddSubgroup]; exact Subgroup.FiniteIndex.index_ne_zero⟩
  infer_instance

theorem toAdditive_subtype_injective {G : Type*} [CommGroup G] (H : Subgroup G) :
    Function.Injective H.subtype.toAdditive :=
  fun _ _ h ↦ Additive.toMul.injective (Subtype.ext (Additive.ofMul.injective h))

theorem finite_modN_of_finite_cokernel {A B : Type*} [AddCommGroup A] [AddCommGroup B] {n : ℕ}
    (f : B →+ A) [Finite (A ⧸ f.range)] [Finite (ModN B n)] : Finite (ModN A n) := by
  have hfh : Function.Exact f (QuotientAddGroup.mk' f.range) :=
    fun y ↦ by rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; rfl
  have : Finite (ModN (A ⧸ f.range) n) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  exact finite_modN_of_exact (QuotientAddGroup.mk'_surjective f.range) hfh

end Subgroup

section Torsion

theorem finite_torsN_of_torsion_trivial {A : Type*} [AddCommGroup A] {n : ℕ}
    (h : ∀ a : A, n • a = 0 → a = 0) : Finite (TorsN A n) :=
  have : Subsingleton (TorsN A n) := ⟨fun x y ↦ Subtype.ext
    ((h _ ((mem_ker_lsmul_iff n _).mp x.2)).trans (h _ ((mem_ker_lsmul_iff n _).mp y.2)).symm)⟩
  Finite.of_subsingleton

variable {F : Type*} [Field F] [ValuativeRel F]

theorem integer_subgroup_torsion {m : ℕ} (hm : (m : F) ≠ 0) (H : AddSubgroup 𝒪[F]) (a : H)
    (ha : m • a = 0) : a = 0 := by
  have hm' : (m : 𝒪[F]) ≠ 0 := fun h ↦ hm (by simpa using congrArg Subtype.val h)
  have h := congrArg (fun x : H ↦ (x : 𝒪[F])) ha
  simp only [AddSubgroup.coe_nsmul, nsmul_eq_mul, ZeroMemClass.coe_zero, mul_eq_zero, hm',
    false_or] at h
  exact Subtype.ext h

end Torsion

section Residue

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  {p : ℕ}

noncomputable def modNIntegerEquiv : ModN 𝒪[E] p ≃ₗ[ℤ] 𝒪[E] ⧸ Ideal.span {(p : 𝒪[E])} :=
  (Submodule.quotEquivOfEq _ _ (by
    ext x
    rw [mem_range_lsmul_iff, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
    simp only [nsmul_eq_mul, mul_comm])).trans
    (Submodule.Quotient.restrictScalarsEquiv ℤ (Ideal.span {(p : 𝒪[E])}))

variable [Fact p.Prime]

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in

theorem finrank_modN_integer {n : ℕ} (hn : Nat.card (𝒪[E] ⧸ Ideal.span {(p : 𝒪[E])}) = p ^ n) :
    Finite (ModN 𝒪[E] p) ∧ Module.finrank (ZMod p) (ModN 𝒪[E] p) = n := by
  have hp := (Fact.out : p.Prime)
  have hcard : Nat.card (ModN 𝒪[E] p) = p ^ n := (Nat.card_congr modNIntegerEquiv.toEquiv).trans hn
  have hfin : Finite (ModN 𝒪[E] p) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  refine ⟨hfin, ?_⟩
  have := Fintype.ofFinite (ModN 𝒪[E] p)
  have h := Module.card_eq_pow_finrank (K := ZMod p) (V := ModN 𝒪[E] p)
  rw [ZMod.card, ← Nat.card_eq_fintype_card, hcard] at h
  exact (Nat.pow_right_injective hp.two_le h).symm

theorem exists_card_quotient_eq_pow (hp0 : (p : E) ≠ 0) :
    ∃ n, Nat.card (𝒪[E] ⧸ Ideal.span {(p : 𝒪[E])}) = p ^ n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  have hp' : (p : 𝒪[E]) ≠ 0 := fun h ↦ hp0 (by simpa using congrArg Subtype.val h)
  obtain ⟨m, ε, hm⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp' hπ
  have hfin : Finite (𝒪[E] ⧸ Ideal.span {(p : 𝒪[E])}) := by
    refine IsLocalRing.finite_quotient_iff.mpr ⟨m, fun x hx ↦ ?_⟩
    obtain ⟨a, rfl⟩ := (mem_maximalIdeal_pow_iff hπ).mp hx
    rw [Ideal.mem_span_singleton', hm]
    exact ⟨((ε⁻¹ : 𝒪[E]ˣ) : 𝒪[E]) * a, by
      have := ε.inv_mul
      linear_combination (π ^ m * a) * this⟩
  have hfin' : Finite (ModN 𝒪[E] p) := Finite.of_equiv _ modNIntegerEquiv.symm.toEquiv
  have := Fintype.ofFinite (ModN 𝒪[E] p)
  refine ⟨Module.finrank (ZMod p) (ModN 𝒪[E] p), ?_⟩
  rw [← Nat.card_congr modNIntegerEquiv.toEquiv, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]

end Residue

section Filtration

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {p e : ℕ} {ε : 𝒪[F]ˣ} (hpe : (p : 𝒪[F]) = ϖ ^ e * ε)
include hϖ hpe

theorem finite_modN_maxPow (k : ℕ) : Finite (ModN (maxPow F k) p) := by
  have hfin : Finite (𝒪[F] ⧸ 𝓂[F] ^ (k + e)) :=
    IsLocalRing.finite_quotient_iff.mpr ⟨k + e, le_rfl⟩
  let φ : maxPow F k →+ 𝒪[F] ⧸ 𝓂[F] ^ (k + e) :=
    (Ideal.Quotient.mk (𝓂[F] ^ (k + e))).toAddMonoidHom.comp (maxPow F k).subtype
  have hφ : ∀ a : maxPow F k, φ a = 0 ↔ a ∈ LinearMap.range (LinearMap.lsmul ℤ (maxPow F k) p) := by
    intro a
    rw [mem_range_lsmul_iff]
    change Ideal.Quotient.mk _ (a : 𝒪[F]) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_maximalIdeal_pow_add_iff hϖ hpe]
    constructor
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, Subtype.ext (by simp [h])⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, by simp⟩
  let L := (LinearMap.range (LinearMap.lsmul ℤ (maxPow F k) p)).liftQ φ.toIntLinearMap
    fun a ha ↦ LinearMap.mem_ker.mpr ((hφ a).mpr ha)
  refine Finite.of_injective L ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact (Submodule.Quotient.mk_eq_zero _).mpr ((hφ a).mp hx)

end Filtration

section Galois

variable {E F : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F]

attribute [local instance] integerUnitsAction

theorem discreteLocalValuation_algEquiv_apply (σ : F ≃ₐ[E] F) (x : F) :
    ClassFieldTheory.Local.discreteLocalValuation F (σ x) =
      ClassFieldTheory.Local.discreteLocalValuation F x := by
  have h := valuation_algEquiv_apply E F σ x
  apply le_antisymm
  · rw [← Valuation.vle_iff_le, (valuation F).vle_iff_le, h]
  · rw [← Valuation.vle_iff_le, (valuation F).vle_iff_le, h]

theorem ordHom_smul (σ : F ≃ₐ[E] F) (x : Additive Fˣ) : ordHom F (σ • x) = ordHom F x := by
  rw [ordHom_apply, ordHom_apply]
  congr 1
  change -WithZero.log (ClassFieldTheory.Local.discreteLocalValuation F (σ ((x.toMul : Fˣ) : F))) =
    -WithZero.log (ClassFieldTheory.Local.discreteLocalValuation F ((x.toMul : Fˣ) : F))
  rw [discreteLocalValuation_algEquiv_apply]

theorem integerUnitsMap_toAdditive_smul (σ : F ≃ₐ[E] F) (a : Additive 𝒪[F]ˣ) :
    (integerUnitsMap F).toAdditive (σ • a) = σ • (integerUnitsMap F).toAdditive a :=
  congrArg Additive.ofMul (integerUnitsMap_smul σ a.toMul)

omit [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] in

theorem finite_torsN_integerUnits (l : ℕ) [NeZero l] : Finite (TorsN (Additive 𝒪[F]ˣ) l) := by
  classical
  have hl : 0 < l := Nat.pos_of_ne_zero (NeZero.ne l)
  have key : ∀ x : TorsN (Additive 𝒪[F]ˣ) l,
      (((x : Additive 𝒪[F]ˣ).toMul : 𝒪[F]ˣ) : 𝒪[F]) ∈ Polynomial.nthRootsFinset l (1 : 𝒪[F]) := by
    intro x
    rw [Polynomial.mem_nthRootsFinset hl, ← Units.val_pow_eq_pow_val, ← toMul_nsmul,
      (mem_ker_lsmul_iff l _).mp x.2]
    rfl
  refine Finite.of_injective
    (fun x : TorsN (Additive 𝒪[F]ˣ) l ↦
      (⟨_, key x⟩ : (Polynomial.nthRootsFinset l (1 : 𝒪[F]) : Set 𝒪[F]))) ?_
  intro x y h
  exact Subtype.ext (Additive.toMul.injective (Units.ext (congrArg Subtype.val h)))

variable {l : ℕ} [NeZero l] (d : AdditiveFunction.{u} l (F ≃ₐ[E] F))

theorem g_units_eq_one_add [Finite (ModN (Additive 𝒪[F]ˣ) l)] :
    d.g (Additive Fˣ) = d.one + d.g (Additive 𝒪[F]ˣ) := by
  let := trivialIntAction.{u} (F ≃ₐ[E] F)
  have := finite_torsN_integerUnits (F := F) l
  have := finite_modN_uliftInt.{u} l
  have := finite_torsN_uliftInt.{u} l
  have hinj : Function.Injective (integerUnitsMap F).toAdditive :=
    fun _ _ h ↦ Additive.toMul.injective (integerUnitsMap_injective (Additive.ofMul.injective h))
  rw [d.g_add (integerUnitsMap F).toAdditive (ordHom F) integerUnitsMap_toAdditive_smul
      (fun σ x ↦ ordHom_smul σ x) hinj ordHom_exact ordHom_surjective,
    d.g_of_trivial_int (ULift.{u} ℤ) (fun _ _ ↦ rfl) AddEquiv.ulift, add_comm]

attribute [local instance] integerAction integerUnitsAction unitFiltrationAction

attribute [local instance] maxPowAction normalSubAction

omit [FiniteDimensional E F] in

theorem valuation_le_of_mem_maxPow {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {k : ℕ} {x : 𝒪[F]}
    (hx : x ∈ 𝓂[F] ^ k) : valuation F (x : F) ≤ valuation F (ϖ : F) ^ k := by
  obtain ⟨a, rfl⟩ := (mem_maximalIdeal_pow_iff hϖ).mp hx
  rw [Subring.coe_mul, map_mul, SubmonoidClass.coe_pow, map_pow]
  exact mul_le_of_le_one_right' a.2

theorem exists_maxPow_le_normalSub [IsGalois E F] {θ : F}
    (hθ : LinearIndependent E fun σ : F ≃ₐ[E] F ↦ σ θ) :
    ∃ j, ∀ k ≥ j, maxPow F k ≤ normalSub E θ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hopen := isOpen_normalLattice π θ hπ hθ 0
  rw [normalLattice_zero_eq] at hopen
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).mp
    (hopen.mem_nhds (Submodule.zero_mem _))
  obtain ⟨j, -, hj⟩ := exists_pow_lt hϖ γ.ne_zero
  refine ⟨j, fun k hk x hx ↦ mem_normalSub.mpr (hγ ?_)⟩
  have h1 : valuation F (ϖ : F) ≤ 1 := ϖ.2
  calc valuation F (x : F) ≤ valuation F (ϖ : F) ^ k := valuation_le_of_mem_maxPow hϖ hx
    _ ≤ valuation F (ϖ : F) ^ j := pow_le_pow_right_of_le_one' h1 hk
    _ < γ := hj

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension E F]
  [FiniteDimensional E F] in

theorem finite_quotient_maxPow {θ : F} {k : ℕ} (hle : maxPow F k ≤ normalSub E θ) :
    Finite (normalSub E θ ⧸ (AddSubgroup.inclusion hle).range) := by
  have hr : (AddSubgroup.inclusion hle).range = (maxPow F k).addSubgroupOf (normalSub E θ) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hfin : Finite (𝒪[F] ⧸ maxPow F k) :=
    IsLocalRing.finite_quotient_iff.mpr ⟨k, le_rfl⟩
  have hidx : (maxPow F k).index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  have hrel : (maxPow F k).relIndex (normalSub E θ) ≠ 0 :=
    fun h ↦ hidx (Nat.eq_zero_of_zero_dvd (h ▸ AddSubgroup.relIndex_dvd_index_of_le hle))
  rw [hr]
  have : ((maxPow F k).addSubgroupOf (normalSub E θ)).FiniteIndex := ⟨hrel⟩
  infer_instance

end Galois

section LemmaA

variable {E F : Type u} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]
  [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra E F] [ValuativeExtension E F] [FiniteDimensional E F] [IsGalois E F]
  {l : ℕ} [Fact l.Prime] (d : AdditiveFunction.{u} l (F ≃ₐ[E] F))

attribute [local instance] integerAction integerUnitsAction unitFiltrationAction maxPowAction normalSubAction

theorem g_integerUnits_eq (hl : (l : F) ≠ 0) {n : ℕ}
    (hn : Nat.card (𝒪[E] ⧸ Ideal.span {(l : 𝒪[E])}) = l ^ n) :
    Finite (ModN (Additive 𝒪[F]ˣ) l) ∧
      d.g (Additive 𝒪[F]ˣ) = n * d.toFun (MonoidAlgebra (ZMod l) (F ≃ₐ[E] F))
        (Representation.leftRegular (ZMod l) (F ≃ₐ[E] F)) := by
  have hlp : l.Prime := Fact.out
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hl' : (l : 𝒪[F]) ≠ 0 := fun h ↦ hl (by simpa using congrArg Subtype.val h)
  obtain ⟨e, ε, hpe⟩ : ∃ (e : ℕ) (ε : 𝒪[F]ˣ), (l : 𝒪[F]) = ϖ ^ e * ε := by
    obtain ⟨e, ε, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl' hϖ
    exact ⟨e, ε, by rw [h, mul_comm]⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  obtain ⟨θ, hθ, hθO⟩ := exists_normalBasis_integer (K := E) (L := F) hπ
  obtain ⟨j, hj⟩ := exists_maxPow_le_normalSub hθ
  have hk : e + 1 ≤ max j (e + 1) := le_max_right _ _
  have hle : maxPow F (max j (e + 1)) ≤ normalSub E θ := hj _ (le_max_left _ _)
  set k := max j (e + 1)
  obtain ⟨hfinE, hrank⟩ := finrank_modN_integer (E := E) hn
  let b : Module.Basis (Fin n) (ZMod l) (ModN 𝒪[E] l) := Module.finBasisOfFinrankEq _ _ hrank

  set U := unitFiltration F k
  have hUt : ∀ a : Additive U, l • a = 0 → a = 0 := by
    intro a ha
    apply Additive.toMul.injective
    have h1 : (a.toMul : 𝒪[F]ˣ) ^ l = 1 := by
      have := congrArg (fun b : Additive U ↦ ((b.toMul : U) : 𝒪[F]ˣ)) ha
      simpa using this
    exact Subtype.ext (eq_one_of_mem_unitFiltration_of_pow_eq_one hϖ hlp hpe hk a.toMul.2 h1)
  let e1 := modNEquivOfSurjective (unitToModN hϖ hpe (Nat.le_of_succ_le hk))
    (unitToModN_surjective hϖ hpe hk) (unitToModN_eq_zero_iff hϖ hpe hlp hk)
  have he1 := modNEquivOfSurjective_apply_modNRep (modNRep (F ≃ₐ[E] F) (maxPow F k) l)
    (unitToModN hϖ hpe (Nat.le_of_succ_le hk)) (unitToModN_surjective hϖ hpe hk)
    (unitToModN_eq_zero_iff hϖ hpe hlp hk) (unitToModN_smul ϖ hϖ hpe _)
  have := finite_modN_maxPow hϖ hpe k
  have : Finite (ModN (Additive U) l) := Finite.of_equiv _ e1.symm.toEquiv
  have := finite_torsN_of_torsion_trivial hUt
  have hPt : ∀ a : maxPow F k, l • a = 0 → a = 0 := integer_subgroup_torsion hl _
  have := finite_torsN_of_torsion_trivial hPt

  let N := normalSubEquiv hθ hθO
  let φ : normalSub E θ →+ (Fin n → MonoidAlgebra (ZMod l) (F ≃ₐ[E] F)) :=
    (coeffToRegular b).comp N.symm.toAddMonoidHom
  have hφs : Function.Surjective φ :=
    (coeffToRegular_surjective (F ≃ₐ[E] F) b).comp N.symm.surjective
  have hφk : ∀ t, φ t = 0 ↔ t ∈ LinearMap.range (LinearMap.lsmul ℤ (normalSub E θ) l) := by
    intro t
    change coeffToRegular b (N.symm t) = 0 ↔ _
    rw [coeffToRegular_eq_zero_iff, mem_range_lsmul_iff, mem_range_lsmul_iff]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨N y, by rw [← map_nsmul, hy, AddEquiv.apply_symm_apply]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨N.symm y, by rw [map_nsmul]⟩
  have hφγ : ∀ (σ : F ≃ₐ[E] F) (t : normalSub E θ), φ (σ • t) =
      piRep (Fin n) (Representation.leftRegular (ZMod l) (F ≃ₐ[E] F)) σ (φ t) := by
    intro σ t
    obtain ⟨c, rfl⟩ := N.surjective t
    change coeffToRegular b (N.symm (σ • N c)) = piRep (Fin n)
      (Representation.leftRegular (ZMod l) (F ≃ₐ[E] F)) σ (coeffToRegular b (N.symm (N c)))
    rw [AddEquiv.symm_apply_apply, normalSubEquiv_apply, smul_normalSubOfCoeff,
      ← normalSubEquiv_apply hθ, AddEquiv.symm_apply_apply, coeffToRegular_perm]
  let e2 := modNEquivOfSurjective φ hφs hφk
  have he2 := modNEquivOfSurjective_apply_modNRep _ φ hφs hφk hφγ
  have : Finite (ModN (normalSub E θ) l) := Finite.of_equiv _ e2.symm.toEquiv
  have hTt : ∀ a : normalSub E θ, l • a = 0 → a = 0 := integer_subgroup_torsion hl _
  have := finite_quotient_maxPow hle
  have := finite_quotient_range_toAdditive U
  refine ⟨finite_modN_of_finite_cokernel U.subtype.toAdditive, ?_⟩
  rw [d.g_eq_of_finite_cokernel U.subtype.toAdditive (fun _ _ ↦ rfl)
      (toAdditive_subtype_injective U),
    d.g_eq_of_torsion_trivial (Additive U) hUt, d.toFun_congr _ _ e1 he1,
    ← d.g_eq_of_torsion_trivial (maxPow F k) hPt,
    ← d.g_eq_of_finite_cokernel (AddSubgroup.inclusion hle) (fun _ _ ↦ rfl)
      (AddSubgroup.inclusion_injective hle),
    d.g_eq_of_torsion_trivial (normalSub E θ) hTt, d.toFun_congr _ _ e2 he2, d.toFun_pi]

theorem g_units_eq (hl : (l : E) ≠ 0) {n : ℕ}
    (hn : Nat.card (𝒪[E] ⧸ Ideal.span {(l : 𝒪[E])}) = l ^ n) :
    d.g (Additive Fˣ) = d.one + n * d.toFun (MonoidAlgebra (ZMod l) (F ≃ₐ[E] F))
      (Representation.leftRegular (ZMod l) (F ≃ₐ[E] F)) := by
  have hlF : (l : F) ≠ 0 := by
    rw [← map_natCast (algebraMap E F)]
    exact (map_ne_zero _).mpr hl
  obtain ⟨hfin, hg⟩ := g_integerUnits_eq d hlF hn
  rw [g_units_eq_one_add d, hg]

end LemmaA

end ModNEquiv

-- from VanishingUnits.lean
section VanishingUnits
open ValuativeRel IsLocalRing

section Group

variable {G : Type*} [CommGroup G]

theorem mul_inv_mem_of_iterate_eq {l m : ℕ} (P O : Subgroup G) (s : G →* G)
    (hPl : ∀ y : G, y ^ l ∈ P) (hO : ∀ x : G, s x * x⁻¹ ∈ O)
    (hOP : ∀ e ∈ O, s e * e⁻¹ ∈ P) (hm : m.Coprime l) (hsm : ∀ x : G, s^[m] x = x) (x : G) :
    s x * x⁻¹ ∈ P := by
  have hPn : P.Normal := Subgroup.normal_of_isMulCommutative P
  have hq : ∀ a b : G, a * b⁻¹ ∈ P → (a : G ⧸ P) = b := fun a b h => by
    rw [QuotientGroup.eq]
    have := P.inv_mem h
    rwa [mul_inv_rev, inv_inv, mul_comm] at this
  set c := s x * x⁻¹ with hc
  have hOs : ∀ e ∈ O, s e ∈ O := fun e he => by
    have := O.mul_mem (hO e) he
    rwa [inv_mul_cancel_right] at this
  have hcO : ∀ j : ℕ, s^[j] c ∈ O := fun j => by
    induction j with
    | zero => exact hO x
    | succ j ih => rw [Function.iterate_succ_apply']; exact hOs _ ih
  have hcj : ∀ j : ℕ, ((s^[j] c : G) : G ⧸ P) = c := fun j => by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', hq _ _ (hOP _ (hcO j)), ih]
  have hsx : s x = x * c := by rw [hc, mul_comm (s x), mul_inv_cancel_left]
  have hxj : ∀ j : ℕ, ((s^[j] x : G) : G ⧸ P) = (x : G ⧸ P) * (c : G ⧸ P) ^ j := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply, hsx, iterate_map_mul, QuotientGroup.mk_mul, ih,
        hcj, pow_succ, mul_assoc]
  have h1 : (c : G ⧸ P) ^ m = 1 := by
    have h := hxj m
    rw [hsm] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  have h2 : (c : G ⧸ P) ^ l = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hPl c
  have h3 : (c : G ⧸ P) = 1 := by
    have h := (pow_gcd_eq_one (a := (c : G ⧸ P))).2 ⟨h1, h2⟩
    rwa [Nat.Coprime.gcd_eq_one hm, pow_one] at h
  exact (QuotientGroup.eq_one_iff c).1 h3

end Group

section LocalField

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_map_units_eq_mul_pow {l m : ℕ} (hl : (l : 𝓀[F]) ≠ 0) (σ : F ≃+* F)
    (hval : ∀ x : F, valuation F (σ x) = valuation F x)
    (hin : ∀ x : F, valuation F x ≤ 1 → valuation F (σ x - x) < 1)
    (hm : m.Coprime l) (hσm : ∀ x : F, σ^[m] x = x) (u : Fˣ) :
    ∃ y : Fˣ, Units.map (σ : F →* F) u = u * y ^ l := by
  set s : Fˣ →* Fˣ := Units.map (σ : F →* F) with hs_def
  have hs : ∀ x : Fˣ, ((s x : Fˣ) : F) = σ x := fun x => rfl
  let P : Subgroup Fˣ := (powMonoidHom l : Fˣ →* Fˣ).range
  let O : Subgroup Fˣ :=
    { carrier := {x | valuation F (x : F) = 1}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at ha hb ⊢
        rw [ha, hb, mul_one]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at ha ⊢
        rw [ha, inv_one] }
  have hmemO : ∀ x : Fˣ, x ∈ O ↔ valuation F (x : F) = 1 := fun x => Iff.rfl
  have hv0 : ∀ x : Fˣ, valuation F (x : F) ≠ 0 := fun x => (valuation F).ne_zero_iff.2 x.ne_zero
  have hO : ∀ x : Fˣ, s x * x⁻¹ ∈ O := fun x => by
    rw [hmemO, Units.val_mul, hs, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hval,
      mul_inv_cancel₀ (hv0 x)]
  have hOP : ∀ e ∈ O, s e * e⁻¹ ∈ P := fun e he => by
    rw [hmemO] at he
    set t := s e * e⁻¹ with ht
    have htv : valuation F (t : F) = 1 := (hmemO t).1 (hO e)
    have ht1 : valuation F ((t : F) - 1) < 1 := by
      have e1 : (t : F) - 1 = (σ e - e) * (e : F)⁻¹ := by
        rw [ht, Units.val_mul, hs, Units.val_inv_eq_inv_val, sub_mul,
          mul_inv_cancel₀ e.ne_zero]
      rw [e1, map_mul, map_inv₀, he, inv_one, mul_one]
      exact hin _ he.le
    obtain ⟨t', ht'⟩ := mem_range_integerUnitsMap_iff.2 htv
    have ht'F : ((t' : 𝒪[F]) : F) = t := by rw [← coe_integerUnitsMap_apply, ht']
    have hmem : t' ∈ unitFiltration F 1 := by
      rw [mem_unitFiltration, pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h1 := valuation_unit hu.unit
      rw [IsUnit.unit_spec] at h1
      have h2 : (((t' : 𝒪[F]) - 1 : 𝒪[F]) : F) = (t : F) - 1 := by
        push_cast
        rw [ht'F]
      rw [h2] at h1
      exact (lt_irrefl _ (h1 ▸ ht1))
    obtain ⟨z, -, hz⟩ := exists_pow_eq_of_mem_unitFiltration_one hl hmem
    refine ⟨integerUnitsMap F z, ?_⟩
    rw [powMonoidHom_apply, ← map_pow, hz, ht']
  have hiter : ∀ (j : ℕ) (x : Fˣ), ((s^[j] x : Fˣ) : F) = σ^[j] (x : F) := fun j => by
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hs, ih]
  have hsm : ∀ x : Fˣ, s^[m] x = x := fun x => Units.ext (by rw [hiter, hσm])
  obtain ⟨y, hy⟩ := mul_inv_mem_of_iterate_eq P O s (fun y => ⟨y, rfl⟩) hO hOP hm hsm u
  refine ⟨y, ?_⟩
  rw [powMonoidHom_apply] at hy
  rw [hy, mul_comm (s u), mul_inv_cancel_left]

end LocalField

end VanishingUnits

end Langlands.GaloisCohomology.Local
