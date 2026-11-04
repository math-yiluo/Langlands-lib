import Langlands.Cohomology.DivisibleSystem.LevelProjective
import Langlands.Shimura.Coefficients.HarrisLattice

/-!
# Levels of `ℓ`-divisible systems over Harris's coefficient ring

Harris 1999, p.307: "Let `𝒪` denote the ring of integers of `L_ℓ`, and let `𝓛_W` be a
`K_ℓ`-stable `𝒪`-lattice in `W(L)`." Here `L_ℓ = L ⊗_ℚ ℚ_ℓ` (p.306) is the product of the
completions of `L` at the places above `ℓ`, and `𝒪` is the product of their valuation rings, the
Library's `HarrisCoefficientIntegers L p` for the finite place `p` of `ℚ`. The module
`LevelProjective` proves that the levels of an `ℓ`-divisible system of `R`-modules are projective
relative to modules killed by `ℓ ^ m` when `ℓ = u π ^ e` with `u` a unit, `e ≥ 1` and `(π)` a
maximal ideal (`IsUnitMulUniformizerPow`). In a product of two or more local rings an element
generating a maximal ideal is a unit in all but one factor, so this hypothesis fails for `𝒪`
whenever `ℓ` is a nonunit in two of its factors. This module proves the same projectivity under
a factorwise hypothesis that `𝒪` satisfies for every nonzero natural number `ℓ`:

* `IsFactorwiseUnitMulUniformizerPow ℓ ε π e`: idempotents `ε i` with `∑ i, ε i = 1`, elements
  `π i` generating maximal ideals, and `ℓ ε i = u π i ^ e i ε i` for units `u`; the exponent
  `e i` may be `0`. Lemmas `exists_unit_pow` and `pow_smul_smul_eq_zero`;
* `IsUnitMulUniformizerPow.factorwise` (one factor), and for a finite product `∏ i, S i` of rings
  `IsFactorwiseUnitMulUniformizerPow.pi` (with `span_mulSingle_eq_comap`) and
  `IsFactorwiseUnitMulUniformizerPow.exists_pi_of_isDiscreteValuationRing`;
* `PowQuotientFlat.exists_lift_smul`: from a module with `PowQuotientFlat π N`, `s • g` lifts
  along a surjection `p : X → Y` whenever `π ^ N` kills `s • X`;
* `DivisibleSystem.powQuotientFlat_factor`: the factor `ε i • T m` of the level `T m` of an
  `ℓ`-divisible system of `R`-modules satisfies `PowQuotientFlat (π i) (e i * m)`; hence
  `DivisibleSystem.exists_free_generators_factor` (the factor is free over
  `R ⧸ (π i ^ (e i * m))`), `DivisibleSystem.powTorsionProjective_obj_of_factorwise` (the level
  `T m` is projective relative to modules killed by `ℓ ^ m`) and
  `DivisibleSystem.underlyingPowTorsionProjectiveBelow_of_factorwise`;
* `coefficientIntegers_natCast_ne_zero` and
  `harrisCoefficientIntegers_isFactorwiseUnitMulUniformizerPow`: `HarrisCoefficientIntegers L p`
  satisfies the factorwise hypothesis for every nonzero natural number `ℓ`, with the
  idempotents of its factors and a uniformizer of every factor;
* over `HarrisCoefficientIntegers L p` and for `[NeZero ℓ]`:
  `DivisibleSystem.powTorsionProjective_obj_harrisCoefficientIntegers`,
  `DivisibleSystem.underlyingPowTorsionProjectiveBelow_harrisCoefficientIntegers`, and for
  Harris's complexes `C_m^{•,H}` of the truncated smooth Godement resolutions
  (`smoothGodementInvariantTotalSystem`, `proPSmoothGodementInvariantTotalSystem`) the forms
  `..._harrisCoefficientIntegers` of `TermwisePowTorsionProjective`, of the surjectivity of the
  transitions of `T_m(j) = Hom(C_m^{j,H}, W_m)` (Harris 1999, p.312, (4.10.3)), of the
  Mittag-Leffler condition of the `T_m(j)`, and of the Mittag-Leffler condition of the Hom
  complexes `Hom^•(C_m^{•,H}, W_m)`.

The level `T m` itself is not shown to be free over `R ⧸ (ℓ ^ m)`: its factors are free over
the rings `R ⧸ (π i ^ (e i * m))`, with possibly different ranks. The hypotheses of the
`H`-invariant systems (`hterm`, `hres`) and the unproved propositions of the parent modules stay
explicit.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

open scoped Pointwise

universe w v u

section Factorwise

variable {R : Type u} [CommRing R]

/-- `R` is the sum of the factors `R ε i` cut out by idempotents `ε i` with `∑ i, ε i = 1`, and on
the factor `R ε i` the scalar `ℓ` is a unit times `π i ^ e i`, where `π i` generates a maximal
ideal of `R`: `ℓ ε i = u π i ^ e i ε i` for a unit `u` of `R`. The exponent `e i` may be `0`, when
`ℓ` is a unit on the factor. -/
structure IsFactorwiseUnitMulUniformizerPow (ℓ : ℕ) {ι : Type*} [Fintype ι] (ε π : ι → R)
    (e : ι → ℕ) : Prop where
  idem : ∀ i, ε i * ε i = ε i
  sum_eq_one : ∑ i, ε i = 1
  isMaximal : ∀ i, (Ideal.span {π i}).IsMaximal
  exists_unit : ∀ i, ∃ u : Rˣ, (ℓ : R) * ε i = u * π i ^ e i * ε i

namespace IsFactorwiseUnitMulUniformizerPow

variable {ℓ : ℕ} {ι : Type*} [Fintype ι] {ε π : ι → R} {e : ι → ℕ}

/-- `ℓ ^ n ε i = u ^ n π i ^ (e i * n) ε i`. -/
lemma exists_unit_pow (h : IsFactorwiseUnitMulUniformizerPow ℓ ε π e) (i : ι) :
    ∃ u : Rˣ, ∀ n : ℕ, (ℓ : R) ^ n * ε i = (u : R) ^ n * π i ^ (e i * n) * ε i := by
  obtain ⟨u, hu⟩ := h.exists_unit i
  refine ⟨u, fun n => ?_⟩
  induction n with
  | zero => simp
  | succ n ih =>
    calc (ℓ : R) ^ (n + 1) * ε i = (u : R) ^ n * π i ^ (e i * n) * ((ℓ : R) * ε i) := by
          rw [pow_succ, mul_comm ((ℓ : R) ^ n) _, mul_assoc, ih]; ring
      _ = (u : R) ^ (n + 1) * π i ^ (e i * (n + 1)) * ε i := by
          rw [hu, mul_add, mul_one, pow_add, pow_succ]; ring

/-- On a module killed by `ℓ ^ m`, the factor `ε i` is killed by `π i ^ (e i * m)`. -/
lemma pow_smul_smul_eq_zero (h : IsFactorwiseUnitMulUniformizerPow ℓ ε π e) (i : ι) {m : ℕ}
    {M : Type*} [AddCommGroup M] [Module R M] (hM : ∀ x : M, (ℓ : R) ^ m • x = 0) (x : M) :
    π i ^ (e i * m) • ε i • x = 0 := by
  obtain ⟨u, hu⟩ := h.exists_unit_pow i
  have h1 : π i ^ (e i * m) * ε i = ((u⁻¹ : Rˣ) : R) ^ m * ((ℓ : R) ^ m * ε i) := by
    rw [hu, ← mul_assoc, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  rw [smul_smul, h1, mul_comm ((ℓ : R) ^ m) (ε i), ← smul_smul, ← smul_smul, hM, smul_zero,
    smul_zero]

end IsFactorwiseUnitMulUniformizerPow

/-- A single uniformizer `ℓ = u π ^ e` (`IsUnitMulUniformizerPow`) is the case of one factor,
with `ε = 1`. -/
lemma IsUnitMulUniformizerPow.factorwise {ℓ : ℕ} {π : R} {e : ℕ}
    (h : IsUnitMulUniformizerPow ℓ π e) :
    IsFactorwiseUnitMulUniformizerPow ℓ (fun _ : Unit => (1 : R)) (fun _ => π) (fun _ => e) where
  idem _ := one_mul 1
  sum_eq_one := by simp
  isMaximal _ := h.isMaximal
  exists_unit _ := by
    obtain ⟨u, hu⟩ := h.exists_unit
    exact ⟨u, by rw [mul_one, mul_one, hu]⟩

namespace IsFactorwiseUnitMulUniformizerPow

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, CommRing (S i)]

omit [Fintype ι] in
/-- In a finite product of rings `∏ i, S i`, the ideal generated by `Pi.mulSingle i a` (the
element with `a` at `i` and `1` elsewhere) is the preimage of the ideal `(a)` of `S i`. -/
lemma span_mulSingle_eq_comap (i : ι) (a : S i) :
    Ideal.span {(Pi.mulSingle i a : (j : ι) → S j)} =
      (Ideal.span {a}).comap (Pi.evalRingHom S i) := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y i, by simp⟩
  · rintro ⟨r, hr⟩
    refine ⟨Function.update x i r, funext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      simpa using hr
    · simp [Pi.mulSingle_eq_of_ne hj, Function.update_of_ne hj]

/-- If, in every factor `S i` of a finite product, `ℓ = u π i ^ e i` with `u` a unit and `π i`
generating a maximal ideal, the product `∏ i, S i` satisfies
`IsFactorwiseUnitMulUniformizerPow` with the idempotents `Pi.single i 1` and the elements
`Pi.mulSingle i (π i)`. -/
lemma pi {ℓ : ℕ} {π : (i : ι) → S i} {e : ι → ℕ} (hmax : ∀ i, (Ideal.span {π i}).IsMaximal)
    (hunit : ∀ i, ∃ u : (S i)ˣ, (ℓ : S i) = u * π i ^ e i) :
    IsFactorwiseUnitMulUniformizerPow ℓ (fun i => (Pi.single i 1 : (j : ι) → S j))
      (fun i => (Pi.mulSingle i (π i) : (j : ι) → S j)) e where
  idem i := by rw [← Pi.single_mul, one_mul]
  sum_eq_one := by
    funext j
    simp [Finset.sum_apply]
  isMaximal i := by
    rw [span_mulSingle_eq_comap]
    exact Ideal.comap_isMaximal_of_surjective _ fun r => ⟨Pi.single i r, by simp⟩
  exists_unit i := by
    obtain ⟨u, hu⟩ := hunit i
    refine ⟨Units.map (MonoidHom.mulSingle S i) u, funext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      simp [hu]
    · simp [Pi.single_eq_of_ne hj]

/-- In a finite product of discrete valuation rings in which `ℓ` is nonzero, `ℓ` is factorwise a
unit times a power of a uniformizer: choose a uniformizer of every factor. -/
lemma exists_pi_of_isDiscreteValuationRing [∀ i, IsDomain (S i)]
    [∀ i, IsDiscreteValuationRing (S i)] {ℓ : ℕ} (hℓ : ∀ i, (ℓ : S i) ≠ 0) :
    ∃ (π : (i : ι) → S i) (e : ι → ℕ),
      IsFactorwiseUnitMulUniformizerPow ℓ (fun i => (Pi.single i 1 : (j : ι) → S j))
        (fun i => (Pi.mulSingle i (π i) : (j : ι) → S j)) e := by
  choose π hπ using fun i => IsDiscreteValuationRing.exists_irreducible (S i)
  choose e u hu using fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hℓ i) (hπ i)
  exact ⟨π, e, pi (fun i => (IsDiscreteValuationRing.irreducible_iff_uniformizer (π i)).1 (hπ i) ▸
    IsLocalRing.maximalIdeal.isMaximal (S i)) fun i => ⟨u i, hu i⟩⟩

end IsFactorwiseUnitMulUniformizerPow

end Factorwise

section Lift

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

namespace PowQuotientFlat

variable {π : R} {N : ℕ} [(Ideal.span {π}).IsMaximal]

/-- Lifting along a surjection `p : X → Y` from a module satisfying `PowQuotientFlat π N`, for
`(π)` a maximal ideal and `s • X` killed by `π ^ N`: every linear map `g : M → Y` has a lift of
`s • g`. The lift is defined on the generators `v` of `exists_presentation` by `s • x i` with
`p (x i) = g (v i)`, and vanishes on the relations because their coefficients are divisible by
`π ^ N`. -/
theorem exists_lift_smul (hM : PowQuotientFlat π N M) (s : R) {X Y : Type*} [AddCommGroup X]
    [Module R X] [AddCommGroup Y] [Module R Y] (p : X →ₗ[R] Y) (hp : Function.Surjective p)
    (hX : ∀ x : X, π ^ N • s • x = 0) (g : M →ₗ[R] Y) :
    ∃ f : M →ₗ[R] X, ∀ y, p (f y) = s • g y := by
  obtain ⟨ι, v, hsurj, hrel⟩ := hM.exists_presentation
  choose x hx using fun i => hp (g (v i))
  let φ := Finsupp.linearCombination R v
  let F : (ι →₀ R) →ₗ[R] X := s • Finsupp.linearCombination R x
  have hF : LinearMap.ker φ ≤ LinearMap.ker F := by
    intro c hc
    obtain ⟨d, hd⟩ := exists_eq_smul_of_forall_dvd_finsupp c (hrel c hc)
    rw [LinearMap.mem_ker, hd, map_smul]
    change π ^ N • s • Finsupp.linearCombination R x d = 0
    exact hX _
  let f : M →ₗ[R] X := ((LinearMap.ker φ).liftQ F hF).comp
    (φ.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hf : ∀ c, f (φ c) = F c := fun c => by
    change (LinearMap.ker φ).liftQ F hF ((φ.quotKerEquivOfSurjective hsurj).symm (φ c)) = F c
    rw [show (φ.quotKerEquivOfSurjective hsurj).symm (φ c) = Submodule.Quotient.mk c from
      (LinearEquiv.symm_apply_eq _).2 (φ.quotKerEquivOfSurjective_apply_mk hsurj c).symm]
    rfl
  refine ⟨f, fun y => ?_⟩
  obtain ⟨c, rfl⟩ := hsurj y
  rw [hf]
  change p (s • Finsupp.linearCombination R x c) = s • g (Finsupp.linearCombination R v c)
  simp only [map_smul, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, hx]

end PowQuotientFlat

end Lift

namespace DivisibleSystem

section ModuleCat

variable {R : Type u} [CommRing R] {ℓ : ℕ} {ι : Type*} [Fintype ι] {ε π : ι → R} {e : ι → ℕ}

/-- For `IsFactorwiseUnitMulUniformizerPow ℓ ε π e`, the factor `ε i • T m` of the level `T m` of
an `ℓ`-divisible system of `R`-modules satisfies `PowQuotientFlat (π i) (e i * m)`. This is the
proof of `DivisibleSystem.powQuotientFlat_obj` carried out on the factor: for `x = ε i x` with
`π i ^ b x = 0`, `a + b = e i m`, `a > 0`, the axiom `flat a m` writes `j x = ℓ ^ a z` for the
inclusion `j : T m → T (a + m)`, so `j x = ε i ℓ ^ a z = π i ^ a w` with
`w = u ^ a π i ^ (e i a - a) ε i z`; then `ℓ ^ m w = 0`, so `w = j y` by `torsion_exact`, and
`π i ^ a (ε i y) = x` because `j` is injective. -/
theorem powQuotientFlat_factor (h : IsFactorwiseUnitMulUniformizerPow ℓ ε π e)
    (T : DivisibleSystem (ModuleCat.{v} R) ℓ) (m : ℕ) (i : ι) :
    PowQuotientFlat (π i) (e i * m) ↥(ε i • (⊤ : Submodule R (T.obj m))) := by
  obtain ⟨u, hu⟩ := h.exists_unit_pow i
  have hkill : ∀ (n : ℕ) (x : T.obj n), (ℓ : R) ^ n • x = 0 := fun n x => by
    rw [← moduleCat_powSMul_hom_apply, T.powSMul_eq_zero, ModuleCat.hom_zero,
      LinearMap.zero_apply]
  have hεε : ∀ {n : ℕ} (x : T.obj n), ε i • ε i • x = ε i • x := fun x => by
    rw [smul_smul, h.idem]
  have hfix : ∀ x : ↥(ε i • (⊤ : Submodule R (T.obj m))), ε i • (x : T.obj m) = x := by
    rintro ⟨x, hx⟩
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact hεε y
  refine ⟨fun x => Subtype.ext ?_, fun a b hab x hx => ?_⟩
  · change π i ^ (e i * m) • (x : T.obj m) = 0
    rw [← hfix x]
    exact h.pow_smul_smul_eq_zero i (hkill m) _
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨x, by rw [pow_zero, one_smul]⟩
  have he : 0 < e i := Nat.pos_of_ne_zero fun he => by rw [he, zero_mul] at hab; omega
  have hx' : π i ^ b • (x : T.obj m) = 0 := congrArg Subtype.val hx
  have hlt : m < a + m := by omega
  let ι' := (T.inclusion hlt).hom
  have hιx : (powSMul ℓ m (T.obj (a + m))).hom (ι' x) = 0 := by
    rw [moduleCat_powSMul_hom_apply, ← ι'.map_smul, hkill, map_zero]
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (T.flat a m) (ι' x) hιx
  change (powSMul ℓ a (T.obj (a + m))).hom z = ι' x at hz
  rw [moduleCat_powSMul_hom_apply] at hz
  obtain ⟨t, ht⟩ : ∃ t, e i * a = a + t :=
    ⟨e i * a - a, by have := Nat.le_mul_of_pos_left a he; omega⟩
  have hιfix : ε i • ι' x = ι' x := by rw [← ι'.map_smul, hfix x]
  let w := ((u : R) ^ a * π i ^ t * ε i) • z
  have hw : π i ^ a • w = ι' x := by
    rw [← hιfix, ← hz, smul_smul, smul_smul, mul_comm (ε i) ((ℓ : R) ^ a), hu, ht, pow_add]
    congr 1
    ring
  have hεw : ε i • w = w := by
    simp only [w, smul_smul]
    congr 1
    linear_combination ((u : R) ^ a * π i ^ t) * h.idem i
  have hw0 : (powSMul ℓ m (T.obj (a + m))).hom w = 0 := by
    rw [moduleCat_powSMul_hom_apply, ← hεw, smul_smul, hu, ← hab, pow_add, ← smul_smul,
      ← smul_smul, hεw, mul_comm (π i ^ a) (π i ^ b), mul_smul, hw, ← ι'.map_smul, hx',
      map_zero, smul_zero]
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 (T.torsion_exact hlt) w hw0
  change ι' y = w at hy
  refine ⟨⟨ε i • y, Submodule.smul_mem_pointwise_smul y (ε i) ⊤ trivial⟩, Subtype.ext ?_⟩
  apply (ModuleCat.mono_iff_injective (T.inclusion hlt)).1 inferInstance
  change ι' (π i ^ a • ε i • y) = ι' x
  rw [ι'.map_smul, ι'.map_smul, hy, hεw, hw]

/-- For `IsFactorwiseUnitMulUniformizerPow ℓ ε π e`, every level `T m` of an `ℓ`-divisible system
of `R`-modules is projective relative to modules killed by `ℓ ^ m`: on each factor `ε i • T m`,
`PowQuotientFlat.exists_lift_smul` lifts `ε i • g`, and the lifts composed with `x ↦ ε i • x` sum
to a lift of `g` because `∑ i, ε i = 1`. -/
theorem powTorsionProjective_obj_of_factorwise (h : IsFactorwiseUnitMulUniformizerPow ℓ ε π e)
    (T : DivisibleSystem (ModuleCat.{v} R) ℓ) (m : ℕ) : PowTorsionProjective ℓ m (T.obj m) := by
  intro X Y p hp hX g
  have hpsurj := (ModuleCat.epi_iff_surjective p).1 hp
  have hXk : ∀ x : X, (ℓ : R) ^ m • x = 0 := fun x => by
    rw [← moduleCat_powSMul_hom_apply, hX, ModuleCat.hom_zero, LinearMap.zero_apply]
  have key : ∀ i, ∃ f : T.obj m →ₗ[R] X, ∀ y, p.hom (f y) = ε i • g.hom y := by
    intro i
    have := h.isMaximal i
    let S := ε i • (⊤ : Submodule R (T.obj m))
    obtain ⟨f, hf⟩ := (T.powQuotientFlat_factor h m i).exists_lift_smul (ε i) p.hom hpsurj
      (fun x => h.pow_smul_smul_eq_zero i hXk x) (g.hom ∘ₗ S.subtype)
    let r : T.obj m →ₗ[R] S := (LinearMap.lsmul R (T.obj m) (ε i)).codRestrict S
      fun y => Submodule.smul_mem_pointwise_smul y (ε i) ⊤ trivial
    refine ⟨f ∘ₗ r, fun y => ?_⟩
    rw [LinearMap.comp_apply, hf]
    change ε i • g.hom (ε i • y) = ε i • g.hom y
    rw [map_smul, smul_smul, h.idem]
  choose f hf using key
  refine ⟨ModuleCat.ofHom (∑ i, f i), ?_⟩
  ext y
  change p.hom ((∑ i, f i) y) = g.hom y
  rw [LinearMap.sum_apply, map_sum]
  simp only [hf]
  rw [← Finset.sum_smul, h.sum_eq_one, one_smul]

/-- For `IsFactorwiseUnitMulUniformizerPow ℓ ε π e`, the factor `ε i • T m` of the level `T m` of
an `ℓ`-divisible system of `R`-modules is free over `R ⧸ (π i ^ (e i * m))`: it has a family of
generators `v` such that a linear combination of the `v j` vanishes exactly when all its
coefficients are divisible by `π i ^ (e i * m)`. -/
theorem exists_free_generators_factor (h : IsFactorwiseUnitMulUniformizerPow ℓ ε π e)
    (T : DivisibleSystem (ModuleCat.{v} R) ℓ) (m : ℕ) (i : ι) :
    ∃ (κ : Type v) (v : κ → ↥(ε i • (⊤ : Submodule R (T.obj m)))),
      Function.Surjective (Finsupp.linearCombination R v) ∧
        ∀ c : κ →₀ R, Finsupp.linearCombination R v c = 0 ↔ ∀ j, π i ^ (e i * m) ∣ c j :=
  haveI := h.isMaximal i
  (T.powQuotientFlat_factor h m i).exists_free_generators

end ModuleCat

section UnderlyingBelow

variable {k : Type u} [CommRing k] {Γ : Type v} [Group Γ] {ℓ : ℕ} {ι : Type*} [Fintype ι]
  {ε π : ι → k} {e : ι → ℕ}

/-- For `IsFactorwiseUnitMulUniformizerPow ℓ ε π e` in `k`, the hypothesis
`UnderlyingPowTorsionProjectiveBelow N K` holds for every `ℓ`-divisible system `K` of complexes
of representations and every `N`. -/
theorem underlyingPowTorsionProjectiveBelow_of_factorwise
    (h : IsFactorwiseUnitMulUniformizerPow ℓ ε π e) (N : ℕ)
    (K : DivisibleSystem (CochainComplex (Rep.{w} k Γ) ℕ) ℓ) :
    UnderlyingPowTorsionProjectiveBelow N K :=
  fun m q _ => ((K.degree q).map
    (forget₂ (Rep.{w} k Γ) (ModuleCat.{w} k))).powTorsionProjective_obj_of_factorwise h m

end UnderlyingBelow

end DivisibleSystem

section Harris

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Shimura.Coefficients

/-- A nonzero natural number `ℓ` is nonzero in the completed integer ring `CoefficientIntegers l`
of `L` at a finite place `l`. -/
lemma coefficientIntegers_natCast_ne_zero {L : Type u} [Field L] [NumberField L]
    (l : FinitePlace L) {ℓ : ℕ} (hℓ : ℓ ≠ 0) : (ℓ : CoefficientIntegers l) ≠ 0 := by
  let : CharZero (FiniteCompletion L l) := Algebra.charZero_of_charZero L (FiniteCompletion L l)
  intro h0
  have := congrArg (algebraMap (CoefficientIntegers l) (FiniteCompletion L l)) h0
  rw [map_natCast, map_zero] at this
  exact Nat.cast_ne_zero.2 hℓ this

variable (L : Type u) [Field L] [NumberField L] (p : FinitePlace ℚ)

open scoped Classical in
/-- Harris's coefficient ring `HarrisCoefficientIntegers L p`, the product of the completed
integer rings of `L` at the places above `p`, satisfies `IsFactorwiseUnitMulUniformizerPow ℓ` for
every nonzero natural number `ℓ`, with the idempotents of the factors and a uniformizer of every
factor. -/
theorem harrisCoefficientIntegers_isFactorwiseUnitMulUniformizerPow {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    ∃ (π : HarrisCoefficientIntegers L p) (e : FinitePlacesAbove L p → ℕ),
      IsFactorwiseUnitMulUniformizerPow ℓ
        (fun l => (Pi.single l 1 : HarrisCoefficientIntegers L p))
        (fun l => (Pi.mulSingle l (π l) : HarrisCoefficientIntegers L p)) e :=
  IsFactorwiseUnitMulUniformizerPow.exists_pi_of_isDiscreteValuationRing
    fun l => coefficientIntegers_natCast_ne_zero l.1 hℓ

namespace DivisibleSystem

variable (ℓ : ℕ) [NeZero ℓ]

/-- Every level `T m` of an `ℓ`-divisible system of modules over Harris's coefficient ring
`HarrisCoefficientIntegers L p` is projective relative to modules killed by `ℓ ^ m`, for every
nonzero natural number `ℓ`. -/
theorem powTorsionProjective_obj_harrisCoefficientIntegers
    (T : DivisibleSystem (ModuleCat.{v} (HarrisCoefficientIntegers L p)) ℓ) (m : ℕ) :
    PowTorsionProjective ℓ m (T.obj m) := by
  obtain ⟨π, e, h⟩ := harrisCoefficientIntegers_isFactorwiseUnitMulUniformizerPow L p
    (NeZero.ne ℓ)
  exact T.powTorsionProjective_obj_of_factorwise h m

/-- Over Harris's coefficient ring `HarrisCoefficientIntegers L p`, the hypothesis
`UnderlyingPowTorsionProjectiveBelow N K` holds for every `ℓ`-divisible system `K` of complexes
of representations and every `N`. -/
theorem underlyingPowTorsionProjectiveBelow_harrisCoefficientIntegers {Γ : Type v} [Group Γ]
    (N : ℕ) (K : DivisibleSystem (CochainComplex (Rep.{w} (HarrisCoefficientIntegers L p) Γ) ℕ) ℓ) :
    UnderlyingPowTorsionProjectiveBelow N K := by
  obtain ⟨π, e, h⟩ := harrisCoefficientIntegers_isFactorwiseUnitMulUniformizerPow L p
    (NeZero.ne ℓ)
  exact underlyingPowTorsionProjectiveBelow_of_factorwise h N K

section SmoothGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {X : Type u}
  [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X] [HasStableNeighbourhoods G X]
  (h : SmoothGodementZeroExactStatement (HarrisCoefficientIntegers L p) G X)
  (T : SmoothSheafDivisibleSystem (HarrisCoefficientIntegers L p) G X ℓ)
  (D : ℕ) (H : Subgroup G) [H.Normal] [H.FiniteIndex]
  (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections (HarrisCoefficientIntegers L p) G X ⋙
      smoothQuotientInvariants (HarrisCoefficientIntegers L p) H).map
        ((smoothGodementTermSystem h T q).projection hm)))
  (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections (HarrisCoefficientIntegers L p) G X ⋙
      smoothQuotientInvariants (HarrisCoefficientIntegers L p) H).map
        ((smoothGodementResidualSystem h T (D + 1)).projection hm)))

/-- Over Harris's coefficient ring `HarrisCoefficientIntegers L p`, Harris's `C_m^{•,H}` for the
truncated smooth Godement resolutions (`smoothGodementInvariantTotalSystem`) satisfies
`TermwisePowTorsionProjective`. -/
lemma termwisePowTorsionProjective_smoothGodementInvariantTotalSystem_harrisCoefficientIntegers :
    TermwisePowTorsionProjective (smoothGodementInvariantTotalSystem h T D H hterm hres) :=
  termwisePowTorsionProjective_smoothGodementInvariantTotalSystem h T D H hterm hres
    (underlyingPowTorsionProjectiveBelow_harrisCoefficientIntegers L p ℓ _ _)

variable (W : DivisibleSystem (Rep.{u} (HarrisCoefficientIntegers L p) (G ⧸ H)) ℓ)

/-- Harris 1999, p.312, (4.10.3), over Harris's coefficient ring `HarrisCoefficientIntegers L p`,
for `T_m(j) = Hom(C_m^{j,H}, W_m)` with `C_m^{•,H}` the complexes
`smoothGodementInvariantTotalSystem`: the transitions of the inverse system of the `T_m(j)` are
surjective. -/
lemma
    smoothGodementInvariantTotalSystem_degree_homSystem_map_surjective_harrisCoefficientIntegers
    (j : ℤ) {m m' : ℕᵒᵖ} (φ : m ⟶ m') :
    Function.Surjective
      ((homSystem (HarrisCoefficientIntegers L p)
        ((smoothGodementInvariantTotalSystem h T D H hterm hres).degree j) W).map φ) :=
  smoothGodementInvariantTotalSystem_degree_homSystem_map_surjective h T D H hterm hres
    (underlyingPowTorsionProjectiveBelow_harrisCoefficientIntegers L p ℓ _ _) W j φ

/-- Over Harris's coefficient ring `HarrisCoefficientIntegers L p`, the inverse system of the
`T_m(j) = Hom(C_m^{j,H}, W_m)`, `C_m^{•,H}` the complexes `smoothGodementInvariantTotalSystem`,
satisfies the Mittag-Leffler condition. -/
lemma
    isMittagLeffler_smoothGodementInvariantTotalSystem_degree_homSystem_harrisCoefficientIntegers
    (j : ℤ) :
    (homSystem (HarrisCoefficientIntegers L p)
      ((smoothGodementInvariantTotalSystem h T D H hterm hres).degree j) W ⋙
        CategoryTheory.forget (ModuleCat.{u} (HarrisCoefficientIntegers L p))).IsMittagLeffler :=
  isMittagLeffler_smoothGodementInvariantTotalSystem_degree_homSystem h T D H hterm hres
    (underlyingPowTorsionProjectiveBelow_harrisCoefficientIntegers L p ℓ _ _) W j

variable
    (W : DivisibleSystem (CochainComplex (Rep.{u} (HarrisCoefficientIntegers L p) (G ⧸ H)) ℤ) ℓ)

/-- Over Harris's coefficient ring `HarrisCoefficientIntegers L p`, the inverse system of Hom
complexes `Hom^•(C_m^{•,H}, W_m)`, `C_m^{•,H}` the complexes
`smoothGodementInvariantTotalSystem`, satisfies the Mittag-Leffler condition in every degree. -/
lemma
    isMittagLeffler_smoothGodementInvariantTotalSystem_homComplexSystem_eval_harrisCoefficientIntegers
    (n : ℤ) :
    (homComplexSystem (HarrisCoefficientIntegers L p)
      (smoothGodementInvariantTotalSystem h T D H hterm hres) W ⋙
        HomologicalComplex.eval (ModuleCat.{u} (HarrisCoefficientIntegers L p))
          (ComplexShape.up ℤ) n ⋙
            CategoryTheory.forget
              (ModuleCat.{u} (HarrisCoefficientIntegers L p))).IsMittagLeffler :=
  isMittagLeffler_smoothGodementInvariantTotalSystem_homComplexSystem_eval h T D H hterm hres
    (underlyingPowTorsionProjectiveBelow_harrisCoefficientIntegers L p ℓ _ _) W n

end SmoothGodement

section ProPSmoothGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {X : Type u}
  [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X] [HasStableNeighbourhoods G X]
  (h : SmoothGodementZeroExactStatement (HarrisCoefficientIntegers L p) G X)
  (T : SmoothSheafDivisibleSystem (HarrisCoefficientIntegers L p) G X ℓ)
  (D : ℕ) (hP : ProPInvariantsExactStatement.{u, u, u}) {q : ℕ} {H : Subgroup G} [H.Normal]
  [H.FiniteIndex] (hH : IsProPSubgroup q H) (hR : IsUnit (q : HarrisCoefficientIntegers L p))
  (hterm : ∀ j ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections (HarrisCoefficientIntegers L p) G X).map
      ((smoothGodementTermSystem h T j).projection hm)))
  (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections (HarrisCoefficientIntegers L p) G X).map
      ((smoothGodementResidualSystem h T (D + 1)).projection hm)))

/-- Over Harris's coefficient ring `HarrisCoefficientIntegers L p`, Harris's `C_m^{•,H}` for the
truncated smooth Godement resolutions and a normal pro-`q` subgroup `H` of finite index, `q` a
unit in the coefficients (`proPSmoothGodementInvariantTotalSystem`), satisfies
`TermwisePowTorsionProjective`. -/
lemma
    termwisePowTorsionProjective_proPSmoothGodementInvariantTotalSystem_harrisCoefficientIntegers :
    TermwisePowTorsionProjective
      (proPSmoothGodementInvariantTotalSystem h T D hP hH hR hterm hres) :=
  termwisePowTorsionProjective_proPSmoothGodementInvariantTotalSystem h T D hP hH hR hterm hres
    (underlyingPowTorsionProjectiveBelow_harrisCoefficientIntegers L p ℓ _ _)

variable (W : DivisibleSystem (Rep.{u} (HarrisCoefficientIntegers L p) (G ⧸ H)) ℓ)

/-- Harris 1999, p.312, (4.10.3), over Harris's coefficient ring `HarrisCoefficientIntegers L p`,
for `T_m(j) = Hom(C_m^{j,H}, W_m)` with `C_m^{•,H}` the complexes
`proPSmoothGodementInvariantTotalSystem`: the transitions of the inverse system of the `T_m(j)`
are surjective. -/
lemma
    proPSmoothGodementInvariantTotalSystem_degree_homSystem_map_surjective_harrisCoefficientIntegers
    (j : ℤ) {m m' : ℕᵒᵖ} (φ : m ⟶ m') :
    Function.Surjective
      ((homSystem (HarrisCoefficientIntegers L p)
        ((proPSmoothGodementInvariantTotalSystem h T D hP hH hR hterm hres).degree j) W).map φ) :=
  proPSmoothGodementInvariantTotalSystem_degree_homSystem_map_surjective h T D hP hH hR hterm hres
    (underlyingPowTorsionProjectiveBelow_harrisCoefficientIntegers L p ℓ _ _) W j φ

/-- Over Harris's coefficient ring `HarrisCoefficientIntegers L p`, the inverse system of the
`T_m(j) = Hom(C_m^{j,H}, W_m)`, `C_m^{•,H}` the complexes
`proPSmoothGodementInvariantTotalSystem`, satisfies the Mittag-Leffler condition. -/
lemma
    isMittagLeffler_proPSmoothGodementInvariantTotalSystem_degree_homSystem_harrisCoefficientIntegers
    (j : ℤ) :
    (homSystem (HarrisCoefficientIntegers L p)
      ((proPSmoothGodementInvariantTotalSystem h T D hP hH hR hterm hres).degree j) W ⋙
        CategoryTheory.forget (ModuleCat.{u} (HarrisCoefficientIntegers L p))).IsMittagLeffler :=
  isMittagLeffler_proPSmoothGodementInvariantTotalSystem_degree_homSystem h T D hP hH hR hterm
    hres (underlyingPowTorsionProjectiveBelow_harrisCoefficientIntegers L p ℓ _ _) W j

variable
    (W : DivisibleSystem (CochainComplex (Rep.{u} (HarrisCoefficientIntegers L p) (G ⧸ H)) ℤ) ℓ)

/-- Over Harris's coefficient ring `HarrisCoefficientIntegers L p`, the inverse system of Hom
complexes `Hom^•(C_m^{•,H}, W_m)`, `C_m^{•,H}` the complexes
`proPSmoothGodementInvariantTotalSystem`, satisfies the Mittag-Leffler condition in every
degree. -/
lemma
    isMittagLeffler_proPSmoothGodementInvariantTotalSystem_homComplexSystem_eval_harrisCoefficientIntegers
    (n : ℤ) :
    (homComplexSystem (HarrisCoefficientIntegers L p)
      (proPSmoothGodementInvariantTotalSystem h T D hP hH hR hterm hres) W ⋙
        HomologicalComplex.eval (ModuleCat.{u} (HarrisCoefficientIntegers L p))
          (ComplexShape.up ℤ) n ⋙
            CategoryTheory.forget
              (ModuleCat.{u} (HarrisCoefficientIntegers L p))).IsMittagLeffler :=
  isMittagLeffler_proPSmoothGodementInvariantTotalSystem_homComplexSystem_eval h T D hP hH hR
    hterm hres (underlyingPowTorsionProjectiveBelow_harrisCoefficientIntegers L p ℓ _ _) W n

end ProPSmoothGodement

end DivisibleSystem

end Harris

end Langlands.Cohomology
