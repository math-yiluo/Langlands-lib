import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Int
import Langlands.Cohomology.DivisibleSystem.InvariantTotalProjective

/-!
# The levels of an `ℓ`-divisible system of modules are free over `R ⧸ (ℓ ^ m)`

Harris 1999, p.304, calls a collection `{T_m}` of sheaves of `ℤ/ℓ^mℤ[S(ẽ)]`-modules an
`ℓ`-divisible system when "`T_m` is free over `ℤ/ℓ^mℤ`, `i` identifies `T_{m'}` with the
`p^{m'}`-torsion in `T_m`, and (2.1) `0 → T_{m'} → T_m → T_{m-m'} → 0` is exact" (the printed
`p^{m'}` must be read as `ℓ^{m'}`, since `T_m` is a `ℤ/ℓ^mℤ`-module). The Library's
`DivisibleSystem` renders the freeness by the axiom `flat`: the kernel of `ℓ ^ b` on `T (a + b)`
is the image of `ℓ ^ a`. This module shows that, for modules over a commutative ring `R` in which
`ℓ = u π ^ e` with `u` a unit, `e ≥ 1` and `(π)` a maximal ideal (`IsUnitMulUniformizerPow`; for
instance `ℤ` or `ℤ_[p]` with `π = ℓ = p`, or a discrete valuation ring with a uniformizer `π` in
which `ℓ` is nonzero and not a unit),
the axioms imply Harris's freeness, and it removes the hypothesis
`UnderlyingPowTorsionProjectiveBelow` from the results of the module `InvariantTotalProjective`:

* `PowQuotientFlat π N M`: `M` is killed by `π ^ N`, and the kernel of `π ^ b` is the image of
  `π ^ a` whenever `a + b = N`;
* `PowQuotientFlat.exists_presentation` and `PowQuotientFlat.exists_free_generators`: for `(π)`
  maximal, lifts `v` of a basis of `M ⧸ π M` over the field `R ⧸ (π)` generate `M`, and a linear
  combination of the `v i` vanishes exactly when all its coefficients are divisible by `π ^ N`;
* `PowQuotientFlat.powTorsionProjective`: such an `M` is projective relative to modules killed
  by `ℓ ^ m` (`PowTorsionProjective ℓ m`) whenever `ℓ ^ m` divides `π ^ N`;
* `IsUnitMulUniformizerPow ℓ π e`, with `IsUnitMulUniformizerPow.int`, `.padicInt` and
  `.exists_of_isDiscreteValuationRing`;
* `DivisibleSystem.powQuotientFlat_obj`: the level `T m` of an `ℓ`-divisible system of
  `R`-modules satisfies `PowQuotientFlat π (e * m)`; hence
  `DivisibleSystem.exists_free_generators_obj` (Harris's "`T_m` is free over `ℤ/ℓ^mℤ`", with
  `R ⧸ (ℓ ^ m)` in place of `ℤ/ℓ^mℤ`) and `DivisibleSystem.powTorsionProjective_obj`;
* `DivisibleSystem.underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow`: for every
  `ℓ`-divisible system `K` of complexes of representations, the underlying modules of the terms
  form `ℓ`-divisible systems of modules, so `UnderlyingPowTorsionProjectiveBelow N K` holds;
* for the total complexes `groupStandardTotalSystem` and Harris's complexes `C_m^{•,H}`
  (`quotientInvariantsTotalSystem`, `smoothGodementInvariantTotalSystem`,
  `proPSmoothGodementInvariantTotalSystem`), the forms `..._of_isUnitMulUniformizerPow` of
  `TermwisePowTorsionProjective`, of the surjectivity of the transitions of
  `T_m(j) = Hom(C_m^j, W_m)` (Harris 1999, p.312, (4.10.3)), of the Mittag-Leffler condition of
  the `T_m(j)`, and of the Mittag-Leffler condition of the Hom complexes `Hom^•(C_m^•, W_m)`.

Harris takes the freeness as part of the definition; here it is derived from the exactness
axioms. The relative projectivity of `PowQuotientFlat.powTorsionProjective` is proved directly
from the presentation, by lifting a morphism on the generators `v i`, not through freeness and
the projectivity of free modules. The hypotheses of the `H`-invariant systems that the
transitions stay epimorphisms on `H`-invariants (`hK`, `hterm`, `hres`) stay explicit.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

open scoped Pointwise

universe w v u uR uG

section Presentation

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- `M` is killed by `π ^ N`, and the kernel of multiplication by `π ^ b` on `M` is the image of
multiplication by `π ^ a` whenever `a + b = N`. -/
structure PowQuotientFlat (π : R) (N : ℕ) (M : Type v) [AddCommGroup M] [Module R M] : Prop where
  smul_eq_zero : ∀ x : M, π ^ N • x = 0
  exists_smul_eq : ∀ a b : ℕ, a + b = N → ∀ x : M, π ^ b • x = 0 → ∃ y : M, π ^ a • y = x

/-- A finitely supported family of elements of `R` all divisible by `r` is `r` times a finitely
supported family. -/
lemma exists_eq_smul_of_forall_dvd_finsupp {ι : Type*} {r : R} (d : ι →₀ R)
    (h : ∀ i, r ∣ d i) : ∃ d' : ι →₀ R, d = r • d' := by
  classical
  choose f hf using h
  refine ⟨d.sum fun i _ => Finsupp.single i (f i), ?_⟩
  rw [Finsupp.smul_sum]
  conv_lhs => rw [← Finsupp.sum_single d]
  refine Finset.sum_congr rfl fun i _ => ?_
  show Finsupp.single i (d i) = r • Finsupp.single i (f i)
  rw [Finsupp.smul_single, smul_eq_mul, ← hf i]

/-- If the reductions modulo `π` of the `v i` span `M ⧸ π M`, every element of `M` is a linear
combination of the `v i` up to an element of `π ^ j M`. -/
lemma exists_eq_linearCombination_add_pow_smul {π : R} {ι : Type*} (v : ι → M)
    (hv : ∀ x : M, ∃ c : ι →₀ R, ∃ z : M, x = Finsupp.linearCombination R v c + π • z)
    (j : ℕ) (x : M) :
    ∃ (c : ι →₀ R) (z : M), x = Finsupp.linearCombination R v c + π ^ j • z := by
  induction j generalizing x with
  | zero => exact ⟨0, x, by simp⟩
  | succ j ih =>
    obtain ⟨c, z, rfl⟩ := ih x
    obtain ⟨c', z', rfl⟩ := hv z
    refine ⟨c + π ^ j • c', z', ?_⟩
    rw [map_add, map_smul, smul_add, add_assoc, pow_succ, mul_smul]

namespace PowQuotientFlat

variable {π : R} {N : ℕ}

/-- If the reductions modulo `π` of the `v i` are linearly independent over `R ⧸ (π)`, the
coefficients of every linear relation among the `v i` in an `R`-module satisfying
`PowQuotientFlat π N` are divisible by `π ^ N`. -/
lemma pow_dvd_of_linearCombination_eq_zero (hM : PowQuotientFlat π N M) {ι : Type*}
    (v : ι → M)
    (hv : ∀ (d : ι →₀ R) (y : M), Finsupp.linearCombination R v d = π • y → ∀ i, π ∣ d i)
    {c : ι →₀ R} (hc : Finsupp.linearCombination R v c = 0) (i : ι) : π ^ N ∣ c i := by
  have key : ∀ j ≤ N, ∃ d : ι →₀ R, c = π ^ j • d := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨c, by simp⟩
    | succ j ih =>
      intro hj
      obtain ⟨d, rfl⟩ := ih (by omega)
      rw [map_smul] at hc
      obtain ⟨y, hy⟩ := hM.exists_smul_eq (N - j) j (by omega) _ hc
      obtain ⟨d', rfl⟩ := exists_eq_smul_of_forall_dvd_finsupp d
        (hv d (π ^ (N - j - 1) • y) (by
          rw [← hy, smul_smul, ← pow_succ', Nat.sub_add_cancel (by omega)]))
      exact ⟨d', by rw [smul_smul, ← pow_succ]⟩
  obtain ⟨d, rfl⟩ := key N le_rfl
  exact ⟨d i, by simp⟩

variable [hπ : (Ideal.span {π}).IsMaximal]

/-- A module satisfying `PowQuotientFlat π N`, for `(π)` a maximal ideal, has a family of
generators `v` whose relations have all their coefficients divisible by `π ^ N`: lifts of a basis
of `M ⧸ π M` over the field `R ⧸ (π)`. -/
theorem exists_presentation (hM : PowQuotientFlat π N M) :
    ∃ (ι : Type v) (v : ι → M), Function.Surjective (Finsupp.linearCombination R v) ∧
      ∀ c : ι →₀ R, Finsupp.linearCombination R v c = 0 → ∀ i, π ^ N ∣ c i := by
  classical
  let _ : Field (R ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  let P : Submodule R M := π • (⊤ : Submodule R M)
  let ι := Module.Basis.ofVectorSpaceIndex (R ⧸ Ideal.span {π}) (M ⧸ P)
  let b : Module.Basis ι (R ⧸ Ideal.span {π}) (M ⧸ P) :=
    Module.Basis.ofVectorSpace (R ⧸ Ideal.span {π}) (M ⧸ P)
  choose v hv using fun i => Submodule.Quotient.mk_surjective P (b i)
  have hmk : ∀ c, Submodule.Quotient.mk (p := P) (Finsupp.linearCombination R v c) =
      c.sum fun i a => Ideal.Quotient.mk (Ideal.span {π}) a • b i := by
    intro c
    rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum]
    change P.mkQ _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change Submodule.Quotient.mk (c i • v i) = _
    rw [Submodule.Quotient.mk_smul, hv i]
    rfl
  have hmemP : ∀ x : M, x ∈ P ↔ ∃ y : M, x = π • y := by
    intro x
    rw [Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨y, _, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, trivial, hy.symm⟩⟩
  have hspan : ∀ x : M, ∃ c : ι →₀ R, ∃ z : M, x = Finsupp.linearCombination R v c + π • z := by
    intro x
    obtain ⟨c, hc⟩ := Finsupp.mapRange_surjective (Ideal.Quotient.mk (Ideal.span {π}))
      (map_zero _) Ideal.Quotient.mk_surjective (b.repr (Submodule.Quotient.mk x))
    have h1 : Submodule.Quotient.mk (p := P) (x - Finsupp.linearCombination R v c) = 0 := by
      rw [Submodule.Quotient.mk_sub, hmk, ← b.linearCombination_repr (Submodule.Quotient.mk x),
        ← hc, Finsupp.linearCombination_apply,
        Finsupp.sum_mapRange_index (h := fun i a => a • b i) (fun i => zero_smul _ (b i)), sub_self]
    obtain ⟨z, hz⟩ := (hmemP _).1 ((Submodule.Quotient.mk_eq_zero P).1 h1)
    exact ⟨c, z, sub_eq_iff_eq_add'.1 hz⟩
  have hind : ∀ (d : ι →₀ R) (y : M), Finsupp.linearCombination R v d = π • y →
      ∀ i, π ∣ d i := by
    intro d y hdy i
    have h1 : (Finsupp.mapRange (Ideal.Quotient.mk (Ideal.span {π})) (map_zero _) d).sum
        (fun i a => a • b i) = 0 := by
      rw [Finsupp.sum_mapRange_index (h := fun i a => a • b i) (fun i => zero_smul _ (b i)),
        ← hmk, hdy, Submodule.Quotient.mk_eq_zero]
      exact (hmemP _).2 ⟨y, rfl⟩
    have h2 : Finsupp.mapRange (Ideal.Quotient.mk (Ideal.span {π})) (map_zero _) d = 0 := by
      rw [← b.repr_linearCombination (Finsupp.mapRange _ _ d), Finsupp.linearCombination_apply,
        h1, map_zero]
    have h3 := congrArg (fun e => e i) h2
    simp only [Finsupp.mapRange_apply, Finsupp.coe_zero, Pi.zero_apply] at h3
    exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h3)
  refine ⟨_, v, fun x => ?_, fun c hc i => hM.pow_dvd_of_linearCombination_eq_zero v hind hc i⟩
  obtain ⟨c, z, hz⟩ := exists_eq_linearCombination_add_pow_smul v hspan N x
  exact ⟨c, by rw [hz, hM.smul_eq_zero, add_zero]⟩

/-- A module satisfying `PowQuotientFlat π N`, for `(π)` a maximal ideal, is free over
`R ⧸ (π ^ N)`: it has a family of generators `v` such that a linear combination of the `v i`
vanishes exactly when all its coefficients are divisible by `π ^ N`. -/
theorem exists_free_generators (hM : PowQuotientFlat π N M) :
    ∃ (ι : Type v) (v : ι → M), Function.Surjective (Finsupp.linearCombination R v) ∧
      ∀ c : ι →₀ R, Finsupp.linearCombination R v c = 0 ↔ ∀ i, π ^ N ∣ c i := by
  obtain ⟨ι, v, hsurj, hrel⟩ := hM.exists_presentation
  refine ⟨ι, v, hsurj, fun c => ⟨hrel c, fun hc => ?_⟩⟩
  obtain ⟨d, rfl⟩ := exists_eq_smul_of_forall_dvd_finsupp c hc
  rw [map_smul, hM.smul_eq_zero]

end PowQuotientFlat

end Presentation

section ModuleCat

variable {R : Type u} [CommRing R]

/-- Multiplication by `ℓ ^ m` on an `R`-module is the scalar multiplication by `(ℓ : R) ^ m`. -/
lemma moduleCat_powSMul_hom_apply (ℓ m : ℕ) (L : ModuleCat.{v} R) (x : L) :
    (powSMul ℓ m L).hom x = ((ℓ : R) ^ m) • x := by
  rw [powSMul, ModuleCat.hom_nsmul, LinearMap.smul_apply, ModuleCat.hom_id, LinearMap.id_apply,
    ← Nat.cast_smul_eq_nsmul R, Nat.cast_pow]

namespace PowQuotientFlat

variable {π : R} {N : ℕ} [(Ideal.span {π}).IsMaximal]

/-- An `R`-module satisfying `PowQuotientFlat π N`, for `(π)` a maximal ideal, is projective
relative to modules killed by `ℓ ^ m` whenever `ℓ ^ m` divides `π ^ N`: a morphism to the target
of a surjection from such a module is lifted on the generators of `exists_presentation`, and the
lift vanishes on the relations because their coefficients are divisible by `π ^ N`. -/
theorem powTorsionProjective {M : ModuleCat.{v} R} (hM : PowQuotientFlat π N M) {ℓ m : ℕ}
    (hπℓ : (ℓ : R) ^ m ∣ π ^ N) : DivisibleSystem.PowTorsionProjective ℓ m M := by
  intro X Y p hp hX g
  obtain ⟨ι, v, hsurj, hrel⟩ := hM.exists_presentation
  have hpsurj := (ModuleCat.epi_iff_surjective p).1 hp
  choose x hx using fun i => hpsurj (g.hom (v i))
  obtain ⟨r, hr⟩ := hπℓ
  have hXπ : ∀ y : X, π ^ N • y = 0 := fun y => by
    rw [hr, mul_comm ((ℓ : R) ^ m) r, mul_smul, ← moduleCat_powSMul_hom_apply, hX,
      ModuleCat.hom_zero, LinearMap.zero_apply, smul_zero]
  let φ := Finsupp.linearCombination R v
  let F := Finsupp.linearCombination R x
  have hF : LinearMap.ker φ ≤ LinearMap.ker F := by
    intro c hc
    obtain ⟨d, hd⟩ := exists_eq_smul_of_forall_dvd_finsupp c (hrel c hc)
    rw [LinearMap.mem_ker, hd, map_smul, hXπ]
  let f : M →ₗ[R] X := ((LinearMap.ker φ).liftQ F hF).comp
    (φ.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hf : ∀ c, f (φ c) = F c := fun c => by
    change (LinearMap.ker φ).liftQ F hF ((φ.quotKerEquivOfSurjective hsurj).symm (φ c)) = F c
    rw [show (φ.quotKerEquivOfSurjective hsurj).symm (φ c) = Submodule.Quotient.mk c from
      (LinearEquiv.symm_apply_eq _).2 (φ.quotKerEquivOfSurjective_apply_mk hsurj c).symm]
    rfl
  refine ⟨ModuleCat.ofHom f, ?_⟩
  ext y
  obtain ⟨c, rfl⟩ := hsurj y
  change p.hom (f (φ c)) = g.hom (φ c)
  rw [hf]
  simp only [F, φ, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hx]

end PowQuotientFlat

/-- `ℓ = u π ^ e` in `R` for a unit `u` and an exponent `e ≥ 1`, where `π` generates a maximal
ideal: `π` is a uniformizer at `ℓ` and `e` the ramification index of `ℓ`. -/
structure IsUnitMulUniformizerPow (ℓ : ℕ) (π : R) (e : ℕ) : Prop where
  isMaximal : (Ideal.span {π}).IsMaximal
  pos : 0 < e
  exists_unit : ∃ u : Rˣ, (ℓ : R) = u * π ^ e

namespace IsUnitMulUniformizerPow

variable {ℓ : ℕ} {π : R} {e : ℕ}

/-- `ℓ ^ m` divides `π ^ (e * m)`. -/
lemma pow_dvd (h : IsUnitMulUniformizerPow ℓ π e) (m : ℕ) : (ℓ : R) ^ m ∣ π ^ (e * m) := by
  obtain ⟨u, hℓ⟩ := h.exists_unit
  refine ⟨((u⁻¹ : Rˣ) : R) ^ m, ?_⟩
  have hu : ((u⁻¹ : Rˣ) : R) ^ m * (u : R) ^ m = 1 := by
    rw [← mul_pow, Units.inv_mul, one_pow]
  rw [hℓ, mul_pow, ← pow_mul]
  linear_combination (-π ^ (e * m)) * hu

/-- `ℓ` itself, when it generates a maximal ideal, with ramification index `1`. -/
lemma natCast (h : (Ideal.span {(ℓ : R)}).IsMaximal) :
    IsUnitMulUniformizerPow ℓ (ℓ : R) 1 :=
  ⟨h, one_pos, 1, by rw [Units.val_one, one_mul, pow_one]⟩

/-- A prime `p` in `ℤ`, with ramification index `1`. -/
lemma int (p : ℕ) [Fact p.Prime] : IsUnitMulUniformizerPow p (p : ℤ) 1 :=
  natCast inferInstance

/-- The prime `p` in the `p`-adic integers `ℤ_[p]`, with ramification index `1`. -/
lemma padicInt (p : ℕ) [Fact p.Prime] : IsUnitMulUniformizerPow p (p : ℤ_[p]) 1 :=
  natCast (PadicInt.maximalIdeal_eq_span_p (p := p) ▸ IsLocalRing.maximalIdeal.isMaximal ℤ_[p])

/-- In a discrete valuation ring, a nonzero nonunit `ℓ` is a unit times a power `ϖ ^ e`, `e ≥ 1`,
of any uniformizer `ϖ`. -/
lemma exists_of_isDiscreteValuationRing [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
    (hϖ : Irreducible ϖ) (hℓ : (ℓ : R) ≠ 0) (hℓu : ¬IsUnit (ℓ : R)) :
    ∃ e, IsUnitMulUniformizerPow ℓ ϖ e := by
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hℓ hϖ
  refine ⟨n, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ ▸
    IsLocalRing.maximalIdeal.isMaximal R, Nat.pos_of_ne_zero fun hn0 => hℓu ?_, u, hn⟩
  rw [hn, hn0, pow_zero, mul_one]
  exact u.isUnit

end IsUnitMulUniformizerPow

namespace DivisibleSystem

variable {ℓ : ℕ} {π : R} {e : ℕ}

/-- If `ℓ = u π ^ e` (`IsUnitMulUniformizerPow`), the level `T m` of an `ℓ`-divisible system of
`R`-modules satisfies `PowQuotientFlat π (e * m)`. For `x` with `π ^ b x = 0`, `a + b = e m`,
`a > 0`: the axiom `flat a m` writes `i x = ℓ ^ a z` in `T (a + m)`, so `i x = π ^ a w` with
`w = u ^ a π ^ (e a - a) z`; then `ℓ ^ m w = u ^ m π ^ b i x = 0`, so `w = i y` by
`torsion_exact`, and `π ^ a y = x` because `i` is injective. -/
theorem powQuotientFlat_obj (h : IsUnitMulUniformizerPow ℓ π e)
    (T : DivisibleSystem (ModuleCat.{v} R) ℓ) (m : ℕ) : PowQuotientFlat π (e * m) (T.obj m) := by
  obtain ⟨u, hℓ⟩ := h.exists_unit
  have hkill : ∀ (n : ℕ) (x : T.obj n), (ℓ : R) ^ n • x = 0 := fun n x => by
    rw [← moduleCat_powSMul_hom_apply, T.powSMul_eq_zero, ModuleCat.hom_zero,
      LinearMap.zero_apply]
  have hℓpow : ∀ n : ℕ, (ℓ : R) ^ n = (u : R) ^ n * π ^ (e * n) := fun n => by
    rw [hℓ, mul_pow, ← pow_mul]
  refine ⟨fun x => ?_, fun a b hab x hx => ?_⟩
  · obtain ⟨r, hr⟩ := h.pow_dvd m
    rw [hr, mul_comm ((ℓ : R) ^ m) r, mul_smul, hkill, smul_zero]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨x, by rw [pow_zero, one_smul]⟩
  have hlt : m < a + m := by omega
  let ι := (T.inclusion hlt).hom
  have hιx : (powSMul ℓ m (T.obj (a + m))).hom (ι x) = 0 := by
    rw [moduleCat_powSMul_hom_apply, ← ι.map_smul, hkill, map_zero]
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 (T.flat a m) (ι x) hιx
  change (powSMul ℓ a (T.obj (a + m))).hom z = ι x at hz
  rw [moduleCat_powSMul_hom_apply] at hz
  obtain ⟨t, ht⟩ : ∃ t, e * a = a + t :=
    ⟨e * a - a, by have := Nat.le_mul_of_pos_left a h.pos; omega⟩
  let w := ((u : R) ^ a * π ^ t) • z
  have hw : π ^ a • w = ι x := by
    rw [← hz, hℓpow, ht, pow_add, smul_smul]
    congr 1
    ring
  have hw0 : (powSMul ℓ m (T.obj (a + m))).hom w = 0 := by
    rw [moduleCat_powSMul_hom_apply, hℓpow, ← hab, pow_add, mul_comm (π ^ a) (π ^ b),
      ← mul_assoc, mul_smul, hw, ← ι.map_smul, mul_smul, hx, smul_zero, map_zero]
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 (T.torsion_exact hlt) w hw0
  change ι y = w at hy
  refine ⟨y, (ModuleCat.mono_iff_injective (T.inclusion hlt)).1 inferInstance ?_⟩
  change ι (π ^ a • y) = ι x
  rw [ι.map_smul, hy, hw]

/-- If `ℓ = u π ^ e` (`IsUnitMulUniformizerPow`), every level `T m` of an `ℓ`-divisible system
of `R`-modules is projective relative to modules killed by `ℓ ^ m`. -/
theorem powTorsionProjective_obj (h : IsUnitMulUniformizerPow ℓ π e)
    (T : DivisibleSystem (ModuleCat.{v} R) ℓ) (m : ℕ) : PowTorsionProjective ℓ m (T.obj m) :=
  haveI := h.isMaximal
  (T.powQuotientFlat_obj h m).powTorsionProjective (h.pow_dvd m)

/-- Harris 1999, p.304, "`T_m` is free over `ℤ/ℓ^mℤ`", for an `ℓ`-divisible system of
`R`-modules when `ℓ = u π ^ e` (`IsUnitMulUniformizerPow`): the level `T m` has a family of
generators `v` such that a linear combination of the `v i` vanishes exactly when all its
coefficients are divisible by `ℓ ^ m`, so `T m` is free over `R ⧸ (ℓ ^ m)`. -/
theorem exists_free_generators_obj (h : IsUnitMulUniformizerPow ℓ π e)
    (T : DivisibleSystem (ModuleCat.{v} R) ℓ) (m : ℕ) :
    ∃ (ι : Type v) (v : ι → T.obj m), Function.Surjective (Finsupp.linearCombination R v) ∧
      ∀ c : ι →₀ R, Finsupp.linearCombination R v c = 0 ↔ ∀ i, (ℓ : R) ^ m ∣ c i := by
  have := h.isMaximal
  obtain ⟨ι, v, hsurj, hrel⟩ := (T.powQuotientFlat_obj h m).exists_free_generators
  obtain ⟨u, hℓ⟩ := h.exists_unit
  have hdvd : ∀ r : R, (ℓ : R) ^ m ∣ r ↔ π ^ (e * m) ∣ r := fun r =>
    ⟨(Dvd.intro_left _ (by rw [hℓ, mul_pow, ← pow_mul])).trans, (h.pow_dvd m).trans⟩
  exact ⟨ι, v, hsurj, fun c => (hrel c).trans (forall_congr' fun i => (hdvd (c i)).symm)⟩

end DivisibleSystem

end ModuleCat

namespace DivisibleSystem

section UnderlyingBelow

variable {k : Type u} [CommRing k] {Γ : Type v} [Group Γ] {ℓ : ℕ} {π : k} {e : ℕ}

/-- If `ℓ = u π ^ e` in `k` (`IsUnitMulUniformizerPow`), the hypothesis
`UnderlyingPowTorsionProjectiveBelow N K` holds for every `ℓ`-divisible system `K` of complexes
of representations and every `N`: the underlying modules of the degree-`q` terms form the
`ℓ`-divisible system `(K.degree q).map (forget₂ _ _)` of `k`-modules. -/
theorem underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow
    (h : IsUnitMulUniformizerPow ℓ π e) (N : ℕ)
    (K : DivisibleSystem (CochainComplex (Rep.{w} k Γ) ℕ) ℓ) :
    UnderlyingPowTorsionProjectiveBelow N K :=
  fun m q _ => ((K.degree q).map (forget₂ (Rep.{w} k Γ) (ModuleCat.{w} k))).powTorsionProjective_obj
    h m

end UnderlyingBelow

section GroupTotal

variable {k : Type u} [CommRing k] {Γ : Type v} [Group Γ] [Finite Γ] {ℓ : ℕ} {π : k} {e : ℕ}
  (hℓ : IsUnitMulUniformizerPow ℓ π e) (N : ℕ)
  (K : DivisibleSystem (CochainComplex (Rep.{max w u v} k Γ) ℕ) ℓ)

include hℓ

/-- If `ℓ = u π ^ e` in `k` (`IsUnitMulUniformizerPow`), the total complexes of the standard
resolutions along `Ind_1^Γ Res_1^Γ` of an `ℓ`-divisible system of complexes of representations of
a finite group `Γ` satisfy `TermwisePowTorsionProjective`. -/
lemma termwisePowTorsionProjective_groupStandardTotalSystem_of_isUnitMulUniformizerPow :
    TermwisePowTorsionProjective (groupStandardTotalSystem.{w} N K) :=
  termwisePowTorsionProjective_groupStandardTotalSystem k N K
    (underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow hℓ N K)

variable (W : DivisibleSystem (Rep.{max w u v} k Γ) ℓ)

/-- Harris 1999, p.312, (4.10.3), for `T_m(j) = Hom(C_m^j, W_m)` with `C_m^•` the total
complexes `groupStandardTotalSystem`, when `ℓ = u π ^ e` in `k`: the transitions of the inverse
system of the `T_m(j)` are surjective. -/
lemma groupStandardTotalSystem_degree_homSystem_map_surjective_of_isUnitMulUniformizerPow
    (j : ℤ) {m m' : ℕᵒᵖ} (φ : m ⟶ m') :
    Function.Surjective
      ((homSystem k ((groupStandardTotalSystem.{w} N K).degree j) W).map φ) :=
  groupStandardTotalSystem_degree_homSystem_map_surjective k N K
    (underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow hℓ N K) W j φ

/-- When `ℓ = u π ^ e` in `k`, the inverse system of the `T_m(j) = Hom(C_m^j, W_m)`, `C_m^•` the
total complexes `groupStandardTotalSystem`, satisfies the Mittag-Leffler condition. -/
lemma isMittagLeffler_groupStandardTotalSystem_degree_homSystem_of_isUnitMulUniformizerPow
    (j : ℤ) :
    (homSystem k ((groupStandardTotalSystem.{w} N K).degree j) W ⋙
      CategoryTheory.forget (ModuleCat.{max w u v} k)).IsMittagLeffler :=
  isMittagLeffler_groupStandardTotalSystem_degree_homSystem k N K
    (underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow hℓ N K) W j

variable (W : DivisibleSystem (CochainComplex (Rep.{max w u v} k Γ) ℤ) ℓ)

/-- When `ℓ = u π ^ e` in `k`, the inverse system of Hom complexes `Hom^•(C_m^•, W_m)`, `C_m^•`
the total complexes `groupStandardTotalSystem`, satisfies the Mittag-Leffler condition in every
degree. -/
lemma isMittagLeffler_groupStandardTotalSystem_homComplexSystem_eval_of_isUnitMulUniformizerPow
    (n : ℤ) :
    (homComplexSystem k (groupStandardTotalSystem.{w} N K) W ⋙
      HomologicalComplex.eval (ModuleCat.{max w u v} k) (ComplexShape.up ℤ) n ⋙
        CategoryTheory.forget (ModuleCat.{max w u v} k)).IsMittagLeffler :=
  isMittagLeffler_groupStandardTotalSystem_homComplexSystem_eval k N K
    (underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow hℓ N K) W n

end GroupTotal

section SmoothTotal

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {ℓ : ℕ}
  {π : R} {e : ℕ}
  (N : ℕ) (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, max w uR uG} R G) ℕ) ℓ)
  (H : Subgroup G) [H.Normal] [H.FiniteIndex]
  (hK : ∀ {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R H).map ((K.projection h).f q)))
  (hℓ : IsUnitMulUniformizerPow ℓ π e)

include hℓ

/-- If `ℓ = u π ^ e` in `R` (`IsUnitMulUniformizerPow`), Harris's `C_m^{•,H}`
(`quotientInvariantsTotalSystem`) satisfies `TermwisePowTorsionProjective`. -/
lemma termwisePowTorsionProjective_quotientInvariantsTotalSystem_of_isUnitMulUniformizerPow :
    TermwisePowTorsionProjective (K.quotientInvariantsTotalSystem N H hK) :=
  termwisePowTorsionProjective_quotientInvariantsTotalSystem.{w, uR, uG} N K H hK
    (underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow hℓ N
      (K.quotientInvariantsComplexes H hK))

variable (W : DivisibleSystem (Rep.{max w uR uG} R (G ⧸ H)) ℓ)

/-- Harris 1999, p.312, (4.10.3), for `T_m(j) = Hom(C_m^{j,H}, W_m)` with `C_m^{•,H}` the
complexes `quotientInvariantsTotalSystem`, when `ℓ = u π ^ e` in `R`: the transitions of the
inverse system of the `T_m(j)` are surjective. -/
lemma quotientInvariantsTotalSystem_degree_homSystem_map_surjective_of_isUnitMulUniformizerPow
    (j : ℤ) {m m' : ℕᵒᵖ} (φ : m ⟶ m') :
    Function.Surjective
      ((homSystem R ((K.quotientInvariantsTotalSystem N H hK).degree j) W).map φ) :=
  quotientInvariantsTotalSystem_degree_homSystem_map_surjective.{w, uR, uG} N K H hK
    (underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow hℓ N
      (K.quotientInvariantsComplexes H hK)) W j φ

/-- When `ℓ = u π ^ e` in `R`, the inverse system of the `T_m(j) = Hom(C_m^{j,H}, W_m)`,
`C_m^{•,H}` the complexes `quotientInvariantsTotalSystem`, satisfies the Mittag-Leffler
condition. -/
lemma isMittagLeffler_quotientInvariantsTotalSystem_degree_homSystem_of_isUnitMulUniformizerPow
    (j : ℤ) :
    (homSystem R ((K.quotientInvariantsTotalSystem N H hK).degree j) W ⋙
      CategoryTheory.forget (ModuleCat.{max w uR uG} R)).IsMittagLeffler :=
  isMittagLeffler_quotientInvariantsTotalSystem_degree_homSystem.{w, uR, uG} N K H hK
    (underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow hℓ N
      (K.quotientInvariantsComplexes H hK)) W j

variable (W : DivisibleSystem (CochainComplex (Rep.{max w uR uG} R (G ⧸ H)) ℤ) ℓ)

/-- When `ℓ = u π ^ e` in `R`, the inverse system of Hom complexes `Hom^•(C_m^{•,H}, W_m)`,
`C_m^{•,H}` the complexes `quotientInvariantsTotalSystem`, satisfies the Mittag-Leffler condition
in every degree. -/
lemma
    isMittagLeffler_quotientInvariantsTotalSystem_homComplexSystem_eval_of_isUnitMulUniformizerPow
    (n : ℤ) :
    (homComplexSystem R (K.quotientInvariantsTotalSystem N H hK) W ⋙
      HomologicalComplex.eval (ModuleCat.{max w uR uG} R) (ComplexShape.up ℤ) n ⋙
        CategoryTheory.forget (ModuleCat.{max w uR uG} R)).IsMittagLeffler :=
  isMittagLeffler_quotientInvariantsTotalSystem_homComplexSystem_eval.{w, uR, uG} N K H hK
    (underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow hℓ N
      (K.quotientInvariantsComplexes H hK)) W n

end SmoothTotal

section SmoothGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ} {π : R} {e : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ) (H : Subgroup G) [H.Normal] [H.FiniteIndex]
  (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
      ((smoothGodementTermSystem h T q).projection hm)))
  (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections R G X ⋙ smoothQuotientInvariants R H).map
      ((smoothGodementResidualSystem h T (D + 1)).projection hm)))
  (hℓ : IsUnitMulUniformizerPow ℓ π e)

include hℓ

/-- If `ℓ = u π ^ e` in `R` (`IsUnitMulUniformizerPow`), Harris's `C_m^{•,H}` for the truncated
smooth Godement resolutions (`smoothGodementInvariantTotalSystem`) satisfies
`TermwisePowTorsionProjective`. -/
lemma termwisePowTorsionProjective_smoothGodementInvariantTotalSystem_of_isUnitMulUniformizerPow :
    TermwisePowTorsionProjective (smoothGodementInvariantTotalSystem h T D H hterm hres) :=
  termwisePowTorsionProjective_smoothGodementInvariantTotalSystem h T D H hterm hres
    (underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow hℓ _ _)

variable (W : DivisibleSystem (Rep.{u} R (G ⧸ H)) ℓ)

/-- Harris 1999, p.312, (4.10.3), for `T_m(j) = Hom(C_m^{j,H}, W_m)` with `C_m^{•,H}` the
complexes `smoothGodementInvariantTotalSystem`, when `ℓ = u π ^ e` in `R`: the transitions of the
inverse system of the `T_m(j)` are surjective. -/
lemma
    smoothGodementInvariantTotalSystem_degree_homSystem_map_surjective_of_isUnitMulUniformizerPow
    (j : ℤ) {m m' : ℕᵒᵖ} (φ : m ⟶ m') :
    Function.Surjective
      ((homSystem R ((smoothGodementInvariantTotalSystem h T D H hterm hres).degree j) W).map
        φ) :=
  smoothGodementInvariantTotalSystem_degree_homSystem_map_surjective h T D H hterm hres
    (underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow hℓ _ _) W j φ

/-- When `ℓ = u π ^ e` in `R`, the inverse system of the `T_m(j) = Hom(C_m^{j,H}, W_m)`,
`C_m^{•,H}` the complexes `smoothGodementInvariantTotalSystem`, satisfies the Mittag-Leffler
condition. -/
lemma
    isMittagLeffler_smoothGodementInvariantTotalSystem_degree_homSystem_of_isUnitMulUniformizerPow
    (j : ℤ) :
    (homSystem R ((smoothGodementInvariantTotalSystem h T D H hterm hres).degree j) W ⋙
      CategoryTheory.forget (ModuleCat.{u} R)).IsMittagLeffler :=
  isMittagLeffler_smoothGodementInvariantTotalSystem_degree_homSystem h T D H hterm hres
    (underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow hℓ _ _) W j

variable (W : DivisibleSystem (CochainComplex (Rep.{u} R (G ⧸ H)) ℤ) ℓ)

/-- When `ℓ = u π ^ e` in `R`, the inverse system of Hom complexes `Hom^•(C_m^{•,H}, W_m)`,
`C_m^{•,H}` the complexes `smoothGodementInvariantTotalSystem`, satisfies the Mittag-Leffler
condition in every degree. -/
lemma
    isMittagLeffler_smoothGodementInvariantTotalSystem_homComplexSystem_eval_of_isUnitMulUniformizerPow
    (n : ℤ) :
    (homComplexSystem R (smoothGodementInvariantTotalSystem h T D H hterm hres) W ⋙
      HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n ⋙
        CategoryTheory.forget (ModuleCat.{u} R)).IsMittagLeffler :=
  isMittagLeffler_smoothGodementInvariantTotalSystem_homComplexSystem_eval h T D H hterm hres
    (underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow hℓ _ _) W n

end SmoothGodement

section ProPSmoothGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ} {π : R} {e : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ) (hP : ProPInvariantsExactStatement.{u, u, u}) {p : ℕ} {H : Subgroup G} [H.Normal]
  [H.FiniteIndex] (hH : IsProPSubgroup p H) (hR : IsUnit (p : R))
  (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections R G X).map
      ((smoothGodementTermSystem h T q).projection hm)))
  (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections R G X).map
      ((smoothGodementResidualSystem h T (D + 1)).projection hm)))
  (hℓ : IsUnitMulUniformizerPow ℓ π e)

include hℓ

/-- If `ℓ = u π ^ e` in `R` (`IsUnitMulUniformizerPow`), Harris's `C_m^{•,H}` for the truncated
smooth Godement resolutions and a normal pro-`p` subgroup `H` of finite index
(`proPSmoothGodementInvariantTotalSystem`) satisfies `TermwisePowTorsionProjective`. -/
lemma
    termwisePowTorsionProjective_proPSmoothGodementInvariantTotalSystem_of_isUnitMulUniformizerPow :
    TermwisePowTorsionProjective
      (proPSmoothGodementInvariantTotalSystem h T D hP hH hR hterm hres) :=
  termwisePowTorsionProjective_proPSmoothGodementInvariantTotalSystem h T D hP hH hR hterm hres
    (underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow hℓ _ _)

variable (W : DivisibleSystem (Rep.{u} R (G ⧸ H)) ℓ)

/-- Harris 1999, p.312, (4.10.3), for `T_m(j) = Hom(C_m^{j,H}, W_m)` with `C_m^{•,H}` the
complexes `proPSmoothGodementInvariantTotalSystem`, when `ℓ = u π ^ e` in `R`: the transitions of
the inverse system of the `T_m(j)` are surjective. -/
lemma
    proPSmoothGodementInvariantTotalSystem_degree_homSystem_map_surjective_of_isUnitMulUniformizerPow
    (j : ℤ) {m m' : ℕᵒᵖ} (φ : m ⟶ m') :
    Function.Surjective
      ((homSystem R ((proPSmoothGodementInvariantTotalSystem h T D hP hH hR hterm hres).degree
        j) W).map φ) :=
  proPSmoothGodementInvariantTotalSystem_degree_homSystem_map_surjective h T D hP hH hR hterm hres
    (underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow hℓ _ _) W j φ

/-- When `ℓ = u π ^ e` in `R`, the inverse system of the `T_m(j) = Hom(C_m^{j,H}, W_m)`,
`C_m^{•,H}` the complexes `proPSmoothGodementInvariantTotalSystem`, satisfies the Mittag-Leffler
condition. -/
lemma
    isMittagLeffler_proPSmoothGodementInvariantTotalSystem_degree_homSystem_of_isUnitMulUniformizerPow
    (j : ℤ) :
    (homSystem R ((proPSmoothGodementInvariantTotalSystem h T D hP hH hR hterm hres).degree j)
      W ⋙ CategoryTheory.forget (ModuleCat.{u} R)).IsMittagLeffler :=
  isMittagLeffler_proPSmoothGodementInvariantTotalSystem_degree_homSystem h T D hP hH hR hterm
    hres (underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow hℓ _ _) W j

variable (W : DivisibleSystem (CochainComplex (Rep.{u} R (G ⧸ H)) ℤ) ℓ)

/-- When `ℓ = u π ^ e` in `R`, the inverse system of Hom complexes `Hom^•(C_m^{•,H}, W_m)`,
`C_m^{•,H}` the complexes `proPSmoothGodementInvariantTotalSystem`, satisfies the Mittag-Leffler
condition in every degree. -/
lemma
    isMittagLeffler_proPSmoothGodementInvariantTotalSystem_homComplexSystem_eval_of_isUnitMulUniformizerPow
    (n : ℤ) :
    (homComplexSystem R (proPSmoothGodementInvariantTotalSystem h T D hP hH hR hterm hres) W ⋙
      HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n ⋙
        CategoryTheory.forget (ModuleCat.{u} R)).IsMittagLeffler :=
  isMittagLeffler_proPSmoothGodementInvariantTotalSystem_homComplexSystem_eval h T D hP hH hR
    hterm hres (underlyingPowTorsionProjectiveBelow_of_isUnitMulUniformizerPow hℓ _ _) W n

end ProPSmoothGodement

end DivisibleSystem

end Langlands.Cohomology
