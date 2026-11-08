import Langlands.LocalFactor.Abelian.GaussShellVanishing
import Langlands.ClassFieldTheory.Local.NormOrderProof
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Langlands.LocalFactor.RankOneStabilityProof

/-! # The quadratic norm–trace estimate for finite extensions of p-adic fields -/

noncomputable section

universe u v

namespace Langlands.LocalFactor.NonabelianSystem.DeligneHenniart

/-- Ultrametric bound for the first two terms of a product of `1 + x i`. -/
theorem prod_one_add_sub_bound {R : Type*} [CommRing R] (f : R → ℝ) (hna : IsNonarchimedean f)
    (hmul : ∀ a b, f (a * b) ≤ f a * f b) (hnn : ∀ a, 0 ≤ f a) (hzero : f 0 = 0)
    {ι : Type*} (s : Finset ι) (x : ι → R) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hx : ∀ i ∈ s, f (x i) ≤ ρ) :
    f (∑ i ∈ s, x i) ≤ ρ ∧ f (∏ i ∈ s, (1 + x i) - 1 - ∑ i ∈ s, x i) ≤ ρ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty, sub_self, hzero]
    exact ⟨hρ0, by positivity⟩
  | insert j s hj ih =>
    obtain ⟨h1, h2⟩ := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    have hxj := hx j (Finset.mem_insert_self j s)
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    refine ⟨(hna _ _).trans (max_le hxj h1), ?_⟩
    set S := ∑ i ∈ s, x i
    set P := ∏ i ∈ s, (1 + x i)
    have heq : (1 + x j) * P - 1 - (x j + S) =
        (P - 1 - S) + x j * S + x j * (P - 1 - S) := by ring
    rw [heq]
    have hA : f (x j * S) ≤ ρ ^ 2 := by
      refine (hmul _ _).trans ?_
      calc f (x j) * f S ≤ ρ * ρ := mul_le_mul hxj h1 (hnn _) hρ0
        _ = ρ ^ 2 := by ring
    have hB : f (x j * (P - 1 - S)) ≤ ρ ^ 2 := by
      refine (hmul _ _).trans ?_
      calc f (x j) * f (P - 1 - S) ≤ 1 * ρ ^ 2 :=
            mul_le_mul (hxj.trans hρ1) h2 (hnn _) zero_le_one
        _ = ρ ^ 2 := one_mul _
    exact (hna _ _).trans (max_le ((hna _ _).trans (max_le h2 hA)) hB)

variable {p : ℕ} [Fact p.Prime]
variable (F : PadicField.{u} p) (E : PadicField.{v} p)
variable [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
variable [FiniteDimensional F.Carrier E.Carrier]

/-- The quadratic remainder `N(1 + y) - 1 - Tr y` of the norm, in the base field. -/
def normTraceRemainder (y : E.Carrier) : F.Carrier :=
  Algebra.norm F.Carrier (1 + y) - 1 - Algebra.trace F.Carrier E.Carrier y

/-- DH81 3.3: writing the norm as a product of conjugates, `N(1 + y) - 1 - Tr y` has
canonical absolute value at most `|y|²`, and `Tr y` at most `|y|`, for `|y| ≤ 1`. -/
theorem canonicalNorm_norm_one_add_sub_le (y : E.Carrier) (hy : E.canonicalNorm y ≤ 1) :
    F.canonicalNorm (normTraceRemainder F E y) ≤ E.canonicalNorm y ^ 2 ∧
      F.canonicalNorm (Algebra.trace F.Carrier E.Carrier y) ≤ E.canonicalNorm y := by
  classical
  let Ω := AlgebraicClosure E.Carrier
  have : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  have : CharZero E.Carrier := Algebra.charZero_of_charZero (Padic p) E.Carrier
  have : Algebra.IsSeparable F.Carrier E.Carrier := inferInstance
  have hfinE : FiniteDimensional (Padic p) E.Carrier := inferInstance
  have : Algebra.IsAlgebraic (Padic p) E.Carrier := inferInstance
  have : Algebra.IsAlgebraic E.Carrier Ω := inferInstance
  have halg : Algebra.IsAlgebraic (Padic p) Ω := Algebra.IsAlgebraic.trans (Padic p) E.Carrier Ω
  let f : Ω → ℝ := spectralNorm (Padic p) Ω
  have hna : IsNonarchimedean f := isNonarchimedean_spectralNorm
  have hmul : ∀ a b : Ω, f (a * b) ≤ f a * f b := fun a b =>
    spectralNorm_mul (halg.isAlgebraic a) (halg.isAlgebraic b)
  have hnn : ∀ a : Ω, 0 ≤ f a := spectralNorm_nonneg
  have hzero : f 0 = 0 := spectralNorm_zero
  have hσ : ∀ σ : E.Carrier →ₐ[F.Carrier] Ω, f (σ y) = E.canonicalNorm y := by
    intro σ
    change spectralValue (minpoly (Padic p) (σ y)) = spectralValue (minpoly (Padic p) y)
    rw [show σ y = (σ.restrictScalars (Padic p)) y from rfl,
      minpoly.algHom_eq _ (σ.restrictScalars (Padic p)).toRingHom.injective]
  have hF : ∀ z : F.Carrier, F.canonicalNorm z = f (algebraMap F.Carrier Ω z) := by
    intro z
    change spectralValue (minpoly (Padic p) z) =
      spectralValue (minpoly (Padic p) (algebraMap F.Carrier Ω z))
    rw [minpoly.algebraMap_eq (algebraMap F.Carrier Ω).injective]
  obtain ⟨hsum, hprod⟩ := prod_one_add_sub_bound f hna hmul hnn hzero Finset.univ
    (fun σ : E.Carrier →ₐ[F.Carrier] Ω => σ y) (ρ := E.canonicalNorm y)
    (spectralNorm_nonneg (K := Padic p) y) hy
    (fun σ _ => (hσ σ).le)
  have hN := Algebra.norm_eq_prod_embeddings F.Carrier Ω (1 + y)
  have hT : algebraMap F.Carrier Ω (Algebra.trace F.Carrier E.Carrier y) =
      ∑ σ : E.Carrier →ₐ[F.Carrier] Ω, σ y := trace_eq_sum_embeddings Ω
  constructor
  · rw [normTraceRemainder, hF, map_sub, map_sub, map_one, hN, hT]
    simpa only [map_add, map_one] using hprod
  · rw [hF, hT]
    exact hsum

/-! ## Translation to normalized orders -/

section Orders

variable {G : PadicField.{u} p} (T : G.TopologicalData)

/-- A power of the canonical norm is an integral power of `p`. -/
theorem canonicalNorm_pow_ef {x : G.Carrier} (hx : x ≠ 0) :
    G.canonicalNorm x ^ (T.ramificationIndex * T.residueDegree) =
      (p : ℝ) ^ ((T.residueDegree : ℤ) * -T.ord x) := by
  rw [← T.normalizedAbs_eq_canonicalNorm_pow_ef, T.normalizedAbs_of_ne_zero hx,
    T.residueCardinality_eq_pow, Nat.cast_pow, ← zpow_natCast, ← zpow_mul]

theorem discreteValuation_eq_exp_neg_ord {x : G.Carrier} (hx : x ≠ 0) :
    T.discreteValuation x = WithZero.exp (-T.ord x) :=
  PadicAbelian.gauss_valuation_eq_exp_neg_ord T hx

theorem mem_additiveLattice_neg_of_le_ord {x : G.Carrier} {m : ℤ} (hm : m ≤ T.ord x)
    (hx : x ≠ 0) : x ∈ T.additiveLattice (-m) := by
  rw [PadicField.TopologicalData.mem_additiveLattice, discreteValuation_eq_exp_neg_ord T hx,
    WithZero.exp_le_exp]
  omega

end Orders

omit [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [FiniteDimensional F.Carrier E.Carrier] in
/-- Comparison of canonical norms on `F` and `E` in terms of orders: if
`|z| ≤ |y| ^ k`, then `k e_F ord_E y ≤ e_E ord_F z`, with absolute ramification
indices `e_F` and `e_E`. -/
theorem ord_mul_le_of_canonicalNorm_le (TF : F.TopologicalData) (TE : E.TopologicalData)
    {z : F.Carrier} {y : E.Carrier} (hz : z ≠ 0) (hy : y ≠ 0) (k : ℕ)
    (h : F.canonicalNorm z ≤ E.canonicalNorm y ^ k) :
    (k : ℤ) * TF.ramificationIndex * TE.ord y ≤ TE.ramificationIndex * TF.ord z := by
  set eF := TF.ramificationIndex
  set fF := TF.residueDegree
  set eE := TE.ramificationIndex
  set fE := TE.residueDegree
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hz0 : 0 ≤ F.canonicalNorm z := spectralNorm_nonneg (K := Padic p) z
  have h' := pow_le_pow_left₀ hz0 h (eF * fF * (eE * fE))
  have hl : F.canonicalNorm z ^ (eF * fF * (eE * fE)) =
      (p : ℝ) ^ ((fF : ℤ) * -TF.ord z * ((eE * fE : ℕ) : ℤ)) := by
    rw [pow_mul, canonicalNorm_pow_ef TF hz, ← zpow_natCast, ← zpow_mul]
  have hr : (E.canonicalNorm y ^ k) ^ (eF * fF * (eE * fE)) =
      (p : ℝ) ^ ((fE : ℤ) * -TE.ord y * ((k * eF * fF : ℕ) : ℤ)) := by
    rw [← pow_mul, show k * (eF * fF * (eE * fE)) = eE * fE * (k * eF * fF) by ring, pow_mul,
      canonicalNorm_pow_ef TE hy, ← zpow_natCast, ← zpow_mul]
  rw [hl, hr, zpow_le_zpow_iff_right₀ hp] at h'
  have hf : (0 : ℤ) < fF * fE := by
    have := TF.residueDegree_pos
    have := TE.residueDegree_pos
    positivity
  push_cast at h'
  nlinarith

/-- DH81 3.3 and 3.6: a first-order linearization of a character of `F` on
`U^m`, together with triviality on `U^a`, gives the value of its norm pullback on
`1 + y` through the trace, as soon as `y` is deep enough in `E`. -/
theorem character_norm_one_add (TF : F.TopologicalData) (TE : E.TopologicalData)
    (χ : F.Carrierˣ →* ℂˣ)
    (ψ : AddChar F.Carrier ℂ) (c : F.Carrier) {m a : ℕ} (hm : 0 < m) (ha : 0 < a)
    (hlin : ∀ z ∈ TF.principalUnits m, (χ z : ℂ) = ψ (c * ((z : F.Carrier) - 1)))
    (hχ : ∀ z ∈ TF.principalUnits a, χ z = 1)
    (y : E.Carrier) (hy : y ≠ 0) (hy1 : 0 < TE.ord y)
    (hR : ((a : ℤ) - 1) * TE.ramificationIndex < 2 * TF.ramificationIndex * TE.ord y)
    (hT : ((m : ℤ) - 1) * TE.ramificationIndex < TF.ramificationIndex * TE.ord y)
    (u : E.Carrierˣ) (hu : (u : E.Carrier) = 1 + y) :
    (χ (Units.map (Algebra.norm F.Carrier) u) : ℂ) =
      ψ (c * Algebra.trace F.Carrier E.Carrier y) := by
  have hyI : y ∈ TE.Integers := by
    rw [TE.mem_integers_iff_discreteValuation_le_one, discreteValuation_eq_exp_neg_ord TE hy,
      WithZero.exp_le_one_iff]
    omega
  have hy1' : E.canonicalNorm y ≤ 1 := (TE.canonicalNorm_le_one_iff_mem_integers y).mpr hyI
  obtain ⟨hRn, hTn⟩ := canonicalNorm_norm_one_add_sub_le F E y hy1'
  set t := Algebra.trace F.Carrier E.Carrier y with ht
  set R := normTraceRemainder F E y with hRdef
  have heE : (0 : ℤ) < TE.ramificationIndex := by exact_mod_cast TE.ramificationIndex_pos
  have heF : (0 : ℤ) < TF.ramificationIndex := by exact_mod_cast TF.ramificationIndex_pos
  -- the trace lies in the `m`-th lattice
  have htm : t ∈ TF.additiveLattice (-(m : ℤ)) := by
    by_cases ht0 : t = 0
    · rw [ht0]; exact AddSubgroup.zero_mem _
    have hle := ord_mul_le_of_canonicalNorm_le F E TF TE ht0 hy 1 (by simpa using hTn)
    push_cast at hle
    apply mem_additiveLattice_neg_of_le_ord TF _ ht0
    by_contra hlt
    push Not at hlt
    have : TE.ramificationIndex * TF.ord t ≤ ((m : ℤ) - 1) * TE.ramificationIndex := by
      nlinarith
    linarith
  -- the quadratic remainder lies in the `a`-th lattice
  have hRa : R ∈ TF.additiveLattice (-(a : ℤ)) := by
    by_cases hR0 : R = 0
    · rw [hR0]; exact AddSubgroup.zero_mem _
    have hle := ord_mul_le_of_canonicalNorm_le F E TF TE hR0 hy 2 hRn
    apply mem_additiveLattice_neg_of_le_ord TF _ hR0
    by_contra hlt
    push Not at hlt
    have : TE.ramificationIndex * TF.ord R ≤ ((a : ℤ) - 1) * TE.ramificationIndex := by
      nlinarith
    push_cast at hle
    linarith
  -- the unit `w = 1 + t` of level `m`
  have hw1 : TF.discreteValuation (1 + t) = 1 :=
    RankOneStability.valuation_one_add TF hm htm
  have hw0 : (1 + t) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hw1
    exact zero_ne_one hw1
  let w : F.Carrierˣ := Units.mk0 (1 + t) hw0
  have hwm : w ∈ TF.principalUnits m := by
    refine ⟨hw1, ?_⟩
    change TF.discreteValuation (1 + t - 1) ≤ _
    rw [add_sub_cancel_left]
    exact htm
  set v := Units.map (Algebra.norm F.Carrier) u with hv
  have hvval : (v : F.Carrier) = (1 + t) + R := by
    rw [hv]
    change Algebra.norm F.Carrier (u : E.Carrier) = _
    rw [hu, hRdef, normTraceRemainder]
    ring
  have hratio : v * w⁻¹ ∈ TF.principalUnits a := by
    have hRle : TF.discreteValuation R ≤ WithZero.exp (-(a : ℤ)) := hRa
    have hval : ((v * w⁻¹ : F.Carrierˣ) : F.Carrier) - 1 = R * (1 + t)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hvval]
      change ((1 + t) + R) * (1 + t)⁻¹ - 1 = R * (1 + t)⁻¹
      field_simp
      ring
    have hdv : TF.discreteValuation (((v * w⁻¹ : F.Carrierˣ) : F.Carrier) - 1) ≤
        WithZero.exp (-(a : ℤ)) := by
      rw [hval, map_mul, map_inv₀, hw1, inv_one, mul_one]
      exact hRle
    refine ⟨?_, hdv⟩
    have hlt : TF.discreteValuation (((v * w⁻¹ : F.Carrierˣ) : F.Carrier) - 1) < 1 := by
      exact hdv.trans_lt (WithZero.exp_lt_one_iff.mpr (by omega))
    have := TF.discreteValuation.map_add_eq_of_lt_left
      (x := 1) (y := ((v * w⁻¹ : F.Carrierˣ) : F.Carrier) - 1) (by simpa using hlt)
    simpa using this
  have hχv : χ v = χ w := by
    have h1 := hχ _ hratio
    rw [map_mul, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  rw [hχv, hlin w hwm]
  simp [w]

/-! ## Rank-one twists through a comparison element -/

section RankOne

variable {G : PadicField.{u} p} (T : G.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter G.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter G.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure G.Carrier _ T.topology (@borel G.Carrier T.topology)

/-- Two elements that define the same additive character on the lattice of depth `t`,
the second of order `-(n(ψ) + A)`, differ by a principal unit of level `A - t`. -/
theorem mul_inv_mem_principalUnits_of_eq_on_lattice (ψ : AdditiveCharacter)
    {c c' : G.Carrierˣ} {A t : ℕ} (htA : t < A)
    (hc' : T.ord (c' : G.Carrier) = -(T.additiveConductor ψ + A))
    (h : letI := T.topology; ∀ x ∈ T.additiveLattice (-(t : ℤ)),
      ψ.complex ((c : G.Carrier) * x) = ψ.complex ((c' : G.Carrier) * x)) :
    c * c'⁻¹ ∈ T.principalUnits (A - t) := by
  let := T.topology
  have hd : ((c : G.Carrier) - c') ∈ T.additiveLattice (T.additiveConductor ψ - -(t : ℤ)) := by
    apply T.mem_additiveLattice_of_forall_complex_mul_eq_one ψ
    intro x hx
    rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, h x hx, ← AddChar.map_add_eq_mul,
      ← neg_mul, ← add_mul, add_neg_cancel, zero_mul, AddChar.map_zero_eq_one]
  have hc'0 : (c' : G.Carrier) ≠ 0 := c'.ne_zero
  have hvc' : T.discreteValuation (c' : G.Carrier) =
      WithZero.exp (T.additiveConductor ψ + A) := by
    rw [discreteValuation_eq_exp_neg_ord T hc'0, hc', neg_neg]
  have hval : ((c * c'⁻¹ : G.Carrierˣ) : G.Carrier) - 1 =
      ((c : G.Carrier) - c') * (c' : G.Carrier)⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  have hle : T.discreteValuation (((c * c'⁻¹ : G.Carrierˣ) : G.Carrier) - 1) ≤
      WithZero.exp (-((A - t : ℕ) : ℤ)) := by
    rw [hval, map_mul, map_inv₀, hvc']
    have h1 : T.discreteValuation ((c : G.Carrier) - c') ≤
        WithZero.exp (T.additiveConductor ψ + t) := by simpa using hd
    calc T.discreteValuation ((c : G.Carrier) - c') *
          (WithZero.exp (T.additiveConductor ψ + A))⁻¹
        ≤ WithZero.exp (T.additiveConductor ψ + t) *
          (WithZero.exp (T.additiveConductor ψ + A))⁻¹ := mul_le_mul' h1 le_rfl
      _ = WithZero.exp (-((A - t : ℕ) : ℤ)) := by
        rw [← WithZero.exp_neg, ← WithZero.exp_add]
        congr 1
        omega
  refine ⟨?_, hle⟩
  have hlt : T.discreteValuation (((c * c'⁻¹ : G.Carrierˣ) : G.Carrier) - 1) < 1 :=
    hle.trans_lt (WithZero.exp_lt_one_iff.mpr (by omega))
  have := T.discreteValuation.map_add_eq_of_lt_left
    (x := 1) (y := ((c * c'⁻¹ : G.Carrierˣ) : G.Carrier) - 1) (by simpa using hlt)
  simpa using this

/-- A linearizing element of the correct order gives the rank-one twist relation
for every character of conductor at most half of that of `χ`, at every Haar
measure. This is the argument of the published `rankOneStability`, at `s = 0`. -/
theorem abelianEpsilonExpression_mul_of_linearization (χ η : Character)
    (ψ : AdditiveCharacter) (μ : LocalHaar) (ha : 2 ≤ T.multiplicativeConductor χ)
    (hη : 2 * T.multiplicativeConductor η ≤ T.multiplicativeConductor χ)
    (d : G.Carrierˣ)
    (hd : T.ord (d : G.Carrier) = -(T.additiveConductor ψ + T.multiplicativeConductor χ))
    (hm : 0 < T.multiplicativeConductor χ - T.multiplicativeConductor χ / 2)
    (hlin : letI := T.topology;
      ∀ h : T.additiveLattice (-((T.multiplicativeConductor χ -
          T.multiplicativeConductor χ / 2 : ℕ) : ℤ)),
        (χ (RankOneStability.oneAddUnit T hm h) : ℂ) = ψ.complex ((d : G.Carrier) * h.val)) :
    T.abelianEpsilonExpression (χ * η) ψ μ = (η d⁻¹ : ℂ) * T.abelianEpsilonExpression χ ψ μ := by
  let := T.topology
  let : MeasurableSpace G.Carrier := borel G.Carrier
  set a := T.multiplicativeConductor χ with ha'
  set k := a / 2
  set m := a - k
  have hlevels : a = m + k := by omega
  have hkm : k ≤ m := by omega
  have hηk : T.multiplicativeConductor η ≤ k := by omega
  have hηm : T.multiplicativeConductor η ≤ m := hηk.trans hkm
  have hcond := (RankOneStability.conductor_and_L T χ ha η hη).1
  have hd' : T.ord (d : G.Carrier) = -(T.additiveConductor ψ + a) := hd
  have hint := RankOneStability.gauss_integral_twist T χ η ψ μ a m k hm hlevels hηk hηm d hd'
    hlin
  have ha0 : T.multiplicativeConductor χ ≠ 0 := by omega
  rw [← PadicAbelian.deligneConstant_eq_abelianEpsilonExpression,
    ← PadicAbelian.deligneConstant_eq_abelianEpsilonExpression]
  dsimp only [PadicAbelian.deligneConstant, PadicAbelian.epsilon, PadicAbelian.epsilonAt]
  rw [hcond, ite_eq_right ha0, ite_eq_right ha0]
  exact hint

/-- The rank-one twist relation holds at any element that differs from a linearizing
element by a principal unit on which `η` is trivial. -/
theorem abelianEpsilonExpression_mul_of_comparison (χ η : Character)
    (ψ : AdditiveCharacter) (μ : LocalHaar) (ha : 2 ≤ T.multiplicativeConductor χ)
    (hη : 2 * T.multiplicativeConductor η ≤ T.multiplicativeConductor χ)
    (d : G.Carrierˣ)
    (hd : T.ord (d : G.Carrier) = -(T.additiveConductor ψ + T.multiplicativeConductor χ))
    (hm : 0 < T.multiplicativeConductor χ - T.multiplicativeConductor χ / 2)
    (hlin : letI := T.topology;
      ∀ h : T.additiveLattice (-((T.multiplicativeConductor χ -
          T.multiplicativeConductor χ / 2 : ℕ) : ℤ)),
        (χ (RankOneStability.oneAddUnit T hm h) : ℂ) = ψ.complex ((d : G.Carrier) * h.val))
    (c : G.Carrierˣ) {s : ℕ} (hcd : c * d⁻¹ ∈ T.principalUnits s)
    (hηs : T.multiplicativeConductor η ≤ s) :
    T.abelianEpsilonExpression (χ * η) ψ μ = (η c⁻¹ : ℂ) * T.abelianEpsilonExpression χ ψ μ := by
  let := T.topology
  rw [abelianEpsilonExpression_mul_of_linearization T χ η ψ μ ha hη d hd hm hlin]
  have h1 := (T.multiplicativeTrivialAt_iff_conductor_le η s).mpr hηs _ hcd
  rw [map_mul, map_inv] at h1
  have h2 : η c = η d := mul_inv_eq_one.mp h1
  rw [map_inv, map_inv, h2]

end RankOne

end Langlands.LocalFactor.NonabelianSystem.DeligneHenniart
