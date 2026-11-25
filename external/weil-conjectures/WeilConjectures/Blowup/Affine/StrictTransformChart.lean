/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps
public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import WeilConjectures.Mathlib.Algebra.Module.Torsion

/-!

# The strict transform on an affine blow-up chart

Let `A → B` be a ring map, `I ⊆ A` an ideal and `a ∈ I`. The affine chart of the base change
`Spec B ×_{Spec A} Bl_I(Spec A)` at `a` has coordinate ring
`C_a(A, B, I) = B ⊗_A A[I/a]`, and the strict transform of `Spec B` is cut out in it by the
`a`-power torsion: its coordinate ring is `C_a^st(A, B, I) = C_a(A, B, I) / Γ_(a)`. We show that
`C_a^st(A, B, I)` is the chart ring `B[IB/b]` of the blow-up of `Spec B` along `IB`, where `b` is
the image of `a`: the map `σ_a : C_a(A, B, I) → B[IB/b]`, `y ⊗ x/a ↦ y·x̄/b`, is surjective with
kernel the `a`-power torsion.

## Main definitions

- `AlgebraicGeometry.AffineBlowup.BaseChangeChart`: the ring `C_a(A, B, I) = B ⊗_A A[I/a]`.
- `AlgebraicGeometry.AffineBlowup.StrictChart`: the ring `C_a^st(A, B, I) = C_a(A, B, I)/Γ_(a)`.
- `AlgebraicGeometry.AffineBlowup.strictChartMap`: the map `σ_a : C_a(A, B, I) → B[IB/b]`.
- `AlgebraicGeometry.AffineBlowup.strictChartEquiv`: the induced isomorphism
  `σ̄_a : C_a^st(A, B, I) ≃ B[IB/b]`.

## Main results

- `AlgebraicGeometry.AffineBlowup.strictChartMap_surjective`: `σ_a` is surjective.
- `AlgebraicGeometry.AffineBlowup.ker_strictChartMap`: the kernel of `σ_a` is the `a`-power
  torsion of `C_a(A, B, I)`.

-/

@[expose] public section

universe u

open TensorProduct

namespace AlgebraicGeometry.AffineBlowup

variable {A : Type u} (B : Type u) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) (a : A)

/-- The coordinate ring `C_a(A, B, I) = B ⊗_A A[I/a]` of the chart at `a` of the base change of
the blow-up of `Spec A` along `I` to `Spec B`.
(blueprint: `definition-strict-transform--1`) -/
noncomputable abbrev BaseChangeChart : Type u :=
  B ⊗[A] chartRing I a

/-- The `a`-power torsion `Γ_(a)(C_a(A, B, I))`, an ideal of `C_a(A, B, I)`. -/
noncomputable abbrev baseChangeChartTorsion : Ideal (BaseChangeChart B I a) :=
  Submodule.powTorsion (BaseChangeChart B I a) (BaseChangeChart B I a)
    (algebraMap A (BaseChangeChart B I a) a)

/-- The coordinate ring `C_a^st(A, B, I) = C_a(A, B, I) / Γ_(a)(C_a(A, B, I))` of the chart at
`a` of the strict transform of `Spec B` in the blow-up of `Spec A` along `I`.
(blueprint: `definition-strict-transform--1`) -/
noncomputable abbrev StrictChart : Type u :=
  BaseChangeChart B I a ⧸ baseChangeChartTorsion B I a

/-- The localization map `A_a → B_b` along `A → B`, where `b` is the image of `a`, as a map of
`A`-algebras. -/
noncomputable def awayBaseChange :
    Localization.Away a →ₐ[A] Localization.Away (algebraMap A B a) where
  __ := Localization.awayMap (algebraMap A B) a
  commutes' r := by
    simp [IsLocalization.Away.map, IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply]

lemma awayBaseChange_chartFraction (n : ℕ) (x : A) :
    awayBaseChange B a (chartFraction a n x) = chartFraction (algebraMap A B a) n
      (algebraMap A B x) := by
  simp only [chartFraction, Localization.mk_eq_mk']
  change IsLocalization.Away.map _ _ (algebraMap A B) a _ = _
  rw [IsLocalization.Away.map, IsLocalization.map_mk']
  congr 1
  exact Subtype.ext (map_pow _ _ _)

/-- The map `C_a(A, B, I) → B_b`, `y ⊗ c ↦ y · c̄`, where `b` is the image of `a`. -/
noncomputable def baseChangeChartToAway :
    BaseChangeChart B I a →ₐ[B] Localization.Away (algebraMap A B a) :=
  Algebra.TensorProduct.lift (Algebra.ofId B _) ((awayBaseChange B a).comp (chartRing I a).val)
    fun _ _ ↦ Commute.all _ _

@[simp]
lemma baseChangeChartToAway_tmul (y : B) (c : chartRing I a) :
    baseChangeChartToAway B I a (y ⊗ₜ c) =
      algebraMap B _ y * awayBaseChange B a (c : Localization.Away a) :=
  rfl

lemma baseChangeChartToAway_algebraMap (r : A) :
    baseChangeChartToAway B I a (algebraMap A _ r) = algebraMap A _ r :=
  (baseChangeChartToAway B I a).commutes' _ |>.trans (by simp [← IsScalarTower.algebraMap_apply])

variable {a}

section

variable (ha : a ∈ I)
include ha

/-- Every element of `C_a(A, B, I)` becomes an element of `B` after multiplication by a power of
`a`. -/
lemma exists_pow_mul_eq_algebraMap (z : BaseChangeChart B I a) :
    ∃ (N : ℕ) (w : B), algebraMap A _ a ^ N * z = algebraMap B _ w := by
  induction z using TensorProduct.inductionOn with
  | tmul y c =>
    obtain ⟨n, x, hx, hc⟩ := (mem_chartRing_iff I ha).mp c.2
    refine ⟨n, y * algebraMap A B x, ?_⟩
    have hc' : (algebraMap A (chartRing I a) a) ^ n * c = algebraMap A _ x := by
      apply Subtype.ext
      simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap, hc]
      rw [← map_pow, ← chartFraction_zero, ← chartFraction_zero, ← chartFraction_mul,
        chartFraction_eq_iff]
      exact ⟨0, by ring⟩
    rw [Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, hc',
      Algebra.algebraMap_eq_smul_one (A := chartRing I a) x, ← TensorProduct.smul_tmul,
      Algebra.TensorProduct.algebraMap_apply]
    simp [Algebra.smul_def, mul_comm]
  | add z z' hz hz' =>
    obtain ⟨N, w, hw⟩ := hz
    obtain ⟨N', w', hw'⟩ := hz'
    refine ⟨N + N', algebraMap A B a ^ N' * w + algebraMap A B a ^ N * w', ?_⟩
    rw [mul_add, pow_add, mul_right_comm, hw, mul_assoc, hw', map_add, map_mul, map_mul,
      map_pow, map_pow, ← IsScalarTower.algebraMap_apply]
    ring

end

variable (a) in
/-- The image of `C_a(A, B, I)` in `B_b` lies in the chart ring `B[IB/b]`. -/
lemma baseChangeChartToAway_mem_chartRing (ha : a ∈ I) (z : BaseChangeChart B I a) :
    baseChangeChartToAway B I a z ∈ chartRing (I.map (algebraMap A B)) (algebraMap A B a) := by
  induction z using TensorProduct.inductionOn with
  | tmul y c =>
    rw [baseChangeChartToAway_tmul]
    refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ y) ?_
    obtain ⟨n, x, hx, hc⟩ := (mem_chartRing_iff I ha).mp c.2
    rw [hc, awayBaseChange_chartFraction]
    refine chartFraction_mem_chartRing _ ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  | add z z' hz hz' => rw [map_add]; exact Subalgebra.add_mem _ hz hz'

variable (a) in
/-- The map `σ_a : C_a(A, B, I) → B[IB/b]`, `y ⊗ x/a ↦ y·x̄/b`, where `b` is the image of `a` in
`B`. It is a well-defined homomorphism of `B`-algebras by the universal properties of
`A[I/a] ⊆ A_a` and of the tensor product.
(blueprint: `definition-strict-transform--1`,
`definition-strict-transform--1`) -/
noncomputable def strictChartMap (ha : a ∈ I) :
    BaseChangeChart B I a →ₐ[B] chartRing (I.map (algebraMap A B)) (algebraMap A B a) :=
  (baseChangeChartToAway B I a).codRestrict _ (baseChangeChartToAway_mem_chartRing B I a ha)

/-- The defining formula of `σ_a` on pure tensors of chart generators: `σ_a(y ⊗ x/a) = y·x̄/b`.
(blueprint: `definition-strict-transform--1`) -/
lemma coe_strictChartMap_tmul (ha : a ∈ I) (y : B) (x : A)
    (hx : chartFraction a 1 x ∈ chartRing I a) :
    (strictChartMap B I a ha (y ⊗ₜ ⟨chartFraction a 1 x, hx⟩) :
      Localization.Away (algebraMap A B a)) =
      algebraMap B _ y * chartFraction (algebraMap A B a) 1 (algebraMap A B x) := by
  change baseChangeChartToAway B I a _ = _
  rw [baseChangeChartToAway_tmul, awayBaseChange_chartFraction]

lemma coe_strictChartMap (ha : a ∈ I) (z : BaseChangeChart B I a) :
    (strictChartMap B I a ha z : Localization.Away (algebraMap A B a)) =
      baseChangeChartToAway B I a z :=
  rfl

/-- **`σ_a` is surjective**: the chart ring `B[IB/b]` is generated over `B` by the fractions
`ȳ/b`, `y ∈ IB`, all of which lie in the image of `σ_a`.
(blueprint: `definition-strict-transform--1`) -/
theorem strictChartMap_surjective (ha : a ∈ I) :
    Function.Surjective (strictChartMap B I a ha) := by
  rw [← AlgHom.range_eq_top, eq_top_iff]
  rintro ⟨z, hz⟩ -
  -- the image of `σ_a` in `B_b`
  set R : Subalgebra B (Localization.Away (algebraMap A B a)) :=
    (baseChangeChartToAway B I a).range with hR
  suffices hzR : z ∈ R by
    obtain ⟨w, hw⟩ := hzR
    exact ⟨w, Subtype.ext hw⟩
  refine (Algebra.adjoin_le ?_ : chartRing (I.map (algebraMap A B)) (algebraMap A B a) ≤ R) hz
  rintro _ ⟨⟨y, hy⟩, rfl⟩
  simp only
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    have hx1 : x ∈ I ^ 1 := by rwa [pow_one]
    refine (AlgHom.mem_range _).mpr
      ⟨1 ⊗ₜ ⟨chartFraction a 1 x, chartFraction_mem_chartRing I hx1⟩, ?_⟩
    rw [baseChangeChartToAway_tmul, map_one, one_mul]
    exact awayBaseChange_chartFraction B a 1 x
  | zero =>
    have h0 : chartFraction (algebraMap A B a) 1 (0 : B) = 0 := Localization.mk_zero _
    rw [h0]
    exact zero_mem R
  | add y y' _ _ hy hy' =>
    rw [chartFraction_add]
    exact add_mem hy hy'
  | smul c y _ hy =>
    have : chartFraction (algebraMap A B a) 1 (c • y) =
        algebraMap B _ c * chartFraction (algebraMap A B a) 1 y := by
      rw [← chartFraction_zero, smul_eq_mul, ← chartFraction_mul, zero_add]
    rw [this]
    exact mul_mem (Subalgebra.algebraMap_mem R c) hy

/-- **The kernel of `σ_a` is the `a`-power torsion** of `C_a(A, B, I)`: an element killed by
`σ_a` becomes an element `w ∈ B` after multiplication by a power of `a`, and `w/1 = 0` in `B_b`
means that `w` is killed by a power of `b`.
(blueprint: `definition-strict-transform--1`) -/
theorem ker_strictChartMap (ha : a ∈ I) :
    RingHom.ker (strictChartMap B I a ha) = baseChangeChartTorsion B I a := by
  ext z
  rw [RingHom.mem_ker, Submodule.mem_powTorsion_iff, ← Subtype.coe_inj, coe_strictChartMap,
    ZeroMemClass.coe_zero]
  have hσ : ∀ z : BaseChangeChart B I a, ∀ n : ℕ,
      baseChangeChartToAway B I a (algebraMap A _ a ^ n * z) =
        algebraMap B _ (algebraMap A B a) ^ n * baseChangeChartToAway B I a z := by
    intro z n
    rw [map_mul, map_pow, baseChangeChartToAway_algebraMap, ← IsScalarTower.algebraMap_apply]
  constructor
  · intro hz
    obtain ⟨N, w, hw⟩ := exists_pow_mul_eq_algebraMap B I ha z
    have h1 := hσ z N
    rw [hz, mul_zero, hw, AlgHom.commutes] at h1
    obtain ⟨⟨_, M, rfl⟩, hM⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap A B a)) _ _).mp h1
    refine ⟨M + N, ?_⟩
    simp only at hM
    rw [smul_eq_mul, pow_add, mul_assoc, hw, ← map_pow,
      IsScalarTower.algebraMap_apply A B (BaseChangeChart B I a), ← map_mul, map_pow, hM, map_zero]
  · rintro ⟨n, hn⟩
    have h1 := hσ z n
    rw [← smul_eq_mul, hn, map_zero] at h1
    have hu : IsUnit (algebraMap B (Localization.Away (algebraMap A B a)) (algebraMap A B a) ^ n) :=
      (IsLocalization.Away.algebraMap_isUnit _).pow n
    exact (hu.mul_right_eq_zero).mp h1.symm

/-- The comparison `σ̄_a : C_a^st(A, B, I) → B[IB/b]` induced by `σ_a` on the quotient by the
`a`-power torsion. (blueprint: `definition-strict-transform--1`) -/
noncomputable def strictChartComparison (ha : a ∈ I) :
    StrictChart B I a →ₐ[B] chartRing (I.map (algebraMap A B)) (algebraMap A B a) :=
  Ideal.Quotient.liftₐ _ (strictChartMap B I a ha) fun z hz ↦ by
    rw [← RingHom.mem_ker, ← ker_strictChartMap B I ha] at *
    exact hz

@[simp]
lemma strictChartComparison_mk (ha : a ∈ I) (z : BaseChangeChart B I a) :
    strictChartComparison B I ha (Ideal.Quotient.mk _ z) = strictChartMap B I a ha z :=
  rfl

/-- **The strict-transform chart comparison is a ring isomorphism**
`σ̄_a : C_a^st(A, B, I) ≃ B[IB/b]`: `σ_a` is surjective and its kernel is exactly the ideal
by which `C_a(A, B, I)` is divided. (blueprint: `definition-strict-transform--1`) -/
theorem strictChartComparison_bijective (ha : a ∈ I) :
    Function.Bijective (strictChartComparison B I ha) := by
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [strictChartComparison_mk, ← RingHom.mem_ker, ker_strictChartMap] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
  · intro w
    obtain ⟨z, rfl⟩ := strictChartMap_surjective B I ha w
    exact ⟨_, strictChartComparison_mk B I ha z⟩

/-- The strict-transform chart comparison `σ̄_a` as an isomorphism of `B`-algebras
`C_a^st(A, B, I) ≃ B[IB/b]`. (blueprint: `definition-strict-transform--1`) -/
noncomputable def strictChartEquiv (ha : a ∈ I) :
    StrictChart B I a ≃ₐ[B] chartRing (I.map (algebraMap A B)) (algebraMap A B a) :=
  AlgEquiv.ofBijective (strictChartComparison B I ha) (strictChartComparison_bijective B I ha)

@[simp]
lemma strictChartEquiv_apply (ha : a ∈ I) (z : StrictChart B I a) :
    strictChartEquiv B I ha z = strictChartComparison B I ha z :=
  rfl

/-! ### Functoriality and localization of the strict-transform charts -/

section Functoriality

variable {B} {B' B'' : Type u} [CommRing B'] [Algebra A B'] [CommRing B''] [Algebra A B'']
  (φ : B →ₐ[A] B') (ψ : B' →ₐ[A] B'')

lemma isUnit_algebraMap_algHom :
    IsUnit (((algebraMap B' (Localization.Away (algebraMap A B' a))).comp φ.toRingHom)
      (algebraMap A B a)) := by
  simpa using IsLocalization.Away.algebraMap_isUnit (algebraMap A B' a)

variable (a) in
/-- The map `B_b → B'_{b'}` induced by a map `φ : B → B'` of `A`-algebras, where `b` and `b'` are
the images of `a`. -/
noncomputable def awayMapOfAlgHom :
    Localization.Away (algebraMap A B a) →+* Localization.Away (algebraMap A B' a) :=
  Localization.awayLift ((algebraMap B' _).comp φ.toRingHom) (algebraMap A B a)
    (isUnit_algebraMap_algHom φ)

@[simp]
lemma awayMapOfAlgHom_algebraMap (y : B) :
    awayMapOfAlgHom a φ (algebraMap B _ y) = algebraMap B' _ (φ y) :=
  IsLocalization.Away.lift_eq (algebraMap A B a) (isUnit_algebraMap_algHom φ) y

lemma awayMapOfAlgHom_awayBaseChange (c : Localization.Away a) :
    awayMapOfAlgHom a φ (awayBaseChange B a c) = awayBaseChange B' a c := by
  have : (awayMapOfAlgHom a φ).comp (awayBaseChange B a).toRingHom =
      (awayBaseChange B' a).toRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers a) (RingHom.ext fun r ↦ ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes]
    have h := awayMapOfAlgHom_algebraMap (a := a) φ (algebraMap A B r)
    rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes, ← IsScalarTower.algebraMap_apply] at h
    exact h
  exact DFunLike.congr_fun this c

variable (a) in
/-- The functoriality `C_a(A, B, I) → C_a(A, B', I)` of the base-change chart ring along a map
`φ : B → B'` of `A`-algebras. -/
noncomputable def BaseChangeChart.map : BaseChangeChart B I a →ₐ[A] BaseChangeChart B' I a :=
  Algebra.TensorProduct.map φ (AlgHom.id A _)

@[simp]
lemma BaseChangeChart.map_tmul (y : B) (c : chartRing I a) :
    BaseChangeChart.map I a φ (y ⊗ₜ c) = φ y ⊗ₜ c :=
  rfl

lemma BaseChangeChart.map_algebraMap (y : B) :
    BaseChangeChart.map I a φ (algebraMap B _ y) = algebraMap B' _ (φ y) := by
  simp [Algebra.TensorProduct.algebraMap_apply]

lemma baseChangeChartToAway_map (z : BaseChangeChart B I a) :
    baseChangeChartToAway B' I a (BaseChangeChart.map I a φ z) =
      awayMapOfAlgHom a φ (baseChangeChartToAway B I a z) := by
  induction z using TensorProduct.inductionOn with
  | tmul y c =>
    rw [BaseChangeChart.map_tmul, baseChangeChartToAway_tmul, baseChangeChartToAway_tmul, map_mul,
      awayMapOfAlgHom_algebraMap, awayMapOfAlgHom_awayBaseChange]
  | add z z' hz hz' => simp only [map_add, hz, hz']

lemma baseChangeChartTorsion_le_comap :
    baseChangeChartTorsion B I a ≤
      (baseChangeChartTorsion B' I a).comap (BaseChangeChart.map I a φ) := by
  intro z hz
  obtain ⟨n, hn⟩ := Submodule.mem_powTorsion_iff.mp hz
  refine Submodule.mem_powTorsion_iff.mpr ⟨n, ?_⟩
  rw [smul_eq_mul] at hn ⊢
  rw [← AlgHom.commutes (BaseChangeChart.map I a φ), ← map_pow, ← map_mul, hn, map_zero]

variable (a) in
/-- The functoriality `C_a^st(A, B, I) → C_a^st(A, B', I)` of the strict-transform chart ring along
a map `φ : B → B'` of `A`-algebras. For a localization `B → B_s` these are the localization maps
of the strict-transform charts, and they are compatible with composition
(`AlgebraicGeometry.AffineBlowup.StrictChart.map_comp`). -/
noncomputable def StrictChart.map : StrictChart B I a →ₐ[A] StrictChart B' I a :=
  Ideal.quotientMapₐ _ (BaseChangeChart.map I a φ) (baseChangeChartTorsion_le_comap I φ)

@[simp]
lemma StrictChart.map_mk (z : BaseChangeChart B I a) :
    StrictChart.map I a φ (Ideal.Quotient.mk _ z) =
      Ideal.Quotient.mk _ (BaseChangeChart.map I a φ z) :=
  rfl

lemma StrictChart.map_algebraMap (y : B) :
    StrictChart.map I a φ (algebraMap B _ y) = algebraMap B' _ (φ y) := by
  change StrictChart.map I a φ (Ideal.Quotient.mk _ (algebraMap B _ y)) =
    Ideal.Quotient.mk _ (algebraMap B' _ (φ y))
  rw [StrictChart.map_mk, BaseChangeChart.map_algebraMap]

variable (a) in
lemma StrictChart.map_id : StrictChart.map I a (AlgHom.id A B) = AlgHom.id A _ := by
  ext z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [StrictChart.map_mk, AlgHom.id_apply]
  congr 1
  induction z using TensorProduct.inductionOn with
  | tmul y c => rfl
  | add z z' hz hz' => rw [map_add, hz, hz']

variable (a) in
/-- **Compatibility of the strict-transform chart maps with composition**: for localizations
this says that localizing successively at `s` and `t` agrees with localizing at the composite.
(blueprint: `definition-strict-transform--1`, compatibility clause) -/
lemma StrictChart.map_comp :
    StrictChart.map I a (ψ.comp φ) = (StrictChart.map I a ψ).comp (StrictChart.map I a φ) := by
  ext z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [AlgHom.comp_apply, StrictChart.map_mk, StrictChart.map_mk, StrictChart.map_mk]
  congr 1
  induction z using TensorProduct.inductionOn with
  | tmul y c => rfl
  | add z z' hz hz' => rw [map_add, hz, hz', map_add, map_add]

/-- **Naturality of the strict-transform chart comparison**: the comparison `σ̄_a` for `B'`
composed with the chart map `C_a^st(A, B, I) → C_a^st(A, B', I)` is the comparison `σ̄_a` for `B`
followed by `B_b → B'_{b'}`. For a localization `B → B_s` this says that the comparison constructed
from the localized data is the localization of `σ̄_a`.
(blueprint: `definition-strict-transform--1`) -/
theorem strictChartComparison_map (ha : a ∈ I) (z : StrictChart B I a) :
    (strictChartComparison B' I ha (StrictChart.map I a φ z) :
      Localization.Away (algebraMap A B' a)) =
      awayMapOfAlgHom a φ (strictChartComparison B I ha z) := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [StrictChart.map_mk, strictChartComparison_mk, strictChartComparison_mk, coe_strictChartMap,
    coe_strictChartMap, baseChangeChartToAway_map]

end Functoriality

section Localization

variable {B} (s : B)

/-- The localization map `B → B_s` as a map of `A`-algebras. -/
noncomputable abbrev awayAlgHom : B →ₐ[A] Localization.Away s :=
  IsScalarTower.toAlgHom A B (Localization.Away s)

@[simp]
lemma awayAlgHom_apply (y : B) : awayAlgHom (A := A) s y = algebraMap B (Localization.Away s) y :=
  rfl

/-- Every element of `C_a(A, B_s, I)` comes from `C_a(A, B, I)` after multiplication by a power of
`s`. -/
lemma exists_pow_mul_eq_map (z : BaseChangeChart (Localization.Away s) I a) :
    ∃ (n : ℕ) (w : BaseChangeChart B I a),
      algebraMap (Localization.Away s) _ (algebraMap B _ s) ^ n * z =
        BaseChangeChart.map I a (awayAlgHom s) w := by
  induction z using TensorProduct.inductionOn with
  | tmul y c =>
    obtain ⟨⟨y₀, t⟩, hy⟩ := IsLocalization.surj (Submonoid.powers s) y
    obtain ⟨n, hn⟩ := t.2
    simp only at hn hy
    refine ⟨n, y₀ ⊗ₜ c, ?_⟩
    rw [BaseChangeChart.map_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_pow, hn, mul_comm]
    exact congrArg (· ⊗ₜ c) hy
  | add z z' hz hz' =>
    obtain ⟨n, w, hw⟩ := hz
    obtain ⟨n', w', hw'⟩ := hz'
    refine ⟨n + n', algebraMap B _ s ^ n' * w + algebraMap B _ s ^ n * w', ?_⟩
    rw [mul_add, pow_add, mul_right_comm, hw, mul_assoc, hw', map_add, map_mul, map_mul,
      map_pow, map_pow, BaseChangeChart.map_algebraMap, awayAlgHom_apply]
    ring

/-- An element of `B_b` killed by `B_b → (B_s)_{b'}` is killed by a power of `s`. -/
lemma exists_pow_mul_eq_zero_of_awayMapOfAlgHom_eq_zero {x : Localization.Away (algebraMap A B a)}
    (hx : awayMapOfAlgHom a (awayAlgHom s) x = 0) :
    ∃ n : ℕ, algebraMap B _ s ^ n * x = 0 := by
  obtain ⟨⟨w, ⟨_, m, rfl⟩⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers (algebraMap A B a)) x
  simp only at hx ⊢
  have hspec := IsLocalization.mk'_spec (Localization.Away (algebraMap A B a)) w
    (⟨_, m, rfl⟩ : Submonoid.powers (algebraMap A B a))
  have h2 := congrArg (awayMapOfAlgHom a (awayAlgHom s)) hspec
  rw [map_mul, hx, zero_mul, awayMapOfAlgHom_algebraMap] at h2
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (algebraMap A (Localization.Away s) a)) _ _).mp h2.symm
  have hk' : algebraMap B (Localization.Away s) ((algebraMap A B a) ^ k * w) = 0 := by
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
    exact hk
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers s) _ _).mp hk'
  refine ⟨n, ?_⟩
  have hu : IsUnit (algebraMap B (Localization.Away (algebraMap A B a)) ((algebraMap A B a) ^ m)) :=
    by rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit _).pow m
  apply hu.mul_left_eq_zero.mp
  rw [mul_assoc, hspec, ← map_pow, ← map_mul]
  exact (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap A B a)) _ _).mpr
    ⟨⟨_, k, rfl⟩, by linear_combination hn⟩

variable (a)

/-- The localization map `C_a^st(A, B, I) → C_a^st(A, B_s, I)` of the strict-transform chart
at `s ∈ B`. -/
noncomputable abbrev strictChartAwayMap :
    StrictChart B I a →ₐ[A] StrictChart (Localization.Away s) I a :=
  StrictChart.map I a (awayAlgHom s)

variable {a}

/-- An element of `C_a^st(A, B, I)` killed by the localization map at `s` is killed by a power of
`s`. -/
lemma exists_pow_mul_eq_zero_of_strictChartAwayMap_eq_zero (ha : a ∈ I) {z : StrictChart B I a}
    (hz : strictChartAwayMap I a s z = 0) : ∃ n : ℕ, algebraMap B _ s ^ n * z = 0 := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [StrictChart.map_mk, Ideal.Quotient.eq_zero_iff_mem, ← ker_strictChartMap _ I ha,
    RingHom.mem_ker, ← Subtype.coe_inj, coe_strictChartMap, ZeroMemClass.coe_zero,
    baseChangeChartToAway_map] at hz
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_awayMapOfAlgHom_eq_zero s hz
  refine ⟨n, ?_⟩
  have h : algebraMap B (StrictChart B I a) s ^ n * Ideal.Quotient.mk _ z =
      Ideal.Quotient.mk _ (algebraMap B (BaseChangeChart B I a) s ^ n * z) := by
    rw [map_mul, map_pow]
    rfl
  rw [h, Ideal.Quotient.eq_zero_iff_mem, ← ker_strictChartMap _ I ha, RingHom.mem_ker,
    ← Subtype.coe_inj, coe_strictChartMap, ZeroMemClass.coe_zero, map_mul, map_pow,
    AlgHom.commutes, hn]

/-- **Localization of the strict-transform chart** at `s ∈ B`: the chart map
`C_a^st(A, B, I) → C_a^st(A, B_s, I)` is a localization away from `s`, i.e. the canonical map
`(C_a^st(A, B, I))_s → C_a^st(A, B_s, I)` is an isomorphism.
(blueprint: `definition-strict-transform--1`) -/
theorem StrictChart.isLocalization_away (ha : a ∈ I) :
    letI := (strictChartAwayMap I a s).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap B (StrictChart B I a) s)
      (StrictChart (Localization.Away s) I a) := by
  let := (strictChartAwayMap I a s).toRingHom.toAlgebra
  have halg : ∀ z, algebraMap (StrictChart B I a) (StrictChart (Localization.Away s) I a) z =
      strictChartAwayMap I a s z := fun _ ↦ rfl
  have hs : ∀ n : ℕ, strictChartAwayMap I a s (algebraMap B (StrictChart B I a) s ^ n) =
      Ideal.Quotient.mk _ (algebraMap (Localization.Away s) (BaseChangeChart _ I a)
        (algebraMap B _ s) ^ n) := by
    intro n
    rw [map_pow, StrictChart.map_algebraMap, map_pow]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [halg, hs, map_pow]
    exact ((IsLocalization.Away.algebraMap_isUnit s).map
      (algebraMap (Localization.Away s) (StrictChart (Localization.Away s) I a))).pow n
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨n, w, hw⟩ := exists_pow_mul_eq_map I s z
    refine ⟨⟨Ideal.Quotient.mk _ w, ⟨_, n, rfl⟩⟩, ?_⟩
    change Ideal.Quotient.mk _ z * strictChartAwayMap I a s (algebraMap B _ s ^ n) =
      strictChartAwayMap I a s (Ideal.Quotient.mk _ w)
    rw [hs, ← map_mul, mul_comm, hw, StrictChart.map_mk]
  · intro x y hxy
    rw [halg, halg, ← sub_eq_zero, ← map_sub] at hxy
    obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_strictChartAwayMap_eq_zero I s ha hxy
    exact ⟨⟨_, n, rfl⟩, by rw [← sub_eq_zero, ← mul_sub, hn]⟩

/-- The canonical isomorphism `(C_a^st(A, B, I))_s ≅ C_a^st(A, B_s, I)` between the localization
of the strict-transform chart ring and the strict-transform chart ring of the localized data.
(blueprint: `definition-strict-transform--1`) -/
noncomputable def strictChartLocalizationEquiv (ha : a ∈ I) :
    Localization.Away (algebraMap B (StrictChart B I a) s) ≃+*
      StrictChart (Localization.Away s) I a :=
  letI := (strictChartAwayMap I a s).toRingHom.toAlgebra
  haveI := StrictChart.isLocalization_away I s ha
  (IsLocalization.algEquiv (Submonoid.powers (algebraMap B (StrictChart B I a) s))
    (Localization.Away (algebraMap B (StrictChart B I a) s))
    (StrictChart (Localization.Away s) I a)).toRingEquiv

@[simp]
lemma strictChartLocalizationEquiv_algebraMap (ha : a ∈ I) (z : StrictChart B I a) :
    strictChartLocalizationEquiv I s ha (algebraMap _ _ z) = strictChartAwayMap I a s z := by
  let := (strictChartAwayMap I a s).toRingHom.toAlgebra
  have := StrictChart.isLocalization_away I s ha
  exact AlgEquiv.commutes _ z

/-- The localized strict-transform chart comparison `(σ̄_a)_s`: the localization at `s` of the
comparison `σ̄_a : C_a^st(A, B, I) → B_b`, with values in `(B_s)_{b'}`.
(blueprint: `definition-strict-transform--1`) -/
noncomputable def strictChartComparisonAway (ha : a ∈ I) :
    Localization.Away (algebraMap B (StrictChart B I a) s) →+*
      Localization.Away (algebraMap A (Localization.Away s) a) :=
  Localization.awayLift ((awayMapOfAlgHom a (awayAlgHom s)).comp
    ((chartRing _ _).val.toRingHom.comp (strictChartComparison B I ha).toRingHom))
    (algebraMap B _ s) (by
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.commutes, Subalgebra.coe_val, Subalgebra.coe_algebraMap,
        awayMapOfAlgHom_algebraMap, awayAlgHom_apply]
      rw [IsScalarTower.algebraMap_apply B (Localization.Away s)]
      exact (IsLocalization.Away.algebraMap_isUnit s).map _)

/-- **The localized comparison is the comparison of the localized data**: `(σ̄_a)_s` agrees with
the strict-transform chart comparison `σ̄_a` constructed directly from `A → B_s`, transported along
`(C_a^st(A, B, I))_s ≅ C_a^st(A, B_s, I)`.
(blueprint: `definition-strict-transform--1`) -/
theorem strictChartComparisonAway_eq (ha : a ∈ I) :
    strictChartComparisonAway I s ha =
      ((chartRing _ _).val.toRingHom.comp
        (strictChartComparison (Localization.Away s) I ha).toRingHom).comp
        (strictChartLocalizationEquiv I s ha).toRingHom := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap B (StrictChart B I a) s))
    (RingHom.ext fun z ↦ ?_)
  simp only [strictChartComparisonAway, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, strictChartLocalizationEquiv_algebraMap]
  rw [Localization.awayLift, IsLocalization.Away.lift_eq]
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Subalgebra.coe_val]
  exact (strictChartComparison_map I (awayAlgHom s) ha z).symm

end Localization

end AlgebraicGeometry.AffineBlowup
