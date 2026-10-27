import Langlands.Geometry.Analytic.StrictTestDomain.FiniteRationalTensorComparisonStatement
import Langlands.Geometry.Analytic.ClosedSubmodulesBanach
import Langlands.Geometry.Analytic.FiniteBanachModule
import Langlands.Geometry.Analytic.AffinoidPowerBounds
import Langlands.Geometry.Analytic.SpectrumNonemptyProof
import Langlands.Geometry.Analytic.TateNoetherian
import Mathlib.Topology.MetricSpace.Ultra.Pi

/-! # Finite rational tensor comparison: proof -/

noncomputable section

open scoped TensorProduct

universe u v

namespace Langlands.Analytic

namespace PresentedStrictAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- Over a coefficient field whose norm is at most one, every nonzero tuple of
an actual presented quotient has finite product norm at least one. -/
theorem one_le_norm_pi_of_scalar_norm_le_one (P : PresentedStrictAffinoidAlgebra K)
    (hK : ∀ c : K, ‖c‖ ≤ 1) {m : ℕ} {x : Fin m → P} (hx : x ≠ 0) : 1 ≤ ‖x‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact (one_le_norm_of_scalar_norm_le_one P hK hi).trans (norm_le_pi_norm x i)

/-- Over a coefficient field whose norm is at most one, the finite product norm
of every tuple of an actual presented quotient is at most one. -/
theorem norm_pi_le_one_of_scalar_norm_le_one (P : PresentedStrictAffinoidAlgebra K)
    (hK : ∀ c : K, ‖c‖ ≤ 1) {m : ℕ} (x : Fin m → P) : ‖x‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i =>
    norm_le_one_of_scalar_norm_le_one P hK (x i)

/-- Over a coefficient field whose norm is at most one, every subset of a
finite product of an actual presented quotient is closed: distinct points
have distance at least one. -/
theorem isClosed_pi_of_scalar_norm_le_one (P : PresentedStrictAffinoidAlgebra K)
    (hK : ∀ c : K, ‖c‖ ≤ 1) {m : ℕ} (S : Set (Fin m → P)) : IsClosed S := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx 1 one_pos
  by_cases h : x - y = 0
  · rwa [sub_eq_zero.mp h]
  · have := one_le_norm_pi_of_scalar_norm_le_one P hK h
    rw [dist_eq_norm] at hxy
    linarith

variable [CompleteSpace K]

/-- Every submodule of a finite product of an actual presented strict affinoid
algebra is closed, over every complete ultrametric coefficient field. -/
theorem isClosed_submodule_pi (P : PresentedStrictAffinoidAlgebra K) {m : ℕ}
    (S : Submodule P (Fin m → P)) : IsClosed (S : Set (Fin m → P)) := by
  by_cases hK : ∀ c : K, ‖c‖ ≤ 1
  · exact isClosed_pi_of_scalar_norm_le_one P hK _
  push Not at hK
  let _ : NontriviallyNormedField K :=
    { toNormedField := inferInstance, non_trivial := hK }
  exact isClosed_submodule_pi_of_noetherian_banach (K := K) S

end PresentedStrictAffinoidAlgebra

namespace BoundedAlgHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P Q : PresentedStrictAffinoidAlgebra K}

/-- A generating tuple of a finite bounded map of actual presented strict
affinoid algebras admits coefficients with a uniform norm bound. -/
theorem exists_coefficientMap_preimage_norm_le (φ : BoundedAlgHom K P Q) {n : ℕ}
    (c : Fin n → Q) (hc : Function.Surjective (φ.coefficientMap c)) :
    ∃ D > 0, ∀ q : Q, ∃ a : Fin n → P, φ.coefficientMap c a = q ∧ ‖a‖ ≤ D * ‖q‖ := by
  by_cases hK : ∀ c : K, ‖c‖ ≤ 1
  · refine ⟨1, one_pos, fun q => ?_⟩
    by_cases hq : q = 0
    · exact ⟨0, by rw [hq, map_zero], by simp [hq]⟩
    · obtain ⟨a, ha⟩ := hc q
      refine ⟨a, ha, ?_⟩
      rw [one_mul]
      exact (PresentedStrictAffinoidAlgebra.norm_pi_le_one_of_scalar_norm_le_one P hK a).trans
        (PresentedStrictAffinoidAlgebra.one_le_norm_of_scalar_norm_le_one Q hK hq)
  push Not at hK
  let _ : NontriviallyNormedField K :=
    { toNormedField := inferInstance, non_trivial := hK }
  exact φ.coefficientMap_exists_preimage_norm_le c hc

end BoundedAlgHom

section QuotientNorm

variable {R W : Type*} [Ring R] [SeminormedAddCommGroup W] [Module R W]

/-- A bound valid for every representative passes to the quotient norm. -/
theorem le_mul_norm_quotient_of_forall_mk {S : Submodule R W} (v : W ⧸ S) {g C : ℝ}
    (hC : 0 ≤ C) (h : ∀ w : W, Submodule.Quotient.mk w = v → g ≤ C * ‖w‖) :
    g ≤ C * ‖v‖ := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hε : 0 < δ / (C + 1) := by positivity
  obtain ⟨w, hw, hwn⟩ := Submodule.Quotient.norm_mk_lt v hε
  calc
    g ≤ C * ‖w‖ := h w hw
    _ ≤ C * (‖v‖ + δ / (C + 1)) := mul_le_mul_of_nonneg_left hwn.le hC
    _ = C * ‖v‖ + C * (δ / (C + 1)) := by ring
    _ ≤ C * ‖v‖ + (C + 1) * (δ / (C + 1)) := by gcongr; linarith
    _ = C * ‖v‖ + δ := by field_simp

/-- The two-variable form of `le_mul_norm_quotient_of_forall_mk`. -/
theorem le_mul_norm_mul_norm_quotient_of_forall_mk {S : Submodule R W} (v₁ v₂ : W ⧸ S)
    {g C : ℝ} (hC : 0 ≤ C)
    (h : ∀ w₁ w₂ : W, Submodule.Quotient.mk w₁ = v₁ → Submodule.Quotient.mk w₂ = v₂ →
      g ≤ C * (‖w₁‖ * ‖w₂‖)) :
    g ≤ C * (‖v₁‖ * ‖v₂‖) := by
  have h₂ : ∀ w₂ : W, Submodule.Quotient.mk w₂ = v₂ → g ≤ (C * ‖v₁‖) * ‖w₂‖ := by
    intro w₂ hw₂
    have h₁ : g ≤ (C * ‖w₂‖) * ‖v₁‖ :=
      le_mul_norm_quotient_of_forall_mk v₁ (by positivity) fun w₁ hw₁ => by
        rw [show C * ‖w₂‖ * ‖w₁‖ = C * (‖w₁‖ * ‖w₂‖) by ring]
        exact h w₁ w₂ hw₁ hw₂
    calc
      g ≤ C * ‖w₂‖ * ‖v₁‖ := h₁
      _ = C * ‖v₁‖ * ‖w₂‖ := by ring
  calc
    g ≤ C * ‖v₁‖ * ‖v₂‖ := le_mul_norm_quotient_of_forall_mk v₂ (by positivity) h₂
    _ = C * (‖v₁‖ * ‖v₂‖) := by ring

/-- Quotients of ultrametric seminormed groups by submodules are ultrametric. -/
theorem isUltrametricDist_submoduleQuotient [IsUltrametricDist W] (S : Submodule R W) :
    IsUltrametricDist (W ⧸ S) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨a, rfl, ha⟩ := Submodule.Quotient.norm_mk_lt x hε
    obtain ⟨b, rfl, hb⟩ := Submodule.Quotient.norm_mk_lt y hε
    calc
      ‖(Submodule.Quotient.mk a : W ⧸ S) + Submodule.Quotient.mk b‖ ≤ ‖a + b‖ := by
        rw [← Submodule.Quotient.mk_add]
        exact Submodule.Quotient.norm_mk_le S _
      _ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max (‖(Submodule.Quotient.mk a : W ⧸ S)‖ + ε)
          (‖(Submodule.Quotient.mk b : W ⧸ S)‖ + ε) := max_le_max ha.le hb.le
      _ = _ := max_add_add_right _ _ _

end QuotientNorm

/-- `Finset.mul_sum` stated over an arbitrary commutative ring, so that its
instance paths are those found by instance search. -/
private theorem mul_sum_fin {R : Type*} [CommRing R] {n : ℕ} (a : R) (f : Fin n → R) :
    a * ∑ k, f k = ∑ k, a * f k :=
  Finset.mul_sum _ _ _

/-- `Finset.sum_mul_sum` stated over an arbitrary commutative ring. -/
private theorem sum_mul_sum_fin {R : Type*} [CommRing R] {n : ℕ} (f g : Fin n → R) :
    (∑ i, f i) * ∑ j, g j = ∑ i, ∑ j, f i * g j :=
  Finset.sum_mul_sum _ _ _ _

namespace StrictTestDomain.RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P Q : PresentedStrictAffinoidAlgebra K} (d : RationalData K P)
  (φ : BoundedAlgHom K P Q)

/-- Induction over the ordinary tensor product through products of the two
actual factor maps. -/
@[elab_as_elim]
theorem algebraicBaseChange_induction {motive : d.algebraicBaseChange φ → Prop}
    (m : d.algebraicBaseChange φ)
    (mul : ∀ (x : d.algebra) (y : Q), motive (d.tensorLeft φ x * d.tensorRight φ y))
    (add : ∀ m m', motive m → motive m' → motive (m + m')) : motive m := by
  let : Algebra P d.algebra := d.baseMap.toAlgHom.toRingHom.toAlgebra
  let : Algebra P Q := φ.toAlgHom.toRingHom.toAlgebra
  change d.algebra ⊗[P] Q at m
  induction m using TensorProduct.inductionOn with
  | tmul x y =>
    have h : (x ⊗ₜ[P] y : d.algebra ⊗[P] Q) = d.tensorLeft φ x * d.tensorRight φ y := by
      change _ = (x ⊗ₜ[P] (1 : Q)) * ((1 : d.algebra) ⊗ₜ[P] y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h]
    exact mul x y
  | add m m' hm hm' => exact add m m' hm hm'

theorem tensorRight_apply_map (x : P) :
    d.tensorRight φ (φ x) = d.tensorLeft φ (d.baseMap x) :=
  (RingHom.congr_fun (d.tensorLeft_comp_baseMap φ) x).symm

/-- The bounded pushout criterion: if the ordinary tensor product is
isomorphic to a complete ultrametric normed algebra in which both factor maps
are bounded, and the comparison is bounded for that norm, then the comparison
is bijective. -/
theorem bijective_tensorComparison_of_normedModel {E : Type v} [NormedCommRing E]
    [IsUltrametricDist E] [NormedAlgebra K E] [CompleteSpace E]
    (ι : d.algebraicBaseChange φ ≃+* E)
    (hK : ∀ k : K, ι (d.tensorLeft φ (algebraMap K d.algebra k)) = algebraMap K E k)
    (hleft : ∃ C > 0, ∀ x : d.algebra, ‖ι (d.tensorLeft φ x)‖ ≤ C * ‖x‖)
    (hright : ∃ C > 0, ∀ y : Q, ‖ι (d.tensorRight φ y)‖ ≤ C * ‖y‖)
    (hτ : ∃ C > 0, ∀ z : E, ‖d.tensorComparison φ (ι.symm z)‖ ≤ C * ‖z‖) :
    Function.Bijective (d.tensorComparison φ) := by
  let a : BoundedAlgHom K d.algebra E :=
    { toAlgHom :=
        { toRingHom := ι.toRingHom.comp (d.tensorLeft φ)
          commutes' := hK }
      bounded := hleft }
  let b : BoundedAlgHom K Q E :=
    { toAlgHom :=
        { toRingHom := ι.toRingHom.comp (d.tensorRight φ)
          commutes' := fun k => by
            change ι (d.tensorRight φ (algebraMap K Q k)) = _
            rw [← φ.toAlgHom.commutes k]
            change ι (d.tensorRight φ (φ (algebraMap K P k))) = _
            rw [tensorRight_apply_map, ← hK]
            congr 2
            exact d.baseMap.toAlgHom.commutes k }
      bounded := hright }
  have hab : a.comp d.baseMap = b.comp φ := by
    apply BoundedAlgHom.ext
    intro x
    change ι (d.tensorLeft φ (d.baseMap x)) = ι (d.tensorRight φ (φ x))
    rw [tensorRight_apply_map]
  let C := d.extension φ a b hab
  have hCcomp : ∀ x, C (d.comparison φ x) = a x := fun x =>
    congrArg (fun χ : BoundedAlgHom K d.algebra E => χ x)
      (d.extension_comp_comparison φ a b hab)
  have hCbase : ∀ y, C ((d.pullback φ).baseMap y) = b y := fun y =>
    congrArg (fun χ : BoundedAlgHom K Q E => χ y) (d.extension_comp_baseMap φ a b hab)
  have hCτ : ∀ m, C (d.tensorComparison φ m) = ι m := by
    intro m
    induction m using d.algebraicBaseChange_induction φ with
    | mul x y =>
      rw [d.tensorComparison_mul, map_mul, hCcomp, hCbase, map_mul]
      rfl
    | add m m' hm hm' => rw [map_add, map_add, hm, hm', map_add]
  let τ' : BoundedAlgHom K E (d.pullback φ).algebra :=
    { toAlgHom :=
        { toRingHom := (d.tensorComparison φ).comp ι.symm.toRingHom
          commutes' := fun k => by
            change d.tensorComparison φ (ι.symm (algebraMap K E k)) = _
            rw [← hK, RingEquiv.symm_apply_apply, tensorComparison_tensorLeft]
            exact (d.comparison φ).toAlgHom.commutes k }
      bounded := hτ }
  have hτ'C : τ'.comp C = BoundedAlgHom.id K (d.pullback φ).algebra := by
    apply (d.pullback φ).hom_ext
    apply BoundedAlgHom.ext
    intro y
    change d.tensorComparison φ (ι.symm (C ((d.pullback φ).baseMap y))) =
      (d.pullback φ).baseMap y
    rw [hCbase]
    change d.tensorComparison φ (ι.symm (ι (d.tensorRight φ y))) = _
    rw [RingEquiv.symm_apply_apply, tensorComparison_tensorRight]
  constructor
  · intro m m' h
    apply ι.injective
    rw [← hCτ, ← hCτ, h]
  · intro y
    exact ⟨ι.symm (C y), congrArg (fun χ : BoundedAlgHom K _ _ => χ y) hτ'C⟩

section Model

variable {n : ℕ} (c : Fin n → Q)

/-- The coefficient sum `w ↦ ∑ k, w k ⊗ c k` of a tuple in the second factor,
written with the actual factor maps. -/
def coefficientSum : (Fin n → d.algebra) →+ d.algebraicBaseChange φ where
  toFun w := ∑ k, d.tensorLeft φ (w k) * d.tensorRight φ (c k)
  map_zero' := by simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]
  map_add' w w' := by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem coefficientSum_apply (w : Fin n → d.algebra) :
    d.coefficientSum φ c w = ∑ k, d.tensorLeft φ (w k) * d.tensorRight φ (c k) :=
  rfl

theorem coefficientSum_smul (x : d.algebra) (w : Fin n → d.algebra) :
    d.coefficientSum φ c (x • w) = d.tensorLeft φ x * d.coefficientSum φ c w := by
  rw [coefficientSum_apply, coefficientSum_apply, mul_sum_fin]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

/-- Coefficients from the original base give the right factor of their sum. -/
theorem coefficientSum_baseMap (a : Fin n → P) :
    d.coefficientSum φ c (fun k => d.baseMap (a k)) =
      d.tensorRight φ (φ.coefficientMap c a) := by
  rw [coefficientSum_apply, BoundedAlgHom.coefficientMap_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, tensorRight_apply_map]

/-- A generating tuple of the finite map generates the ordinary tensor product
over its left factor. -/
theorem coefficientSum_surjective (hc : Function.Surjective (φ.coefficientMap c)) :
    Function.Surjective (d.coefficientSum φ c) := by
  intro m
  induction m using d.algebraicBaseChange_induction φ with
  | mul x y =>
    obtain ⟨a, rfl⟩ := hc y
    exact ⟨x • fun k => d.baseMap (a k), by
      rw [coefficientSum_smul, coefficientSum_baseMap]⟩
  | add m m' hm hm' =>
    obtain ⟨w, rfl⟩ := hm
    obtain ⟨w', rfl⟩ := hm'
    exact ⟨w + w', map_add _ _ _⟩

/-- Products of coefficient sums, given coefficients `s i j` for the products
of the generators. -/
theorem coefficientSum_mul (s : Fin n → Fin n → Fin n → d.algebra)
    (hs : ∀ i j, d.coefficientSum φ c (s i j) =
      d.tensorRight φ (c i) * d.tensorRight φ (c j))
    (u w : Fin n → d.algebra) :
    d.coefficientSum φ c u * d.coefficientSum φ c w =
      d.coefficientSum φ c (∑ i, ∑ j, (u i * w j) • s i j) := by
  simp only [map_sum, coefficientSum_smul, hs]
  rw [coefficientSum_apply, coefficientSum_apply, sum_mul_sum_fin]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  ring

/-- The kernel of the coefficient sum, as a submodule over the left factor. -/
def coefficientKernel : Submodule d.algebra (Fin n → d.algebra) where
  carrier := {w | d.coefficientSum φ c w = 0}
  add_mem' {w w'} hw hw' := by
    change d.coefficientSum φ c (w + w') = 0
    rw [map_add, hw, hw', add_zero]
  zero_mem' := map_zero _
  smul_mem' x w hw := by
    change d.coefficientSum φ c (x • w) = 0
    rw [coefficientSum_smul, hw, mul_zero]

theorem mem_coefficientKernel {w : Fin n → d.algebra} :
    w ∈ d.coefficientKernel φ c ↔ d.coefficientSum φ c w = 0 :=
  Iff.rfl

/-- The quotient of coefficient tuples by the kernel of the coefficient sum. -/
abbrev CoefficientQuotient := (Fin n → d.algebra) ⧸ d.coefficientKernel φ c

theorem coefficientQuotient_mk_eq_mk_iff {w w' : Fin n → d.algebra} :
    (Submodule.Quotient.mk w : d.CoefficientQuotient φ c) = Submodule.Quotient.mk w' ↔
      d.coefficientSum φ c w = d.coefficientSum φ c w' := by
  rw [Submodule.Quotient.eq, mem_coefficientKernel, map_sub, sub_eq_zero]

variable (hsurj : Function.Surjective (d.coefficientSum φ c))

/-- The additive identification of the ordinary tensor product with the
coefficient quotient, given by any choice of coefficients. -/
def coefficientSection : d.algebraicBaseChange φ →+ d.CoefficientQuotient φ c where
  toFun m := Submodule.Quotient.mk (Function.surjInv hsurj m)
  map_zero' := by
    rw [← Submodule.Quotient.mk_zero, coefficientQuotient_mk_eq_mk_iff,
      Function.surjInv_eq hsurj, map_zero]
  map_add' m m' := by
    rw [← Submodule.Quotient.mk_add, coefficientQuotient_mk_eq_mk_iff, map_add,
      Function.surjInv_eq hsurj, Function.surjInv_eq hsurj, Function.surjInv_eq hsurj]

theorem coefficientSection_eq_mk_iff (m : d.algebraicBaseChange φ) (w : Fin n → d.algebra) :
    d.coefficientSection φ c hsurj m = Submodule.Quotient.mk w ↔
      m = d.coefficientSum φ c w := by
  change Submodule.Quotient.mk _ = _ ↔ _
  rw [coefficientQuotient_mk_eq_mk_iff, Function.surjInv_eq hsurj]

theorem coefficientSection_coefficientSum (w : Fin n → d.algebra) :
    d.coefficientSection φ c hsurj (d.coefficientSum φ c w) = Submodule.Quotient.mk w :=
  (d.coefficientSection_eq_mk_iff φ c hsurj _ w).mpr rfl

theorem coefficientSection_bijective :
    Function.Bijective (d.coefficientSection φ c hsurj) := by
  constructor
  · intro m m' h
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (d.coefficientSection φ c hsurj m')
    rw [← hw] at h
    rw [(d.coefficientSection_eq_mk_iff φ c hsurj m w).mp h,
      (d.coefficientSection_eq_mk_iff φ c hsurj m' w).mp hw.symm]
  · intro v
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact ⟨_, d.coefficientSection_coefficientSum φ c hsurj w⟩

theorem coefficientSection_tensorLeft_mul (x : d.algebra) (m : d.algebraicBaseChange φ) :
    d.coefficientSection φ c hsurj (d.tensorLeft φ x * m) =
      x • d.coefficientSection φ c hsurj m := by
  obtain ⟨w, rfl⟩ := hsurj m
  rw [← coefficientSum_smul, coefficientSection_coefficientSum,
    coefficientSection_coefficientSum, Submodule.Quotient.mk_smul]

theorem coefficientSection_algebraMap_mul (k : K) (m : d.algebraicBaseChange φ) :
    d.coefficientSection φ c hsurj (d.tensorLeft φ (algebraMap K d.algebra k) * m) =
      k • d.coefficientSection φ c hsurj m := by
  rw [coefficientSection_tensorLeft_mul, algebraMap_smul]

omit hsurj in
/-- The left factor acts boundedly on the coefficient quotient. -/
theorem norm_smul_coefficientQuotient_le (x : d.algebra) (v : d.CoefficientQuotient φ c) :
    ‖x • v‖ ≤ ‖x‖ * ‖v‖ :=
  le_mul_norm_quotient_of_forall_mk v (norm_nonneg x) fun w hw => by
    rw [← hw, ← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.norm_mk_le _ _).trans (norm_smul_le x w)

omit hsurj in
/-- Scalars act boundedly on the coefficient quotient. -/
theorem norm_scalar_smul_coefficientQuotient_le (k : K) (v : d.CoefficientQuotient φ c) :
    ‖k • v‖ ≤ ‖k‖ * ‖v‖ :=
  le_mul_norm_quotient_of_forall_mk v (norm_nonneg k) fun w hw => by
    rw [← hw, ← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.norm_mk_le _ _).trans (norm_smul_le k w)

/-- The quotient seminorm is submultiplicative up to the bound `‖μ‖` on the
coefficients of the products of the generators. -/
theorem norm_coefficientSection_mul_le (s : Fin n → Fin n → Fin n → d.algebra)
    (hs : ∀ i j, d.coefficientSum φ c (s i j) =
      d.tensorRight φ (c i) * d.tensorRight φ (c j))
    (μ : K) (hsn : ∀ i j, ‖s i j‖ ≤ ‖μ‖) (x y : d.algebraicBaseChange φ) :
    ‖d.coefficientSection φ c hsurj (x * y)‖ ≤
      ‖μ‖ * (‖d.coefficientSection φ c hsurj x‖ * ‖d.coefficientSection φ c hsurj y‖) := by
  apply le_mul_norm_mul_norm_quotient_of_forall_mk _ _ (norm_nonneg μ)
  intro u w hu hw
  rw [(d.coefficientSection_eq_mk_iff φ c hsurj x u).mp hu.symm,
    (d.coefficientSection_eq_mk_iff φ c hsurj y w).mp hw.symm,
    d.coefficientSum_mul φ c s hs, coefficientSection_coefficientSum]
  refine (Submodule.Quotient.norm_mk_le _ _).trans ?_
  have h0 : 0 ≤ ‖μ‖ * (‖u‖ * ‖w‖) := by positivity
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0
  intro i _
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0
  intro j _
  calc
    ‖(u i * w j) • s i j‖ ≤ ‖u i * w j‖ * ‖s i j‖ := norm_smul_le _ _
    _ ≤ (‖u i‖ * ‖w j‖) * ‖μ‖ :=
      mul_le_mul (norm_mul_le _ _) (hsn i j) (norm_nonneg _) (by positivity)
    _ ≤ (‖u‖ * ‖w‖) * ‖μ‖ := by
      gcongr
      · exact norm_le_pi_norm u i
      · exact norm_le_pi_norm w j
    _ = _ := by ring

/-- The left factor is bounded for the quotient seminorm. -/
theorem norm_coefficientSection_tensorLeft_le (x : d.algebra) :
    ‖d.coefficientSection φ c hsurj (d.tensorLeft φ x)‖ ≤
      ‖d.coefficientSection φ c hsurj 1‖ * ‖x‖ := by
  rw [← mul_one (d.tensorLeft φ x), coefficientSection_tensorLeft_mul, mul_comm]
  exact d.norm_smul_coefficientQuotient_le φ c x _

/-- Bounded coefficient lifts make the right factor bounded for the quotient
seminorm. -/
theorem exists_norm_coefficientSection_tensorRight_le
    (hlift : ∃ D > 0, ∀ q : Q, ∃ a : Fin n → P, φ.coefficientMap c a = q ∧ ‖a‖ ≤ D * ‖q‖) :
    ∃ C > 0, ∀ q : Q, ‖d.coefficientSection φ c hsurj (d.tensorRight φ q)‖ ≤ C * ‖q‖ := by
  obtain ⟨D, hD, hlift⟩ := hlift
  obtain ⟨Cβ, hCβ, hβ⟩ := d.baseMap.bounded
  refine ⟨Cβ * D, by positivity, fun q => ?_⟩
  obtain ⟨a, rfl, han⟩ := hlift q
  rw [← coefficientSum_baseMap, coefficientSection_coefficientSum]
  have hpi : ‖(fun k => d.baseMap (a k))‖ ≤ Cβ * ‖a‖ :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k =>
      (hβ (a k)).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm a k) hCβ.le)
  calc
    ‖(Submodule.Quotient.mk (fun k => d.baseMap (a k)) : d.CoefficientQuotient φ c)‖ ≤
        Cβ * ‖a‖ := (Submodule.Quotient.norm_mk_le _ _).trans hpi
    _ ≤ Cβ * (D * ‖φ.coefficientMap c a‖) := by gcongr
    _ = _ := by ring

/-- The comparison is bounded for the quotient seminorm. -/
theorem exists_norm_tensorComparison_le :
    ∃ C > 0, ∀ m : d.algebraicBaseChange φ,
      ‖d.tensorComparison φ m‖ ≤ C * ‖d.coefficientSection φ c hsurj m‖ := by
  obtain ⟨Cc, hCc, hcomp⟩ := (d.comparison φ).bounded
  let Cb : ℝ := ∑ k, ‖(d.pullback φ).baseMap (c k)‖
  have hCb : 0 ≤ Cb := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨Cc * Cb + 1, by positivity, fun m => ?_⟩
  have key : ‖d.tensorComparison φ m‖ ≤ (Cc * Cb) * ‖d.coefficientSection φ c hsurj m‖ := by
    apply le_mul_norm_quotient_of_forall_mk _ (by positivity)
    intro w hw
    rw [(d.coefficientSection_eq_mk_iff φ c hsurj m w).mp hw.symm, coefficientSum_apply,
      map_sum]
    calc
      ‖∑ k, d.tensorComparison φ (d.tensorLeft φ (w k) * d.tensorRight φ (c k))‖ ≤
          ∑ k, ‖d.tensorComparison φ (d.tensorLeft φ (w k) * d.tensorRight φ (c k))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ k, Cc * ‖w‖ * ‖(d.pullback φ).baseMap (c k)‖ :=
        Finset.sum_le_sum fun k _ => by
          rw [d.tensorComparison_mul]
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            ((hcomp (w k)).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm w k) hCc.le))
            (norm_nonneg _))
      _ = Cc * ‖w‖ * Cb := (Finset.mul_sum _ _ _).symm
      _ = Cc * Cb * ‖w‖ := by ring
  exact key.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
    (norm_nonneg _))

omit hsurj in
/-- The normed model: if the coefficient kernel is closed, the generators have
uniformly bounded coefficient lifts, and their products have coefficients
bounded by `‖μ‖`, then the scaled quotient norm makes the ordinary tensor
product a complete ultrametric normed algebra, and the comparison is bijective. -/
theorem bijective_tensorComparison_of_generators
    (hlift : ∃ D > 0, ∀ q : Q, ∃ a : Fin n → P, φ.coefficientMap c a = q ∧ ‖a‖ ≤ D * ‖q‖)
    (hclosed : IsClosed (d.coefficientKernel φ c : Set (Fin n → d.algebra)))
    (μ : K) (hμ : μ ≠ 0)
    (hstruct : ∀ i j, ∃ s : Fin n → d.algebra,
      d.coefficientSum φ c s = d.tensorRight φ (c i) * d.tensorRight φ (c j) ∧ ‖s‖ ≤ ‖μ‖) :
    Function.Bijective (d.tensorComparison φ) := by
  have hsurj : Function.Surjective (d.coefficientSum φ c) := by
    obtain ⟨D, _, hl⟩ := hlift
    exact d.coefficientSum_surjective φ c fun q => (hl q).imp fun _ h => h.1
  choose s hs hsn using hstruct
  have hμpos : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
  obtain ⟨Cr, hCr, hr⟩ := d.exists_norm_coefficientSection_tensorRight_le φ c hsurj hlift
  obtain ⟨Ct, hCt, ht⟩ := d.exists_norm_tensorComparison_le φ c hsurj
  have hm := d.norm_coefficientSection_mul_le φ c hsurj s hs μ hsn
  have hl := d.norm_coefficientSection_tensorLeft_le φ c hsurj
  have hK := d.coefficientSection_algebraMap_mul φ c hsurj
  have hnK := d.norm_scalar_smul_coefficientQuotient_le φ c
  have : IsClosed (d.coefficientKernel φ c : Set (Fin n → d.algebra)) := hclosed
  have : IsUltrametricDist (d.CoefficientQuotient φ c) :=
    isUltrametricDist_submoduleQuotient _
  let g := d.coefficientSection φ c hsurj
  let f : d.algebraicBaseChange φ ≃+ d.CoefficientQuotient φ c :=
    (AddEquiv.ofBijective g (d.coefficientSection_bijective φ c hsurj)).trans
      (LinearEquiv.smulOfNeZero K (d.CoefficientQuotient φ c) μ hμ).toAddEquiv
  let nG : NormedAddCommGroup (d.algebraicBaseChange φ) :=
    NormedAddCommGroup.induced _ _ f f.injective
  have hnorm : ∀ m : d.algebraicBaseChange φ, ‖m‖ = ‖μ‖ * ‖g m‖ := fun m =>
    norm_smul μ (g m)
  have hmul : ∀ x y : d.algebraicBaseChange φ, ‖x * y‖ ≤ ‖x‖ * ‖y‖ := by
    intro x y
    rw [hnorm, hnorm, hnorm]
    calc
      ‖μ‖ * ‖g (x * y)‖ ≤ ‖μ‖ * (‖μ‖ * (‖g x‖ * ‖g y‖)) :=
        mul_le_mul_of_nonneg_left (hm x y) (norm_nonneg _)
      _ = ‖μ‖ * ‖g x‖ * (‖μ‖ * ‖g y‖) := by ring
  let nR : NormedCommRing (d.algebraicBaseChange φ) :=
    { nG, (inferInstance : CommRing (d.algebraicBaseChange φ)) with
      norm_mul_le := hmul }
  let alg : Algebra K (d.algebraicBaseChange φ) :=
    ((d.tensorLeft φ).comp (algebraMap K d.algebra)).toAlgebra
  let : NormedAlgebra K (d.algebraicBaseChange φ) :=
    { alg with
      norm_smul_le := fun k m => by
        change ‖d.tensorLeft φ (algebraMap K d.algebra k) * m‖ ≤ ‖k‖ * ‖m‖
        rw [hnorm, hnorm, hK]
        calc
          ‖μ‖ * ‖k • g m‖ ≤ ‖μ‖ * (‖k‖ * ‖g m‖) :=
            mul_le_mul_of_nonneg_left (hnK k _) (norm_nonneg _)
          _ = ‖k‖ * (‖μ‖ * ‖g m‖) := by ring }
  let : IsUltrametricDist (d.algebraicBaseChange φ) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
      rw [hnorm, hnorm, hnorm, map_add, ← mul_max_of_nonneg _ _ (norm_nonneg μ)]
      exact mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_add_le_max _ _) (norm_nonneg _)
  have : CompleteSpace (d.algebraicBaseChange φ) := by
    have hiso : Isometry f := AddMonoidHomClass.isometry_of_norm f fun _ => rfl
    rw [completeSpace_iff_isComplete_range hiso.isUniformInducing, f.surjective.range_eq]
    exact isComplete_univ
  refine d.bijective_tensorComparison_of_normedModel φ (RingEquiv.refl _) (fun _ => rfl)
    ⟨‖μ‖ * ‖g 1‖ + 1, by positivity, fun x => ?_⟩ ⟨‖μ‖ * Cr, by positivity, fun y => ?_⟩
    ⟨Ct / ‖μ‖, by positivity, fun z => ?_⟩
  · change ‖d.tensorLeft φ x‖ ≤ _
    rw [hnorm]
    calc
      ‖μ‖ * ‖g (d.tensorLeft φ x)‖ ≤ ‖μ‖ * (‖g 1‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (hl x) (norm_nonneg _)
      _ ≤ (‖μ‖ * ‖g 1‖ + 1) * ‖x‖ := by nlinarith [norm_nonneg x]
  · change ‖d.tensorRight φ y‖ ≤ _
    rw [hnorm]
    calc
      ‖μ‖ * ‖g (d.tensorRight φ y)‖ ≤ ‖μ‖ * (Cr * ‖y‖) :=
        mul_le_mul_of_nonneg_left (hr y) (norm_nonneg _)
      _ = ‖μ‖ * Cr * ‖y‖ := by ring
  · change ‖d.tensorComparison φ z‖ ≤ _
    rw [hnorm]
    calc
      ‖d.tensorComparison φ z‖ ≤ Ct * ‖g z‖ := ht z
      _ = Ct / ‖μ‖ * (‖μ‖ * ‖g z‖) := by field_simp

include hsurj in
/-- After scaling by a scalar of large norm, the products of the generators
have coefficients whose norms are at most that scalar norm. Over trivially
normed fields the scalar is one. -/
theorem exists_structure_scale :
    ∃ μ : K, μ ≠ 0 ∧ ∀ i j, ∃ s : Fin n → d.algebra,
      d.coefficientSum φ c s = d.tensorRight φ (c i) * d.tensorRight φ (c j) ∧
        ‖s‖ ≤ ‖μ‖ := by
  choose s hs using fun ij : Fin n × Fin n =>
    hsurj (d.tensorRight φ (c ij.1) * d.tensorRight φ (c ij.2))
  by_cases hK : ∀ k : K, ‖k‖ ≤ 1
  · refine ⟨1, one_ne_zero, fun i j => ⟨s (i, j), hs (i, j), ?_⟩⟩
    rw [norm_one]
    exact PresentedStrictAffinoidAlgebra.norm_pi_le_one_of_scalar_norm_le_one d.algebra hK _
  push Not at hK
  let _ : NontriviallyNormedField K :=
    { toNormedField := inferInstance, non_trivial := hK }
  obtain ⟨μ, hμ⟩ := NormedField.exists_lt_norm K (∑ ij, ‖s ij‖)
  have hsum : 0 ≤ ∑ ij, ‖s ij‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨μ, fun h => ?_, fun i j => ⟨s (i, j), hs (i, j), ?_⟩⟩
  · rw [h, norm_zero] at hμ
    linarith
  · exact (Finset.single_le_sum (fun ij _ => norm_nonneg (s ij))
      (Finset.mem_univ (i, j))).trans hμ.le

end Model

end StrictTestDomain.RationalData

namespace StrictTestDomain

/-- The finite rational tensor comparison holds for all actual presented
strict affinoid algebras over every complete ultrametric normed field. -/
theorem finiteRationalTensorComparison : FiniteRationalTensorComparisonStatement.{u} := by
  intro K _ _ _ P Q d φ hfin
  obtain ⟨n, c, hc⟩ := φ.finite_iff_exists_surjective_coefficientMap.mp hfin
  have hsurj := d.coefficientSum_surjective φ c hc
  obtain ⟨μ, hμ, hstruct⟩ := d.exists_structure_scale φ c hsurj
  exact d.bijective_tensorComparison_of_generators φ c
    (φ.exists_coefficientMap_preimage_norm_le c hc)
    (PresentedStrictAffinoidAlgebra.isClosed_submodule_pi d.algebra _) μ hμ hstruct

end StrictTestDomain

end Langlands.Analytic
