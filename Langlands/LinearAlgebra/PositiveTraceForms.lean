import Langlands.LinearAlgebra.FiniteRankTraceExact
import Langlands.LinearAlgebra.FiniteSimpleTrace
import Langlands.Algebra.SandwichDimensionBoundProof
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Order.Atoms.Finite

/-!
# Positive traces and invariant forms on simple modules

Let `A` be a complex algebra with an involution. If the trace of a
finite-dimensional `A`-module is positive on every `star a * a`, then every
simple subquotient of that module carries a positive definite Hermitian form
for which `star a` is adjoint to `a`. On a finite-dimensional simple module
two such forms are proportional.
-/

noncomputable section

open scoped ComplexConjugate ComplexOrder

namespace Langlands.PositiveTraceForms

universe uA uM uN uQ uW uV uI

section Trace

theorem mem_finiteRankEnd {X : Type uM} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (T : Module.End ℂ X) : T ∈ finiteRankEnd X :=
  (mem_finiteRankEnd_iff T).mpr inferInstance

/-- Additivity of the trace along a short exact sequence of finite-dimensional
complex vector spaces. -/
theorem trace_eq_add_of_exact {N : Type uN} {M : Type uM} {Q : Type uQ}
    [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N]
    [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    [AddCommGroup Q] [Module ℂ Q] [FiniteDimensional ℂ Q]
    (f : N →ₗ[ℂ] M) (g : M →ₗ[ℂ] Q) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : LinearMap.range f = LinearMap.ker g)
    (TN : Module.End ℂ N) (TM : Module.End ℂ M) (TQ : Module.End ℂ Q)
    (hfT : TM ∘ₗ f = f ∘ₗ TN) (hgT : g ∘ₗ TM = TQ ∘ₗ g) :
    LinearMap.trace ℂ M TM = LinearMap.trace ℂ N TN + LinearMap.trace ℂ Q TQ := by
  have h := FiniteRankEnd.trace_shortExact f g hf hg hfg ⟨TN, mem_finiteRankEnd TN⟩
    ⟨TM, mem_finiteRankEnd TM⟩ ⟨TQ, mem_finiteRankEnd TQ⟩ hfT hgT
  simpa only [FiniteRankEnd.trace_eq_ambient] using h

end Trace

section Action

variable {A : Type uA} [Ring A] [Algebra ℂ A]

/-- The complex-linear action of an algebra element on a module. -/
abbrev act (M : Type uM) [AddCommGroup M] [Module ℂ M] [Module A M]
    [IsScalarTower ℂ A M] (a : A) : Module.End ℂ M :=
  DistribSMul.toLinearMap ℂ M a

@[simp] theorem act_apply {M : Type uM} [AddCommGroup M] [Module ℂ M] [Module A M]
    [IsScalarTower ℂ A M] (a : A) (v : M) : act M a v = a • v := rfl

theorem act_mul {M : Type uM} [AddCommGroup M] [Module ℂ M] [Module A M]
    [IsScalarTower ℂ A M] (a b : A) : act M (a * b) = act M a ∘ₗ act M b := by
  ext v
  exact mul_smul a b v

/-- Traces of isomorphic modules agree. -/
theorem trace_act_eq_of_equiv {M : Type uM} {N : Type uN}
    [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
    [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
    (e : M ≃ₗ[A] N) (a : A) :
    LinearMap.trace ℂ N (act N a) = LinearMap.trace ℂ M (act M a) := by
  have h : act N a = (e.restrictScalars ℂ).conj (act M a) := by
    ext v
    simp only [act_apply, LinearEquiv.conj_apply_apply, LinearEquiv.restrictScalars_apply,
      LinearEquiv.restrictScalars_symm_apply]
    rw [map_smul, LinearEquiv.apply_symm_apply]
  rw [h, LinearMap.trace_conj']

theorem act_eq_zero_of_equiv {M : Type uM} {N : Type uN}
    [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
    [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
    (e : M ≃ₗ[A] N) {a : A} (ha : act M a = 0) : act N a = 0 := by
  ext v
  have := congrArg e (LinearMap.congr_fun ha (e.symm v))
  simpa [← e.map_smul] using this

end Action

section Isotypic

variable {A : Type uA} [Ring A] [Algebra ℂ A]
variable {ι : Type uI} [Fintype ι] (M : ι → Type uM)
variable [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
variable [∀ i, Module A (M i)] [∀ i, IsScalarTower ℂ A (M i)]
variable [∀ i, FiniteDimensional ℂ (M i)] [∀ i, IsSimpleModule A (M i)]

open Classical in
/-- Density gives an algebra element acting as the identity on the members
isomorphic to a selected member and as zero on all other members. -/
theorem exists_isotypic_action (j : ι) :
    ∃ r : A, ∀ i, act (M i) r =
      if Nonempty (M i ≃ₗ[A] M j) then LinearMap.id else 0 := by
  classical
  let C : ι → Prop := fun i => Nonempty (M i ≃ₗ[A] M j)
  have hcross (φ : Module.End A (∀ i, M i)) {i k : ι}
      (hik : ¬ Nonempty (M k ≃ₗ[A] M i)) (v : M k) : φ (Pi.single k v) i = 0 := by
    let f : M k →ₗ[A] M i :=
      (LinearMap.proj i).comp (φ.comp (LinearMap.single A M k))
    have hf : f = 0 := f.bijective_or_eq_zero.resolve_left fun hf =>
      hik ⟨LinearEquiv.ofBijective f hf⟩
    exact LinearMap.congr_fun hf v
  have hsum (φ : Module.End A (∀ i, M i)) (i : ι) (x : ∀ i, M i) :
      φ x i = ∑ k, φ (Pi.single k (x k)) i := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum, Finset.sum_apply]
  have hCC {i k : ι} (hi : C i) (hk : ¬ C k) : ¬ Nonempty (M k ≃ₗ[A] M i) :=
    fun ⟨e⟩ => hk ⟨e.trans hi.some⟩
  have hNC {i k : ι} (hi : ¬ C i) (hk : C k) : ¬ Nonempty (M k ≃ₗ[A] M i) :=
    fun ⟨e⟩ => hi ⟨e.symm.trans hk.some⟩
  let q : (∀ i, M i) → (∀ i, M i) := fun x i => if C i then x i else 0
  have hq_single (k : ι) (v : M k) : q (Pi.single k v) =
      if C k then Pi.single k v else 0 := by
    funext i
    by_cases hik : i = k
    · subst hik
      by_cases h : C i <;> simp [q, h]
    · by_cases h : C k <;> simp [q, h, Pi.single_eq_of_ne hik]
  let p : Module.End (Module.End A (∀ i, M i)) (∀ i, M i) :=
    { toFun := q
      map_add' := fun x y => by
        funext i
        by_cases h : C i <;> simp [q, h]
      map_smul' := fun φ x => by
        funext i
        change (if C i then φ x i else 0) = φ (q x) i
        rw [hsum φ i (q x)]
        by_cases hi : C i
        · have hite : (if C i then φ x i else 0) = φ x i := ite_eq_left_of_eq_true _ _ (eq_true hi)
          rw [hite, hsum φ i x]
          apply Finset.sum_congr rfl
          intro k _
          by_cases hk : C k
          · have hqk : q x k = x k := ite_eq_left_of_eq_true _ _ (eq_true hk)
            rw [hqk]
          · have hqk : q x k = 0 := ite_eq_right_of_eq_false _ _ (eq_false hk)
            rw [hqk, Pi.single_zero, map_zero, Pi.zero_apply]
            exact hcross φ (hCC hi hk) (x k)
        · have hite : (if C i then φ x i else 0) = 0 := ite_eq_right_of_eq_false _ _ (eq_false hi)
          rw [hite]
          symm
          apply Finset.sum_eq_zero
          intro k _
          by_cases hk : C k
          · have hqk : q x k = x k := ite_eq_left_of_eq_true _ _ (eq_true hk)
            rw [hqk]
            exact hcross φ (hNC hi hk) (x k)
          · have hqk : q x k = 0 := ite_eq_right_of_eq_false _ _ (eq_false hk)
            rw [hqk, Pi.single_zero, map_zero, Pi.zero_apply] }
  let b := fun i => Module.finBasis ℂ (M i)
  let s : Finset (∀ i, M i) :=
    Finset.univ.biUnion fun i =>
      Finset.univ.image fun k => Pi.single i (b i k)
  obtain ⟨r, hr⟩ := jacobson_density p s
  refine ⟨r, fun i => (b i).ext fun k => ?_⟩
  have hk : Pi.single i (b i k) ∈ s :=
    Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i, Finset.mem_image_of_mem _ (Finset.mem_univ k)⟩
  have h := congrArg (fun x => x i) (hr _ hk)
  change q (Pi.single i (b i k)) i = (r • Pi.single i (b i k)) i at h
  rw [hq_single] at h
  by_cases hi : C i
  · have hi' : Nonempty (M i ≃ₗ[A] M j) := hi
    simp only [hi, ↓reduceIte, Pi.single_eq_same, Pi.smul_apply] at h
    simp only [act_apply, hi', ↓reduceIte, LinearMap.id_apply]
    exact h.symm
  · have hi' : ¬ Nonempty (M i ≃ₗ[A] M j) := hi
    simp only [hi, ↓reduceIte, Pi.zero_apply, Pi.smul_apply, Pi.single_eq_same] at h
    simp only [act_apply, hi', ↓reduceIte, LinearMap.zero_apply]
    exact h.symm

end Isotypic

section Burnside

variable {A : Type uA} [Ring A] [Algebra ℂ A]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
  [FiniteDimensional ℂ V] [IsSimpleModule A V]

/-- Burnside's theorem in the form used below. -/
theorem exists_act_eq (T : Module.End ℂ V) : ∃ x : A, act V x = T := by
  obtain ⟨x, hx⟩ := SandwichDimensionBound.action_surjective ℂ A V T
  exact ⟨x, by ext v; exact LinearMap.congr_fun hx v⟩

/-- An element whose products have vanishing trace acts by zero on a simple
finite-dimensional module. -/
theorem act_eq_zero_of_trace_mul (a : A)
    (h : ∀ x : A, LinearMap.trace ℂ V (act V (x * a)) = 0) : act V a = 0 := by
  by_contra ha
  obtain ⟨v, hv⟩ : ∃ v, act V a v ≠ 0 := by
    by_contra hall
    push Not at hall
    exact ha (LinearMap.ext hall)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual ℂ V, ℓ (act V a v) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ _).mp hall)
  obtain ⟨x, hx⟩ := exists_act_eq (A := A) (ℓ.smulRight v)
  apply hℓ
  have := h x
  rw [act_mul, hx] at this
  have heq : ℓ.smulRight v ∘ₗ act V a = (ℓ ∘ₗ act V a).smulRight v := by
    ext w
    rfl
  rw [heq, LinearMap.trace_smulRight] at this
  exact this

end Burnside

section ActionLinear

variable {A : Type uA} [Ring A] [Algebra ℂ A]

theorem act_sub {M : Type uM} [AddCommGroup M] [Module ℂ M] [Module A M]
    [IsScalarTower ℂ A M] (a b : A) : act M (a - b) = act M a - act M b := by
  ext v
  exact sub_smul a b v

/-- The action map `A → End_ℂ M` as a complex-linear map. -/
def actLinear (M : Type uM) [AddCommGroup M] [Module ℂ M] [Module A M]
    [IsScalarTower ℂ A M] : A →ₗ[ℂ] Module.End ℂ M where
  toFun := act M
  map_add' a b := by
    ext v
    exact add_smul a b v
  map_smul' c a := by
    ext v
    exact smul_assoc c a v

@[simp] theorem actLinear_apply {M : Type uM} [AddCommGroup M] [Module ℂ M] [Module A M]
    [IsScalarTower ℂ A M] (a : A) : actLinear M a = act M a := rfl

/-- Additivity of the trace of the action for a submodule and its quotient. -/
theorem trace_act_eq_add {M : Type uM} [AddCommGroup M] [Module ℂ M] [Module A M]
    [IsScalarTower ℂ A M] [FiniteDimensional ℂ M] (S : Submodule A M)
    [FiniteDimensional ℂ S] [FiniteDimensional ℂ (M ⧸ S)] (a : A) :
    LinearMap.trace ℂ M (act M a) =
      LinearMap.trace ℂ S (act S a) + LinearMap.trace ℂ (M ⧸ S) (act (M ⧸ S) a) := by
  refine trace_eq_add_of_exact (S.subtype.restrictScalars ℂ) (S.mkQ.restrictScalars ℂ)
    Subtype.val_injective S.mkQ_surjective ?_ _ _ _ ?_ ?_
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero S).mpr y.property
    · intro hx
      exact ⟨⟨x, (Submodule.Quotient.mk_eq_zero S).mp hx⟩, rfl⟩
  · exact LinearMap.ext fun x => rfl
  · exact LinearMap.ext fun x => rfl

end ActionLinear

section Positivity

variable {A : Type uA} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

theorem im_eq_zero_of_nonneg {z : ℂ} (hz : 0 ≤ z) : z.im = 0 :=
  (Complex.nonneg_iff.mp hz).2.symm

/-- A complex-linear functional that is nonnegative on every `star a * a` is
Hermitian. -/
theorem conj_apply_star_mul (t : A →ₗ[ℂ] ℂ) (ht : ∀ a, 0 ≤ t (star a * a)) (a b : A) :
    conj (t (star a * b)) = t (star b * a) := by
  have h1 := im_eq_zero_of_nonneg (ht (a + b))
  have h2 := im_eq_zero_of_nonneg (ht (a + Complex.I • b))
  have ha := im_eq_zero_of_nonneg (ht a)
  have hb := im_eq_zero_of_nonneg (ht b)
  have e1 : t (star (a + b) * (a + b)) =
      t (star a * a) + t (star a * b) + t (star b * a) + t (star b * b) := by
    simp only [star_add, add_mul, mul_add, map_add]
    ring
  have e2 : t (star (a + Complex.I • b) * (a + Complex.I • b)) =
      t (star a * a) + Complex.I * t (star a * b) + conj Complex.I * t (star b * a) +
        conj Complex.I * Complex.I * t (star b * b) := by
    simp only [star_add, star_smul, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
      map_add, map_smul, smul_eq_mul, Complex.star_def]
    ring
  rw [e1] at h1
  rw [e2, Complex.conj_I] at h2
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re,
    Complex.neg_im, Complex.mul_re] at h1 h2
  apply Complex.ext
  · simp only [Complex.conj_re]
    nlinarith
  · simp only [Complex.conj_im]
    nlinarith

/-- The positive semidefinite Hermitian form `(a, b) ↦ t (star a * b)` on `A`. -/
@[reducible] def starMulCore (t : A →ₗ[ℂ] ℂ) (ht : ∀ a, 0 ≤ t (star a * a)) :
    PreInnerProductSpace.Core ℂ A where
  inner a b := t (star a * b)
  conj_inner_symm a b := conj_apply_star_mul t ht b a
  re_inner_nonneg a := (Complex.nonneg_iff.mp (ht a)).1
  add_left a b c := by simp only [star_add, add_mul, map_add]
  smul_left a b r := by
    simp only [star_smul, smul_mul_assoc, map_smul, smul_eq_mul, Complex.star_def]

/-- Cauchy--Schwarz for a positive functional: an element of zero length is
orthogonal to everything. -/
theorem apply_star_mul_eq_zero (t : A →ₗ[ℂ] ℂ) (ht : ∀ a, 0 ≤ t (star a * a)) {a : A}
    (ha : t (star a * a) = 0) (b : A) : t (star b * a) = 0 := by
  let c := starMulCore t ht
  let _ : Inner ℂ A := c.toInner
  have h := InnerProductSpace.Core.inner_mul_inner_self_le (𝕜 := ℂ) (F := A) a b
  have h0 : RCLike.re (inner ℂ a a) = 0 := by
    change RCLike.re (t (star a * a)) = 0
    rw [ha, map_zero]
  rw [h0, zero_mul, InnerProductSpace.Core.norm_inner_symm a b] at h
  have h' : ‖inner ℂ b a‖ = 0 := by nlinarith [norm_nonneg (inner ℂ b a)]
  exact norm_eq_zero.mp h'

end Positivity

section TraceVanishing

variable {A : Type uA} [Ring A] [Algebra ℂ A]
variable {ι : Type uI} [Fintype ι] (M : ι → Type uM)
variable [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
variable [∀ i, Module A (M i)] [∀ i, IsScalarTower ℂ A (M i)]
variable [∀ i, FiniteDimensional ℂ (M i)] [∀ i, IsSimpleModule A (M i)]

/-- If every product `x * a` has vanishing total trace on a finite family of
finite-dimensional simple modules, then `a` acts by zero on each member. -/
theorem act_eq_zero_of_sum_trace_mul (a : A)
    (h : ∀ x : A, ∑ i, LinearMap.trace ℂ (M i) (act (M i) (x * a)) = 0) (j : ι) :
    act (M j) a = 0 := by
  classical
  obtain ⟨r, hr⟩ := exists_isotypic_action (A := A) M j
  apply act_eq_zero_of_trace_mul a
  intro x
  have h1 := h (r * x)
  have h2 : ∀ i, LinearMap.trace ℂ (M i) (act (M i) (r * x * a)) =
      if Nonempty (M i ≃ₗ[A] M j) then LinearMap.trace ℂ (M j) (act (M j) (x * a))
      else 0 := by
    intro i
    rw [mul_assoc, act_mul, hr i]
    split_ifs with hi
    · rw [LinearMap.id_comp]
      exact (trace_act_eq_of_equiv hi.some (x * a)).symm
    · rw [LinearMap.zero_comp, map_zero]
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul] at h1
  have hj : j ∈ Finset.univ.filter fun i => Nonempty (M i ≃ₗ[A] M j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ j, ⟨LinearEquiv.refl A (M j)⟩⟩
  have hcard : ((Finset.univ.filter fun i => Nonempty (M i ≃ₗ[A] M j)).card : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨j, hj⟩)
  exact (mul_eq_zero.mp h1).resolve_left hcard

omit [Fintype ι] [∀ i, FiniteDimensional ℂ (M i)] [∀ i, IsSimpleModule A (M i)] in
open Classical in
/-- Multiplying on the right by an isotypic density element spreads vanishing
on one member to every member. -/
theorem act_mul_eq_zero_of_isotypic {r : A} {j : ι}
    (hr : ∀ i, act (M i) r = if Nonempty (M i ≃ₗ[A] M j) then LinearMap.id else 0)
    {y : A} (hy : act (M j) y = 0) (i : ι) : act (M i) (y * r) = 0 := by
  rw [act_mul, hr i]
  split_ifs with hi
  · rw [LinearMap.comp_id]
    exact act_eq_zero_of_equiv hi.some.symm hy
  · rw [LinearMap.comp_zero]

end TraceVanishing

section Form

/-- A positive definite Hermitian form on a module over a complex algebra with
involution, for which `star a` is adjoint to `a`. The form is conjugate-linear
in its first argument, following `InnerProductSpace.Core`. -/
structure StarInvariantForm (A : Type uA) [Ring A] [StarRing A]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [Module A V]
    extends toInnerProductCore : InnerProductSpace.Core ℂ V where
  /-- The adjoint of the action of `a` is the action of `star a`. -/
  adjoint (a : A) (v w : V) : inner (a • v) w = inner v (star a • w)

namespace StarInvariantForm

variable {A : Type uA} [Ring A] [StarRing A]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [Module A V]
variable (b : StarInvariantForm A V)

theorem inner_add_right (v w u : V) : b.inner v (w + u) = b.inner v w + b.inner v u := by
  rw [← b.conj_inner_symm v (w + u), b.add_left, map_add, b.conj_inner_symm,
    b.conj_inner_symm]

theorem inner_smul_right (v w : V) (c : ℂ) : b.inner v (c • w) = c * b.inner v w := by
  rw [← b.conj_inner_symm v (c • w), b.smul_left, map_mul, b.conj_inner_symm,
    Complex.conj_conj]

theorem conj_inner_self (v : V) : conj (b.inner v v) = b.inner v v :=
  b.conj_inner_symm v v

theorem eq_of_forall_inner_eq {y y' : V} (h : ∀ u, b.inner u y = b.inner u y') : y = y' := by
  have hsub : ∀ u, b.inner u (y - y') = 0 := fun u => by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ y', b.inner_add_right, b.inner_smul_right, h u]
    ring
  exact sub_eq_zero.mp (b.definite _ (hsub _))

/-- Transport of a star-invariant form along an isomorphism of modules. -/
def comapEquiv [Algebra ℂ A] {N : Type uN} [AddCommGroup N] [Module ℂ N] [Module A N]
    [IsScalarTower ℂ A V] [IsScalarTower ℂ A N]
    (b : StarInvariantForm A N) (e : V ≃ₗ[A] N) : StarInvariantForm A V where
  inner v w := b.inner (e v) (e w)
  conj_inner_symm v w := b.conj_inner_symm (e v) (e w)
  re_inner_nonneg v := b.re_inner_nonneg (e v)
  add_left u v w := by
    change b.inner (e (u + v)) (e w) = b.inner (e u) (e w) + b.inner (e v) (e w)
    rw [map_add, b.add_left]
  smul_left v w c := by
    change b.inner (e (c • v)) (e w) = conj c * b.inner (e v) (e w)
    have hc : e (c • v) = c • e v := e.toLinearMap.map_smul_of_tower c v
    rw [hc, b.smul_left]
  definite v hv := e.injective ((b.definite _ hv).trans (map_zero e).symm)
  adjoint a v w := by
    rw [map_smul, b.adjoint, map_smul]

end StarInvariantForm

end Form

section Uniqueness

variable {A : Type uA} [Ring A] [Algebra ℂ A] [StarRing A]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
  [FiniteDimensional ℂ V] [IsSimpleModule A V]

/-- Two star-invariant positive definite forms on a finite-dimensional simple
module are proportional. -/
theorem StarInvariantForm.inner_mul_inner_eq (b b' : StarInvariantForm A V) (v₀ x w : V) :
    b.inner v₀ v₀ * b'.inner x w = b'.inner v₀ v₀ * b.inner x w := by
  let T : Module.End ℂ V :=
    { toFun := fun u => b.inner v₀ u • x
      map_add' := fun u u' => by rw [b.inner_add_right, add_smul]
      map_smul' := fun c u => by
        rw [b.inner_smul_right, mul_smul]
        rfl }
  obtain ⟨a, ha⟩ := exists_act_eq (A := A) T
  have hact (u : V) : a • u = b.inner v₀ u • x := LinearMap.congr_fun ha u
  have hstar : star a • w = b.inner x w • v₀ := by
    apply b.eq_of_forall_inner_eq
    intro u
    rw [← b.adjoint, hact, b.smul_left, b.conj_inner_symm, b.inner_smul_right]
    ring
  have key := b'.adjoint a v₀ w
  rw [hact, hstar, b'.smul_left, b'.inner_smul_right, b.conj_inner_self] at key
  rw [key]
  ring

/-- Two star-invariant positive definite forms on a finite-dimensional simple
module differ by a positive real factor. -/
theorem StarInvariantForm.exists_pos_real_eq (b b' : StarInvariantForm A V) :
    ∃ r : ℝ, 0 < r ∧ ∀ x w : V, b'.inner x w = r * b.inner x w := by
  have : Nontrivial V := IsSimpleModule.nontrivial A V
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  have hpos (c : StarInvariantForm A V) : 0 < (c.inner v₀ v₀).re ∧ (c.inner v₀ v₀).im = 0 := by
    have him : (c.inner v₀ v₀).im = 0 := by
      have h := congrArg Complex.im (c.conj_inner_self v₀)
      rw [Complex.conj_im] at h
      linarith
    refine ⟨lt_of_le_of_ne (c.re_inner_nonneg v₀) fun hre => hv₀ (c.definite v₀ ?_), him⟩
    exact Complex.ext hre.symm him
  obtain ⟨hb, hbi⟩ := hpos b
  obtain ⟨hb', hbi'⟩ := hpos b'
  refine ⟨(b'.inner v₀ v₀).re / (b.inner v₀ v₀).re, div_pos hb' hb, fun x w => ?_⟩
  have hb0 : b.inner v₀ v₀ = ((b.inner v₀ v₀).re : ℂ) := Complex.ext rfl (by simp [hbi])
  have hb0' : b'.inner v₀ v₀ = ((b'.inner v₀ v₀).re : ℂ) := Complex.ext rfl (by simp [hbi'])
  have hne : ((b.inner v₀ v₀).re : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have key := b.inner_mul_inner_eq b' v₀ x w
  rw [hb0, hb0'] at key
  rw [Complex.ofReal_div, div_mul_eq_mul_div, eq_div_iff hne, mul_comm, key]

end Uniqueness

section Construction

variable {A : Type uA} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
variable {ι : Type uI} [Fintype ι] (M : ι → Type uM)
variable [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
variable [∀ i, Module A (M i)] [∀ i, IsScalarTower ℂ A (M i)]
variable [∀ i, FiniteDimensional ℂ (M i)] [∀ i, IsSimpleModule A (M i)]

/-- A positive functional which is the sum of the traces of a finite family of
finite-dimensional simple modules yields a star-invariant positive definite
form on every member of the family. -/
theorem exists_starInvariantForm_of_sum (t : A →ₗ[ℂ] ℂ) (ht : ∀ a, 0 ≤ t (star a * a))
    (htr : ∀ a, t a = ∑ i, LinearMap.trace ℂ (M i) (act (M i) a)) (j : ι) :
    Nonempty (StarInvariantForm A (M j)) := by
  classical
  obtain ⟨r, hr⟩ := exists_isotypic_action (A := A) M j
  have hrj : act (M j) r = LinearMap.id := by
    rw [hr j]
    exact ite_eq_left_of_eq_true _ _ (eq_true ⟨LinearEquiv.refl A (M j)⟩)
  obtain ⟨σ, hσ⟩ := (actLinear (A := A) (M j)).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr fun T => exists_act_eq (A := A) T)
  have hσ' (T : Module.End ℂ (M j)) : act (M j) (σ T) = T := LinearMap.congr_fun hσ T
  have : Nontrivial (M j) := IsSimpleModule.nontrivial A (M j)
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : M j)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual ℂ (M j), ℓ v₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv₀ ((Module.forall_dual_apply_eq_zero_iff ℂ v₀).mp hall)
  let L : M j →ₗ[ℂ] Module.End ℂ (M j) :=
    { toFun := fun v => ℓ.smulRight v
      map_add' := fun v w => by
        ext u
        simp [smul_add]
      map_smul' := fun c v => by
        ext u
        simp [smul_comm (ℓ u) c v] }
  have hL (v u : M j) : L v u = ℓ u • v := rfl
  let Φ : M j →ₗ[ℂ] A := LinearMap.mulRight ℂ r ∘ₗ σ ∘ₗ L
  have hΦ (v : M j) : Φ v = σ (L v) * r := rfl
  have hΦact (v : M j) : act (M j) (Φ v) = L v := by
    rw [hΦ, act_mul, hσ', hrj, LinearMap.comp_id]
  have hT0 : ∀ d : A, (∀ i, act (M i) d = 0) → ∀ x, t (x * d) = 0 := fun d hd x => by
    rw [htr]
    simp only [act_mul, hd, LinearMap.comp_zero, map_zero, Finset.sum_const_zero]
  have hT1 : ∀ d : A, (∀ i, act (M i) d = 0) → ∀ x, t (star d * x) = 0 := fun d hd x => by
    rw [← conj_apply_star_mul t ht x d, hT0 d hd, map_zero]
  have hd : ∀ (c : A) (u : M j) (i : ι), act (M i) (Φ (c • u) - c * Φ u) = 0 := by
    intro c u i
    have hsplit : Φ (c • u) - c * Φ u = (σ (L (c • u)) - c * σ (L u)) * r := by
      rw [hΦ, hΦ, sub_mul, mul_assoc]
    rw [hsplit]
    apply act_mul_eq_zero_of_isotypic M hr
    rw [act_sub, act_mul, hσ', hσ']
    ext x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, act_apply, LinearMap.zero_apply, hL]
    rw [smul_comm c (ℓ x) u, sub_self]
  refine ⟨{ inner := fun v w => t (star (Φ v) * Φ w)
            conj_inner_symm := fun v w => conj_apply_star_mul t ht (Φ w) (Φ v)
            re_inner_nonneg := fun v => (Complex.nonneg_iff.mp (ht (Φ v))).1
            add_left := fun v w u => by simp only [map_add, star_add, add_mul]
            smul_left := fun v w c => by
              simp only [map_smul, star_smul, smul_mul_assoc, smul_eq_mul, Complex.star_def]
            definite := fun v hv => ?_
            adjoint := fun a v w => ?_ }⟩
  · have hzero : ∀ x, t (x * Φ v) = 0 := fun x => by
      simpa using apply_star_mul_eq_zero t ht hv (star x)
    have hact : act (M j) (Φ v) = 0 :=
      act_eq_zero_of_sum_trace_mul M (Φ v) (fun x => by rw [← htr]; exact hzero x) j
    rw [hΦact] at hact
    have h := LinearMap.congr_fun hact v₀
    rw [hL, LinearMap.zero_apply] at h
    exact (smul_eq_zero.mp h).resolve_left hℓ
  · have e1 : Φ (a • v) = a * Φ v + (Φ (a • v) - a * Φ v) := by abel
    have e2 : Φ (star a • w) = star a * Φ w + (Φ (star a • w) - star a * Φ w) := by abel
    rw [e1, e2, star_add, add_mul, mul_add, map_add, map_add, hT1 _ (hd a v),
      hT0 _ (hd (star a) w), add_zero, add_zero, star_mul, mul_assoc]

end Construction

section Decomposition

/-- A bundled finite-dimensional simple module over `A`, with its complex
structure. -/
structure SimpleFDModule (A : Type uA) [Ring A] [Algebra ℂ A] where
  /-- The carrier. -/
  carrier : Type uM
  [instAddCommGroup : AddCommGroup carrier]
  [instModuleComplex : Module ℂ carrier]
  [instModule : Module A carrier]
  [instIsScalarTower : IsScalarTower ℂ A carrier]
  [instFiniteDimensional : FiniteDimensional ℂ carrier]
  [instIsSimpleModule : IsSimpleModule A carrier]

attribute [instance] SimpleFDModule.instAddCommGroup SimpleFDModule.instModuleComplex
  SimpleFDModule.instModule SimpleFDModule.instIsScalarTower
  SimpleFDModule.instFiniteDimensional SimpleFDModule.instIsSimpleModule

variable {A : Type uA} [Ring A] [Algebra ℂ A]

/-- The trace of the action on a bundled simple module. -/
def SimpleFDModule.traceAct (F : SimpleFDModule.{uA, uM} A) (a : A) : ℂ :=
  LinearMap.trace ℂ F.carrier (act F.carrier a)

theorem composition_factors_of_subsingleton (M : Type uM) [AddCommGroup M] [Module ℂ M]
    [Module A M] [IsScalarTower ℂ A M] [Subsingleton M] :
    (∀ a : A, LinearMap.trace ℂ M (act M a) =
        (([] : List (SimpleFDModule.{uA, uM} A)).map fun F => F.traceAct a).sum) ∧
      ∀ (W : Type uW) [AddCommGroup W] [Module A W] (V : Type uV) [AddCommGroup V]
        [Module A V] [IsSimpleModule A V] (ι : W →ₗ[A] M), Function.Injective ι →
        ∀ f : W →ₗ[A] V, Function.Surjective f →
          ∃ F ∈ ([] : List (SimpleFDModule.{uA, uM} A)), Nonempty (V ≃ₗ[A] F.carrier) := by
  refine ⟨fun a => ?_, fun W _ _ V _ _ _ ι hι f hf => ?_⟩
  · have h0 : act M a = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [h0, map_zero]
    rfl
  · exfalso
    have : Subsingleton W := hι.subsingleton
    have : Subsingleton V := hf.subsingleton
    have := IsSimpleModule.nontrivial A V
    exact not_nontrivial V ‹_›

/-- Every finite-dimensional module has a finite list of simple composition
factors: the trace of the action is the sum of their traces, and every simple
subquotient is isomorphic to one of them. -/
theorem exists_composition_factors (M : Type uM) [AddCommGroup M] [Module ℂ M]
    [Module A M] [IsScalarTower ℂ A M] [FiniteDimensional ℂ M] :
    ∃ L : List (SimpleFDModule.{uA, uM} A),
      (∀ a : A, LinearMap.trace ℂ M (act M a) = (L.map fun F => F.traceAct a).sum) ∧
      ∀ (W : Type uW) [AddCommGroup W] [Module A W] (V : Type uV) [AddCommGroup V]
        [Module A V] [IsSimpleModule A V] (ι : W →ₗ[A] M), Function.Injective ι →
        ∀ f : W →ₗ[A] V, Function.Surjective f → ∃ F ∈ L, Nonempty (V ≃ₗ[A] F.carrier) := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℂ M ≤ n := ⟨_, le_rfl⟩
  induction n generalizing M with
  | zero =>
    have : Subsingleton M :=
      Module.finrank_zero_iff.mp (Nat.le_zero.mp hn)
    exact ⟨[], composition_factors_of_subsingleton M⟩
  | succ n ih =>
    rcases subsingleton_or_nontrivial M with hM | hM
    · exact ⟨[], composition_factors_of_subsingleton M⟩
    have : IsArtinian A M := isArtinian_of_tower ℂ inferInstance
    obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule A M)
    have : IsSimpleModule A S := isSimpleModule_iff_isAtom.mpr hS
    have : FiniteDimensional ℂ S :=
      Module.Finite.of_injective (S.subtype.restrictScalars ℂ) Subtype.val_injective
    have : FiniteDimensional ℂ (M ⧸ S) :=
      Module.Finite.of_surjective (S.mkQ.restrictScalars ℂ) S.mkQ_surjective
    have hdim : Module.finrank ℂ (M ⧸ S) < Module.finrank ℂ M := by
      have h := LinearMap.finrank_range_add_finrank_ker (S.mkQ.restrictScalars ℂ)
      rw [LinearMap.range_eq_top.mpr
        (show Function.Surjective (S.mkQ.restrictScalars ℂ) from S.mkQ_surjective),
        finrank_top] at h
      have hker : LinearMap.ker (S.mkQ.restrictScalars ℂ) = S.restrictScalars ℂ := by
        ext x
        exact Submodule.Quotient.mk_eq_zero S
      have hpos : Module.finrank ℂ (LinearMap.ker (S.mkQ.restrictScalars ℂ)) ≠ 0 := by
        rw [Ne, Submodule.finrank_eq_zero, hker, Submodule.restrictScalars_eq_bot_iff]
        exact hS.1
      omega
    obtain ⟨L, htr, hsub⟩ := ih (M ⧸ S) (by omega)
    let FS : SimpleFDModule.{uA, uM} A := { carrier := S }
    refine ⟨FS :: L, fun a => ?_, fun W _ _ V _ _ _ ι hι f hf => ?_⟩
    · rw [List.map_cons, List.sum_cons, ← htr a]
      exact trace_act_eq_add S a
    · let g : W →ₗ[A] M ⧸ S := S.mkQ ∘ₗ ι
      by_cases hW : LinearMap.ker g ≤ LinearMap.ker f
      · let ι' : W ⧸ LinearMap.ker g →ₗ[A] M ⧸ S := (LinearMap.ker g).liftQ g le_rfl
        have hι' : Function.Injective ι' := by
          rw [← LinearMap.ker_eq_bot]
          exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
        let f' : W ⧸ LinearMap.ker g →ₗ[A] V := (LinearMap.ker g).liftQ f hW
        have hf' : Function.Surjective f' := by
          intro v
          obtain ⟨w, rfl⟩ := hf v
          exact ⟨Submodule.Quotient.mk w, rfl⟩
        obtain ⟨F, hF, he⟩ := hsub (W ⧸ LinearMap.ker g) V ι' hι' f' hf'
        exact ⟨F, List.mem_cons_of_mem _ hF, he⟩
      · obtain ⟨w, hwW, hfw⟩ := Set.not_subset.mp hW
        have hmemS : ∀ u : LinearMap.ker g, ι u ∈ S := fun u =>
          (Submodule.Quotient.mk_eq_zero S).mp (LinearMap.mem_ker.mp u.property)
        let φ : LinearMap.ker g →ₗ[A] S :=
          LinearMap.codRestrict S (ι ∘ₗ (LinearMap.ker g).subtype) hmemS
        have hφinj : Function.Injective φ := by
          intro u u' huu
          apply Subtype.val_injective
          apply hι
          exact congrArg Subtype.val huu
        have hφsurj : Function.Surjective φ := by
          rw [← LinearMap.range_eq_top]
          refine (eq_bot_or_eq_top (LinearMap.range φ)).resolve_left fun hbot => ?_
          rw [LinearMap.range_eq_bot] at hbot
          have h0 : (⟨w, hwW⟩ : LinearMap.ker g) = 0 :=
            hφinj (by rw [hbot, map_zero, LinearMap.zero_apply])
          apply hfw
          have : w = 0 := congrArg Subtype.val h0
          change w ∈ LinearMap.ker f
          rw [LinearMap.mem_ker, this, map_zero]
        let eφ : LinearMap.ker g ≃ₗ[A] S := LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
        have : IsSimpleModule A (LinearMap.ker g) := IsSimpleModule.congr eφ
        let ψ : LinearMap.ker g →ₗ[A] V := f ∘ₗ (LinearMap.ker g).subtype
        have hψ : ψ ≠ 0 := by
          intro h0
          apply hfw
          have := LinearMap.congr_fun h0 ⟨w, hwW⟩
          change w ∈ LinearMap.ker f
          exact LinearMap.mem_ker.mpr this
        let eψ : LinearMap.ker g ≃ₗ[A] V :=
          LinearEquiv.ofBijective ψ (LinearMap.bijective_of_ne_zero hψ)
        exact ⟨FS, List.mem_cons_self .., ⟨eψ.symm.trans eφ⟩⟩

end Decomposition

section Main

variable {A : Type uA} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

/-- **Positive traces give unitary structures on simple subquotients.** Let `M`
be a finite-dimensional module over a complex algebra with involution, whose
trace is nonnegative on every `star a * a`. Then every simple subquotient `V` of
`M` (presented by an injection `W → M` and a surjection `W → V`) carries a
positive definite Hermitian form for which `star a` is adjoint to `a`. -/
theorem exists_starInvariantForm_of_subquotient
    (M : Type uM) [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
    [FiniteDimensional ℂ M]
    (hpos : ∀ a : A, 0 ≤ LinearMap.trace ℂ M (act M (star a * a)))
    {W : Type uW} [AddCommGroup W] [Module A W]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
    [IsSimpleModule A V]
    (ι : W →ₗ[A] M) (hι : Function.Injective ι) (f : W →ₗ[A] V)
    (hf : Function.Surjective f) :
    Nonempty (StarInvariantForm A V) := by
  obtain ⟨L, htrL, hsub⟩ := exists_composition_factors.{uA, uM, uW, uV} (A := A) M
  obtain ⟨F, hF, ⟨e⟩⟩ := hsub W V ι hι f hf
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hF
  let t : A →ₗ[ℂ] ℂ := LinearMap.trace ℂ M ∘ₗ actLinear M
  have htr : ∀ a, t a = ∑ k : Fin L.length,
      LinearMap.trace ℂ (L.get k).carrier (act (L.get k).carrier a) := by
    intro a
    change LinearMap.trace ℂ M (act M a) = _
    rw [htrL a, ← Fin.sum_univ_fun_getElem L fun F => F.traceAct a]
    rfl
  obtain ⟨b⟩ := exists_starInvariantForm_of_sum (fun k : Fin L.length => (L.get k).carrier)
    t hpos htr i
  exact ⟨b.comapEquiv e⟩

end Main

end Langlands.PositiveTraceForms
