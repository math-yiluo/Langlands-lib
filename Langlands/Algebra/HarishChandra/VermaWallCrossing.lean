import Langlands.Algebra.HarishChandra.SplitCartanVerma
import Mathlib.Algebra.Polynomial.Roots

/-! # Central characters of mirror Verma modules across a wall

Let `X, X'` be real-regular elements of a split Cartan subalgebra `𝔥` whose positive systems
differ by one root: `Re α(X) > 0 > Re α(X')`, and every other root has real parts of the same sign
at `X` and `X'`. Let `e ∈ 𝔤_α`, `f ∈ 𝔤_{-α}`, `h = [e, f]` with `α(h) = 2`. For a central element
`z` of `U(𝔤)` let `χ_X(λ)` be the scalar congruent to `z` modulo the mirror Verma right ideal
`R_X(λ)`. This file proves `χ_X(λ) = χ_{X'}(λ - α)` for every linear form `λ` on `𝔥`.

For `λ(h) = -m` with `m ∈ ℕ` this follows from two singular vectors: `f^{m+1}` multiplies
`R_X(λ + (m+1)α)` into `R_X(λ)`, and `f^m` multiplies `R_{X'}(λ + mα)` into
`R_X(λ) + f^{m+1} U(𝔤)`. Neither `f^{m+1}` nor `f^m` lies in the corresponding right ideal. Both
sides are polynomial along the line `λ + t α / 2`, which meets the hyperplanes `λ(h) = -m`
infinitely often. -/

noncomputable section

universe v

set_option autoImplicit false

namespace Langlands.Algebra.HarishChandra

open LieModule Langlands.Algebra.UniversalEnveloping Polynomial

attribute [local instance 100] LieRing.ofAssociativeRing

section Sl2

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]

local notation "U" => UniversalEnvelopingAlgebra ℂ L
local notation "ι" => UniversalEnvelopingAlgebra.ι ℂ

variable {H : LieSubalgebra ℂ L} (α : H →ₗ[ℂ] ℂ) {e f : L} {h : H}

theorem ι_mul_ι_of_lie_eq_smul {x y : L} {c : ℂ} (hxy : ⁅x, y⁆ = c • y) :
    ι y * ι x = ι x * ι y - c • ι y := by
  have h1 := LieHom.map_lie (UniversalEnvelopingAlgebra.ι ℂ (L := L)) x y
  rw [hxy, map_smul, Ring.lie_def] at h1
  rw [h1]
  abel

include α in
/-- Commuting a power of a negative root vector past an element of `𝔥`. -/
theorem pow_mul_ι_cartan (hf : f ∈ weightSpace L (-⇑α)) (h' : H) (k : ℕ) :
    ι f ^ k * ι (h' : L) = ι (h' : L) * ι f ^ k + ((k : ℂ) * α h') • ι f ^ k := by
  have hb : ⁅(h' : L), f⁆ = (-(α h')) • f := (mem_weightSpace _ _).mp hf h'
  have h1 : ι f * ι (h' : L) = ι (h' : L) * ι f + (α h') • ι f := by
    rw [ι_mul_ι_of_lie_eq_smul hb, neg_smul, sub_neg_eq_add]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, ih, mul_add, ← mul_assoc, h1, mul_smul_comm, add_mul, mul_assoc,
      smul_mul_assoc, ← pow_succ', add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

include α in
/-- The commutation of a power of `f` with `e`:
`f^{k+1} e = e f^{k+1} - (k+1) f^k h + (k+1) k f^k`. -/
theorem pow_succ_mul_ι_e (hf : f ∈ weightSpace L (-⇑α)) (hef : ⁅e, f⁆ = (h : L))
    (hαh : α h = 2) (k : ℕ) :
    ι f ^ (k + 1) * ι e = ι e * ι f ^ (k + 1) - ((k : ℂ) + 1) • (ι f ^ k * ι (h : L)) +
      (((k : ℂ) + 1) * k) • ι f ^ k := by
  have hfe : ι f * ι e = ι e * ι f - ι (h : L) := by
    have h1 := LieHom.map_lie (UniversalEnvelopingAlgebra.ι ℂ (L := L)) e f
    rw [hef, Ring.lie_def] at h1
    rw [h1]
    abel
  induction k with
  | zero =>
    rw [zero_add, pow_one, pow_zero, one_mul, Nat.cast_zero, zero_add, one_smul, mul_zero,
      zero_smul, add_zero]
    exact hfe
  | succ k ih =>
    have hc := pow_mul_ι_cartan α hf h (k + 1)
    rw [hαh] at hc
    calc ι f ^ (k + 1 + 1) * ι e = ι f * (ι f ^ (k + 1) * ι e) := by
          rw [pow_succ' (ι f) (k + 1), mul_assoc]
      _ = (ι f * ι e) * ι f ^ (k + 1) - ((k : ℂ) + 1) • (ι f ^ (k + 1) * ι (h : L)) +
            (((k : ℂ) + 1) * k) • ι f ^ (k + 1) := by
          rw [ih, mul_add, mul_sub, mul_smul_comm, mul_smul_comm, ← mul_assoc, ← mul_assoc,
            ← pow_succ']
      _ = ι e * ι f ^ (k + 1 + 1) - ι (h : L) * ι f ^ (k + 1) -
            ((k : ℂ) + 1) • (ι f ^ (k + 1) * ι (h : L)) +
            (((k : ℂ) + 1) * k) • ι f ^ (k + 1) := by
          rw [hfe, sub_mul, mul_assoc, ← pow_succ']
      _ = ι e * ι f ^ (k + 1 + 1) - (((k + 1 : ℕ) : ℂ) + 1) • (ι f ^ (k + 1) * ι (h : L)) +
            ((((k + 1 : ℕ) : ℂ) + 1) * ((k + 1 : ℕ) : ℂ)) • ι f ^ (k + 1) := by
          have hh : ι (h : L) * ι f ^ (k + 1) =
              ι f ^ (k + 1) * ι (h : L) - ((((k + 1 : ℕ) : ℂ)) * 2) • ι f ^ (k + 1) := by
            rw [hc]
            abel
          rw [hh]
          push_cast
          module

theorem commutatorMap_ι_pow_of_mem_weightSpace {χ : H → ℂ} {x : L}
    (hx : x ∈ weightSpace L χ) (h' : H) (k : ℕ) :
    commutatorMap (h' : L) (ι x ^ k) = ((k : ℂ) * χ h') • ι x ^ k := by
  refine commutatorMap_pow (h' : L) (ι x) (χ h') ?_ k
  have hb : ⁅(h' : L), x⁆ = χ h' • x := (mem_weightSpace _ _).mp hx h'
  rw [commutatorMap_ι, hb, map_smul]

end Sl2

section Basis

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]

local notation "U" => UniversalEnvelopingAlgebra ℂ L
local notation "ι" => UniversalEnvelopingAlgebra.ι ℂ

theorem orderedPBWMonomial_single {n : ℕ} (b : Module.Basis (Fin n) ℂ L) (a : Fin n) (k : ℕ) :
    orderedPBWMonomial b (Pi.single a k) = ι (b a) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, ← orderedPBWMonomial_zero b]
    congr 1
    funext i
    simp
  | succ k ih =>
    rw [pow_succ', ← ih, orderedPBWMonomial, orderedPBWMonomial,
      mul_ofFn_prod_pow_single (fun i => ι (b i)) (Pi.single a k) a (fun i hi hei => by
        rw [Pi.single_eq_of_ne (ne_of_lt hi)] at hei
        exact absurd rfl hei)]
    congr 1
    refine congrArg List.ofFn (funext fun i => ?_)
    by_cases hi : i = a
    · subst hi
      simp
    · simp [Pi.single_eq_of_ne hi]

variable {H : LieSubalgebra ℂ L} {X : H}

theorem monomialRootWeight_single {n : ℕ} (w : Fin n → H → ℂ) (a : Fin n) (k : ℕ) :
    monomialRootWeight w (Pi.single a k) = fun h => (k : ℂ) * w a h := by
  funext h
  rw [monomialRootWeight, Finset.sum_eq_single a (fun i _ hi => by
    rw [Pi.single_eq_of_ne hi, Nat.cast_zero, zero_mul]) (fun ha => absurd (Finset.mem_univ a) ha),
    Pi.single_eq_same]

namespace SortedWeightBasis

variable (B : SortedWeightBasis H X)

/-- A nonzero vector of a nonzero weight is a multiple of the basis vector of that weight. -/
theorem exists_eq_smul {ψ : H → ℂ} (hψ : ψ ≠ 0) {x : L} (hx : x ∈ weightSpace L ψ)
    (hx0 : x ≠ 0) : ∃ (a : Fin B.n) (c : ℂ), B.w a = ψ ∧ c ≠ 0 ∧ x = c • B.b a := by
  classical
  have hsupp : B.b.repr x ≠ 0 := fun h => hx0 (B.b.repr.injective (h.trans (map_zero _).symm))
  obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr hsupp
  have hwa : B.w a = ψ :=
    weight_eq_of_basis_repr_ne_zero B.b B.w B.mem hx (Finsupp.mem_support_iff.mp ha)
  refine ⟨a, B.b.repr x a, hwa, Finsupp.mem_support_iff.mp ha, ?_⟩
  have hrepr : B.b.repr x = Finsupp.single a (B.b.repr x a) := by
    ext a'
    by_cases h' : a' = a
    · subst h'
      rw [Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne' (Ne.symm h')]
      by_contra hne
      have hwa' := weight_eq_of_basis_repr_ne_zero B.b B.w B.mem hx hne
      exact h' (B.line a' a (hwa' ▸ hψ) (hwa'.trans hwa.symm))
  calc x = B.b.repr.symm (B.b.repr x) := (B.b.repr.symm_apply_apply x).symm
    _ = B.b.repr x a • B.b a := by
      conv_lhs => rw [hrepr]
      exact Module.Basis.repr_symm_single _ _ _

end SortedWeightBasis

end Basis

section WallCrossing

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]

local notation "U" => UniversalEnvelopingAlgebra ℂ L
local notation "ι" => UniversalEnvelopingAlgebra.ι ℂ

variable {H : LieSubalgebra ℂ L}

/-- The sum of the weight spaces of the weights with positive real part at both `X` and `X'`. -/
def commonPositiveSubmodule (X X' : H) : Submodule ℂ L :=
  ⨆ (χ : H → ℂ) (_ : 0 < (χ X).re ∧ 0 < (χ X').re), (weightSpace L χ : Submodule ℂ L)

theorem commonPositiveSubmodule_le (X X' : H) :
    commonPositiveSubmodule X X' ≤ positiveRootSubmodule H X :=
  iSup₂_le fun χ hχ => le_iSup₂_of_le (f := fun (χ : H → ℂ) (_ : 0 < (χ X).re) =>
    (weightSpace L χ : Submodule ℂ L)) χ hχ.1 le_rfl

theorem commonPositiveSubmodule_comm (X X' : H) :
    commonPositiveSubmodule X X' = commonPositiveSubmodule X' X := by
  simp only [commonPositiveSubmodule, and_comm]

/-- Two real-regular elements whose positive systems differ exactly in the root `α`, with an
`𝔰𝔩₂`-triple `e, f, h` for `α`. -/
structure WallCrossing (X X' : H) (α : H →ₗ[ℂ] ℂ) (e f : L) (h : H) : Prop where
  pos : 0 < (α X).re
  neg : (α X').re < 0
  adj : ∀ χ : H → ℂ, χ ≠ 0 → weightSpace L χ ≠ ⊥ → χ ≠ ⇑α → χ ≠ -⇑α →
    (0 < (χ X).re ↔ 0 < (χ X').re)
  mem_e : e ∈ weightSpace L ⇑α
  mem_f : f ∈ weightSpace L (-⇑α)
  lie_ef : ⁅e, f⁆ = (h : L)
  apply_h : α h = 2

namespace WallCrossing

variable {X X' : H} {α : H →ₗ[ℂ] ℂ} {e f : L} {h : H} (W : WallCrossing X X' α e f h)
include W

/-- The same data seen from `X'`, with the root `-α` and the triple `f, e, -h`. -/
theorem symm : WallCrossing X' X (-α) f e (-h) where
  pos := by rw [LinearMap.neg_apply, Complex.neg_re]; exact neg_pos.mpr W.neg
  neg := by rw [LinearMap.neg_apply, Complex.neg_re]; exact neg_neg_of_pos W.pos
  adj χ h0 hne h1 h2 := by
    rw [LinearMap.coe_neg] at h1 h2
    rw [neg_neg] at h2
    exact (W.adj χ h0 hne h2 h1).symm
  mem_e := by rw [LinearMap.coe_neg]; exact W.mem_f
  mem_f := by rw [LinearMap.coe_neg, neg_neg]; exact W.mem_e
  lie_ef := by rw [← lie_skew, W.lie_ef]; rfl
  apply_h := by rw [LinearMap.neg_apply, map_neg, neg_neg, W.apply_h]

theorem e_ne_zero : e ≠ 0 := by
  intro he
  have h1 := W.lie_ef
  rw [he, zero_lie] at h1
  have h2 : h = 0 := Subtype.ext h1.symm
  have := W.apply_h
  rw [h2, map_zero] at this
  exact two_ne_zero this.symm

theorem f_ne_zero : f ≠ 0 := W.symm.e_ne_zero

theorem alpha_ne_zero : ⇑α ≠ 0 := by
  intro h0
  have := W.pos
  rw [h0, Pi.zero_apply, Complex.zero_re] at this
  exact lt_irrefl 0 this

theorem weightSpace_alpha_ne_bot : weightSpace L ⇑α ≠ ⊥ :=
  weightSpace_ne_bot_of_mem W.mem_e W.e_ne_zero

theorem weightSpace_neg_alpha_ne_bot : weightSpace L (-⇑α) ≠ ⊥ :=
  weightSpace_ne_bot_of_mem W.mem_f W.f_ne_zero

theorem exists_smul_e (hC : IsSplitCartan H) {x : L} (hx : x ∈ weightSpace L ⇑α) :
    ∃ c : ℂ, x = c • e := by
  have hrank := hC.finrank_weightSpace (⇑α) W.alpha_ne_zero W.weightSpace_alpha_ne_bot
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hrank
    (x := (⟨e, W.mem_e⟩ : weightSpace L ⇑α)) (fun h0 => W.e_ne_zero (congrArg Subtype.val h0))
    ⟨x, hx⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem exists_smul_f (hC : IsSplitCartan H) {x : L} (hx : x ∈ weightSpace L (-⇑α)) :
    ∃ c : ℂ, x = c • f := by
  refine W.symm.exists_smul_e hC ?_
  rw [LinearMap.coe_neg]
  exact hx

theorem positiveRootSubmodule_le :
    positiveRootSubmodule H X ≤ commonPositiveSubmodule X X' ⊔ weightSpace L ⇑α := by
  refine iSup₂_le fun χ hχ => ?_
  by_cases hbot : weightSpace L χ = ⊥
  · rw [hbot]
    exact bot_le
  by_cases hα : χ = ⇑α
  · subst hα
    exact le_sup_right
  have h0 : χ ≠ 0 := by
    rintro rfl
    rw [Pi.zero_apply, Complex.zero_re] at hχ
    exact lt_irrefl 0 hχ
  have hnα : χ ≠ -⇑α := by
    rintro rfl
    rw [Pi.neg_apply, Complex.neg_re] at hχ
    exact absurd hχ (not_lt.mpr (neg_nonpos.mpr W.pos.le))
  have h' := (W.adj χ h0 hbot hα hnα).mp hχ
  exact le_sup_of_le_left (le_iSup₂_of_le (f := fun (χ : H → ℂ)
    (_ : 0 < (χ X).re ∧ 0 < (χ X').re) => (weightSpace L χ : Submodule ℂ L)) χ ⟨hχ, h'⟩ le_rfl)

theorem positiveRootSubmodule_le' :
    positiveRootSubmodule H X' ≤ commonPositiveSubmodule X X' ⊔ weightSpace L (-⇑α) := by
  have := W.symm.positiveRootSubmodule_le
  rwa [commonPositiveSubmodule_comm, LinearMap.coe_neg] at this

theorem lie_f_mem (hC : IsSplitCartan H) {x : L} (hx : x ∈ commonPositiveSubmodule X X') :
    ⁅f, x⁆ ∈ commonPositiveSubmodule X X' := by
  induction hx using Submodule.iSup_induction' with
  | mem χ x hx =>
    induction hx using Submodule.iSup_induction' with
    | mem hχ x hx =>
      by_cases hx0 : x = 0
      · rw [hx0, lie_zero]
        exact Submodule.zero_mem _
      have hmem := bracket_mem_weightSpace_add W.mem_f hx
      by_cases hbot : weightSpace L (-⇑α + χ) = ⊥
      · rw [hbot] at hmem
        rw [(LieSubmodule.mem_bot _).mp hmem]
        exact Submodule.zero_mem _
      have hχbot : weightSpace L χ ≠ ⊥ := weightSpace_ne_bot_of_mem hx hx0
      have h0 : -⇑α + χ ≠ 0 := by
        intro h0
        have hχα : χ = ⇑α := (neg_add_eq_zero.mp h0).symm
        have := hχ.2
        rw [hχα] at this
        exact lt_asymm this W.neg
      have hX' : 0 < ((-⇑α + χ) X').re := by
        rw [Pi.add_apply, Pi.neg_apply, Complex.add_re, Complex.neg_re]
        linarith [hχ.2, W.neg]
      have hneα : -⇑α + χ ≠ ⇑α := by
        intro h2
        have hχ2 : χ = (2 : ℂ) • ⇑α := by
          rw [two_smul]
          exact neg_add_eq_iff_eq_add.mp h2
        rw [hχ2] at hχbot
        rcases hC.reduced (⇑α) W.alpha_ne_zero W.weightSpace_alpha_ne_bot 2 two_ne_zero hχbot
          with h | h
        · norm_num at h
        · norm_num at h
      have hneα' : -⇑α + χ ≠ -⇑α := by
        intro h2
        have hχ0 : χ = 0 := by
          rw [neg_add_eq_iff_eq_add, add_neg_cancel] at h2
          exact h2
        have := hχ.1
        rw [hχ0, Pi.zero_apply, Complex.zero_re] at this
        exact lt_irrefl 0 this
      have hX := (W.adj _ h0 hbot hneα hneα').mpr hX'
      exact le_iSup₂_of_le (f := fun (χ : H → ℂ)
        (_ : 0 < (χ X).re ∧ 0 < (χ X').re) => (weightSpace L χ : Submodule ℂ L))
        (-⇑α + χ) ⟨hX, hX'⟩ le_rfl hmem
    | zero => rw [lie_zero]; exact Submodule.zero_mem _
    | add x y _ _ h₁ h₂ => rw [lie_add]; exact Submodule.add_mem _ h₁ h₂
  | zero => rw [lie_zero]; exact Submodule.zero_mem _
  | add x y _ _ h₁ h₂ => rw [lie_add]; exact Submodule.add_mem _ h₁ h₂

theorem pow_mul_mem (hC : IsSplitCartan H) (k : ℕ) :
    ∀ x ∈ commonPositiveSubmodule X X', ∀ v : U,
      ι f ^ k * (ι x * v) ∈ generatorRightIdeal (commonPositiveSubmodule X X') := by
  induction k with
  | zero =>
    intro x hx v
    rw [pow_zero, one_mul]
    exact generator_mul_mem_generatorRightIdeal _ hx v
  | succ k ih =>
    intro x hx v
    have hfx : ι f * ι x = ι x * ι f + ι ⁅f, x⁆ := by
      rw [LieHom.map_lie, Ring.lie_def]
      abel
    rw [pow_succ, mul_assoc, ← mul_assoc (ι f), hfx, add_mul, mul_add, mul_assoc]
    exact Submodule.add_mem _ (ih x hx _) (ih _ (W.lie_f_mem hC hx) v)

end WallCrossing

end WallCrossing

section WallCrossingVerma

variable {L : Type v} [LieRing L] [LieAlgebra ℂ L]

local notation "U" => UniversalEnvelopingAlgebra ℂ L
local notation "ι" => UniversalEnvelopingAlgebra.ι ℂ

variable {H : LieSubalgebra ℂ L}

theorem mem_positiveRootSubmodule {X : H} {χ : H → ℂ} (hχ : 0 < (χ X).re) {x : L}
    (hx : x ∈ weightSpace L χ) : x ∈ positiveRootSubmodule H X :=
  (le_iSup₂_of_le (f := fun (χ : H → ℂ) (_ : 0 < (χ X).re) =>
    (weightSpace L χ : Submodule ℂ L)) χ hχ le_rfl) hx

theorem commutatorMap_eq_zero_of_mem_center {z : U} (hz : z ∈ Subalgebra.center ℂ U) (x : L) :
    commutatorMap x z = 0 := by
  rw [commutatorMap_apply, Subalgebra.mem_center_iff.mp hz (ι x), sub_self]

theorem pow_mul_cartan_sub (α : H →ₗ[ℂ] ℂ) {f : L} (hf : f ∈ weightSpace L (-⇑α)) (k : ℕ)
    (lam : H →ₗ[ℂ] ℂ) (h' : H) :
    ι f ^ k * (ι (h' : L) - algebraMap ℂ U ((lam + (k : ℂ) • α) h')) =
      (ι (h' : L) - algebraMap ℂ U (lam h')) * ι f ^ k := by
  rw [mul_sub, pow_mul_ι_cartan α hf h' k, sub_mul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, map_add]
  simp only [Algebra.algebraMap_eq_smul_one, mul_add, mul_smul_comm, smul_mul_assoc, mul_one,
    one_mul]
  module

theorem range_mulLeft_mul_mem (u : U) {x : U} (hx : x ∈ LinearMap.range (LinearMap.mulLeft ℂ u))
    (y : U) : x * y ∈ LinearMap.range (LinearMap.mulLeft ℂ u) := by
  obtain ⟨v, rfl⟩ := hx
  exact ⟨v * y, by simp [mul_assoc]⟩

theorem single_mem_realNegativeLetterSpan {X : H} {n : ℕ} (b : Module.Basis (Fin n) ℂ L)
    (w : Fin n → H → ℂ) (a : Fin n) (ha : realWeight w X a < 0) (k : ℕ) :
    orderedPBWMonomial b (Pi.single a k) ∈ realNegativeLetterSpan b w X := by
  refine Submodule.subset_span ⟨Pi.single a k, fun i hi => ?_, orderedPBWBasisOf_apply _ _⟩
  by_cases hia : i = a
  · rw [hia]
    exact ha
  · rw [Pi.single_eq_of_ne hia] at hi
    exact absurd rfl hi

namespace WallCrossing

variable [FiniteDimensional ℂ L] {X X' : H} {α : H →ₗ[ℂ] ℂ} {e f : L} {h : H}
  (W : WallCrossing X X' α e f h) (hC : IsSplitCartan H)
include W hC

omit [FiniteDimensional ℂ L] in
/-- `f^{m+1}` is a singular vector of weight `λ + (m+1)α` modulo `R_X(λ)` when `λ(h) = -m`. -/
theorem pow_succ_mul_mem_vermaIdeal (m : ℕ) (lam : H →ₗ[ℂ] ℂ) (hlam : lam h = -m) {r : U}
    (hr : r ∈ vermaIdeal H X (lam + ((m : ℂ) + 1) • α)) :
    ι f ^ (m + 1) * r ∈ vermaIdeal H X lam := by
  refine mul_mem_of_mem_vermaIdeal X _ (vermaIdeal H X lam)
    (fun _ hr y => vermaIdeal_mul_mem X lam hr y) _ ?_ ?_ hr
  · intro x hx
    obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Submodule.mem_sup.mp (W.positiveRootSubmodule_le hx)
    obtain ⟨c, rfl⟩ := W.exists_smul_e hC hx₁
    rw [map_add, mul_add, map_smul, mul_smul_comm]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ c ?_)
    · have := W.pow_mul_mem hC (m + 1) x₀ hx₀ 1
      rw [mul_one] at this
      exact generatorRightIdeal_le_vermaIdeal X lam (commonPositiveSubmodule_le X X') this
    · have hc := pow_mul_ι_cartan α W.mem_f h m
      rw [W.apply_h] at hc
      rw [pow_succ_mul_ι_e α W.mem_f W.lie_ef W.apply_h m, hc]
      have key : ι e * ι f ^ (m + 1) - ((m : ℂ) + 1) • (ι (h : L) * ι f ^ m +
            ((m : ℂ) * 2) • ι f ^ m) + (((m : ℂ) + 1) * m) • ι f ^ m =
          ι e * ι f ^ (m + 1) -
            ((m : ℂ) + 1) • ((ι (h : L) - algebraMap ℂ U (lam h)) * ι f ^ m) := by
        rw [hlam, sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
        module
      rw [key]
      exact Submodule.sub_mem _
        (positive_mul_mem_vermaIdeal X lam (mem_positiveRootSubmodule W.pos W.mem_e) _)
        (Submodule.smul_mem _ _ (cartan_mul_mem_vermaIdeal X lam h _))
  · intro h'
    have := pow_mul_cartan_sub α W.mem_f (m + 1) lam h'
    push_cast at this
    rw [this]
    exact cartan_mul_mem_vermaIdeal X lam h' _

omit [FiniteDimensional ℂ L] in
/-- `f^m` is a singular vector of weight `λ + mα` for `X'` modulo `R_X(λ) + f^{m+1} U(𝔤)`. -/
theorem pow_mul_mem_sup (m : ℕ) (lam : H →ₗ[ℂ] ℂ) {r : U}
    (hr : r ∈ vermaIdeal H X' (lam + (m : ℂ) • α)) :
    ι f ^ m * r ∈ vermaIdeal H X lam ⊔ LinearMap.range (LinearMap.mulLeft ℂ (ι f ^ (m + 1))) := by
  refine mul_mem_of_mem_vermaIdeal X' _ _
    (fun _ hr y => sup_mul_mem (fun _ hr y => vermaIdeal_mul_mem X lam hr y)
      (fun _ hr y => range_mulLeft_mul_mem _ hr y) hr y) _ ?_ ?_ hr
  · intro x hx
    obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := Submodule.mem_sup.mp (W.positiveRootSubmodule_le' hx)
    obtain ⟨c, rfl⟩ := W.exists_smul_f hC hx₁
    rw [map_add, mul_add, map_smul, mul_smul_comm]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
      (Submodule.smul_mem _ c (Submodule.mem_sup_right ⟨1, ?_⟩))
    · have := W.pow_mul_mem hC m x₀ hx₀ 1
      rw [mul_one] at this
      exact generatorRightIdeal_le_vermaIdeal X lam (commonPositiveSubmodule_le X X') this
    · simp [pow_succ]
  · intro h'
    rw [pow_mul_cartan_sub α W.mem_f m lam h']
    exact Submodule.mem_sup_left (cartan_mul_mem_vermaIdeal X lam h' _)

omit [FiniteDimensional ℂ L] hC in
theorem pow_eq_smul_monomial (B : SortedWeightBasis H X) :
    ∃ (a : Fin B.n) (c : ℂ), B.w a = -⇑α ∧ c ≠ 0 ∧ realWeight B.w X a < 0 ∧
      ∀ k : ℕ, ι f ^ k = c ^ k • orderedPBWMonomial B.b (Pi.single a k) := by
  obtain ⟨a, c, hwa, hc, hfa⟩ :=
    B.exists_eq_smul (neg_ne_zero.mpr W.alpha_ne_zero) W.mem_f W.f_ne_zero
  refine ⟨a, c, hwa, hc, ?_, fun k => ?_⟩
  · rw [realWeight, hwa, Pi.neg_apply, Complex.neg_re]
    exact neg_neg_of_pos W.pos
  · rw [orderedPBWMonomial_single, hfa, map_smul, smul_pow]

/-- No power of `f` lies in `R_X(λ)`. -/
theorem pow_not_mem_vermaIdeal (hX : IsRealRegular H X) (k : ℕ) (lam : H →ₗ[ℂ] ℂ) :
    ι f ^ k ∉ vermaIdeal H X lam := by
  obtain ⟨B⟩ := hC.nonempty_sortedWeightBasis hX
  obtain ⟨a, c, -, hc, hneg, hpow⟩ := W.pow_eq_smul_monomial B
  rw [← B.basisVermaIdeal_eq hC.isLieAbelian, hpow]
  refine not_mem_basisVermaIdeal B.b B.w B.lie_eq X (B.param lam) B.zero B.antitone
    (Submodule.smul_mem _ _ (single_mem_realNegativeLetterSpan B.b B.w a hneg k)) ?_
  refine smul_ne_zero (pow_ne_zero _ hc) ?_
  rw [← orderedPBWBasisOf_apply]
  exact (orderedPBWBasisOf B.b).ne_zero _

/-- `f^m` does not lie in `R_X(λ) + f^{m+1} U(𝔤)` when `λ(h) = -m`. -/
theorem pow_not_mem_sup (hX : IsRealRegular H X) (m : ℕ) (lam : H →ₗ[ℂ] ℂ)
    (hlam : lam h = -m) :
    ι f ^ m ∉ vermaIdeal H X lam ⊔ LinearMap.range (LinearMap.mulLeft ℂ (ι f ^ (m + 1))) := by
  intro hmem
  obtain ⟨B⟩ := hC.nonempty_sortedWeightBasis hX
  obtain ⟨a, c, hwa, hc, hneg, hpow⟩ := W.pow_eq_smul_monomial B
  have hnegspan : ∀ k, ι f ^ k ∈ realNegativeLetterSpan B.b B.w X := fun k => by
    rw [hpow k]
    exact Submodule.smul_mem _ _ (single_mem_realNegativeLetterSpan B.b B.w a hneg k)
  obtain ⟨r, hr, t, ⟨x, rfl⟩, heq⟩ := Submodule.mem_sup.mp hmem
  rw [← B.basisVermaIdeal_eq hC.isLieAbelian] at hr
  obtain ⟨y, hy, hyeq⟩ := exists_eq_mul_of_mem_sup B.b B.w B.lie_eq X B.zero B.antitone
    B.neg_letters_lie (B.param lam) (B.param (lam + ((m : ℂ) + 1) • α)) (ι f ^ (m + 1))
    (hnegspan (m + 1))
    (fun r hr => by
      rw [B.basisVermaIdeal_eq hC.isLieAbelian] at hr ⊢
      exact W.pow_succ_mul_mem_vermaIdeal hC m lam hlam hr)
    (hnegspan m) ⟨r, hr, x, heq.symm⟩
  have h1 : (orderedPBWBasisOf B.b).repr (ι f ^ m) (Pi.single a m) = c ^ m := by
    rw [hpow m, map_smul, ← orderedPBWBasisOf_apply, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
  have heig : ∀ (e' : Fin B.n → ℕ) (h' : H),
      commutatorMap (h' : L) (ι f ^ (m + 1) * orderedPBWMonomial B.b e') =
        (((m : ℂ) + 1) * (-(α h')) + monomialRootWeight B.w e' h') •
          (ι f ^ (m + 1) * orderedPBWMonomial B.b e') := by
    intro e' h'
    rw [commutatorMap_mul, commutatorMap_ι_pow_of_mem_weightSpace W.mem_f,
      commutatorMap_orderedPBWMonomial B.b B.w B.lie_eq, smul_mul_assoc, mul_smul_comm,
      ← add_smul]
    push_cast
    rfl
  have h2 : (orderedPBWBasisOf B.b).repr (ι f ^ (m + 1) * y) (Pi.single a m) = 0 := by
    rw [← (orderedPBWBasisOf B.b).linearCombination_repr y, Finsupp.linearCombination_apply,
      Finsupp.sum, Finset.mul_sum, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun e' he' => ?_
    rw [mul_smul_comm, map_smul, Finsupp.smul_apply, orderedPBWBasisOf_apply]
    have hen : ∀ i, e' i ≠ 0 → realWeight B.w X i < 0 := by
      intro i hi
      by_contra hnot
      exact (Finsupp.mem_support_iff.mp he') (repr_eq_zero_of_mem_span _ _ hy
        (fun h' => hnot (h' i hi)))
    by_contra hne
    rw [smul_eq_mul] at hne
    have hne' := right_ne_zero_of_mul hne
    have hwt := monomialRootWeight_eq_of_mem_support B.b B.w B.lie_eq
      (ι f ^ (m + 1) * orderedPBWMonomial B.b e')
      (fun h' => ((m : ℂ) + 1) * (-(α h')) + monomialRootWeight B.w e' h') (heig e')
      (Pi.single a m) (Finsupp.mem_support_iff.mpr hne')
    rw [monomialRootWeight_single, hwa] at hwt
    have hX' := congrFun hwt X
    simp only [Pi.neg_apply] at hX'
    have hval : monomialRootWeight B.w e' X = α X := by linear_combination -hX'
    have hre := congrArg Complex.re hval
    rw [realWeight_sum] at hre
    have hle : ∑ i, (e' i : ℝ) * realWeight B.w X i ≤ 0 := Finset.sum_nonpos fun i _ => by
      by_cases hi : e' i = 0
      · simp [hi]
      · exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hen i hi).le
    linarith [W.pos]
  rw [hyeq, h2] at h1
  exact pow_ne_zero m hc h1.symm

/-- Comparison of `R_X(λ)` and `R_X(λ + (m+1)α)` through the singular vector `f^{m+1}`. -/
theorem eq_of_sub_mem_shift (hX : IsRealRegular H X) (m : ℕ) (lam : H →ₗ[ℂ] ℂ)
    (hlam : lam h = -m) {z : U} (hz : z ∈ Subalgebra.center ℂ U) {s s' : ℂ}
    (h₁ : z - algebraMap ℂ U s ∈ vermaIdeal H X lam)
    (h₂ : z - algebraMap ℂ U s' ∈ vermaIdeal H X (lam + ((m : ℂ) + 1) • α)) : s = s' :=
  eq_of_sub_mem_of_mul_sub_mem (vermaIdeal H X lam) (fun _ hr y => vermaIdeal_mul_mem X lam hr y)
    z (ι f ^ (m + 1)) (Subalgebra.mem_center_iff.mp hz _).symm s s' h₁
    (W.pow_succ_mul_mem_vermaIdeal hC m lam hlam h₂) (W.pow_not_mem_vermaIdeal hC hX (m + 1) lam)

/-- Comparison of `R_X(λ)` and `R_{X'}(λ + mα)` through the singular vector `f^m`. -/
theorem eq_of_sub_mem_cross (hX : IsRealRegular H X) (m : ℕ) (lam : H →ₗ[ℂ] ℂ)
    (hlam : lam h = -m) {z : U} (hz : z ∈ Subalgebra.center ℂ U) {s s' : ℂ}
    (h₁ : z - algebraMap ℂ U s ∈ vermaIdeal H X lam)
    (h₂ : z - algebraMap ℂ U s' ∈ vermaIdeal H X' (lam + (m : ℂ) • α)) : s = s' :=
  eq_of_sub_mem_of_mul_sub_mem _
    (fun _ hr y => sup_mul_mem (fun _ hr y => vermaIdeal_mul_mem X lam hr y)
      (fun _ hr y => range_mulLeft_mul_mem _ hr y) hr y)
    z (ι f ^ m) (Subalgebra.mem_center_iff.mp hz _).symm s s' (Submodule.mem_sup_left h₁)
    (W.pow_mul_mem_sup hC m lam h₂) (W.pow_not_mem_sup hC hX m lam hlam)

/-- The wall-crossing identity on the hyperplanes `λ(h) = -m`. -/
theorem sub_mem_vermaIdeal_of_eq_neg_nat (hX : IsRealRegular H X) (hX' : IsRealRegular H X')
    (m : ℕ) (lam : H →ₗ[ℂ] ℂ) (hlam : lam h = -m) {z : U} (hz : z ∈ Subalgebra.center ℂ U)
    {s : ℂ} (h₁ : z - algebraMap ℂ U s ∈ vermaIdeal H X lam) :
    z - algebraMap ℂ U s ∈ vermaIdeal H X' (lam - α) := by
  have hzc : ∀ h' : H, commutatorMap (h' : L) z = 0 := fun h' =>
    commutatorMap_eq_zero_of_mem_center hz _
  obtain ⟨s₁, hs₁⟩ := exists_sub_mem_vermaIdeal hC hX' z hzc (lam + (m : ℂ) • α)
  have e1 := W.eq_of_sub_mem_cross hC hX m lam hlam hz h₁ hs₁
  obtain ⟨s₂, hs₂⟩ := exists_sub_mem_vermaIdeal hC hX' z hzc (lam - α)
  have hlam' : (lam + (m : ℂ) • α) (-h) = -m := by
    rw [LinearMap.add_apply, LinearMap.smul_apply, map_neg, map_neg, hlam, W.apply_h,
      smul_eq_mul]
    ring
  have hshift : lam + (m : ℂ) • α + ((m : ℂ) + 1) • (-α) = lam - α := by
    ext x
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply,
      LinearMap.sub_apply, smul_eq_mul]
    ring
  have e2 := W.symm.eq_of_sub_mem_shift hC hX' m (lam + (m : ℂ) • α) hlam' hz hs₁
    (by rw [hshift]; exact hs₂)
  rw [e1, e2]
  exact hs₂

/-- **Wall crossing.** If `z` is central and `z ≡ s` modulo `R_X(λ)`, then `z ≡ s` modulo
`R_{X'}(λ - α)`. -/
theorem sub_mem_vermaIdeal (hX : IsRealRegular H X) (hX' : IsRealRegular H X')
    (lam : H →ₗ[ℂ] ℂ) {z : U} (hz : z ∈ Subalgebra.center ℂ U) {s : ℂ}
    (h₁ : z - algebraMap ℂ U s ∈ vermaIdeal H X lam) :
    z - algebraMap ℂ U s ∈ vermaIdeal H X' (lam - α) := by
  have hzc : ∀ h' : H, commutatorMap (h' : L) z = 0 := fun h' =>
    commutatorMap_eq_zero_of_mem_center hz _
  let ω : H →ₗ[ℂ] ℂ := (2 : ℂ)⁻¹ • α
  have hω : ω h = 1 := by
    simp only [ω, LinearMap.smul_apply, W.apply_h, smul_eq_mul]
    norm_num
  obtain ⟨P, hP⟩ := exists_polynomial_sub_mem_vermaIdeal hC hX z hzc lam ω
  obtain ⟨Q, hQ⟩ := exists_polynomial_sub_mem_vermaIdeal hC hX' z hzc (lam - α) ω
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    have hsub : Set.range (fun m : ℕ => -lam h - (m : ℂ)) ⊆ {x | P.eval x = Q.eval x} := by
      rintro _ ⟨m, rfl⟩
      have hl : (lam + (-lam h - (m : ℂ)) • ω) h = -m := by
        rw [LinearMap.add_apply, LinearMap.smul_apply, hω, smul_eq_mul, mul_one]
        ring
      have h₂ := W.sub_mem_vermaIdeal_of_eq_neg_nat hC hX hX' m _ hl hz (hP _)
      have heq : lam + (-lam h - (m : ℂ)) • ω - α = lam - α + (-lam h - (m : ℂ)) • ω := by
        abel
      rw [heq] at h₂
      exact eq_of_sub_mem_vermaIdeal hC hX' _ z h₂ (hQ _)
    refine Set.Infinite.mono hsub (Set.infinite_range_of_injective ?_)
    intro m₁ m₂ hm
    simp only [sub_right_inj] at hm
    exact_mod_cast hm
  have h0 : z - algebraMap ℂ U (P.eval 0) ∈ vermaIdeal H X lam := by
    simpa using hP 0
  have hs : s = P.eval 0 := eq_of_sub_mem_vermaIdeal hC hX lam z h₁ h0
  rw [hs, hPQ]
  simpa using hQ 0

end WallCrossing

end WallCrossingVerma

end Langlands.Algebra.HarishChandra
