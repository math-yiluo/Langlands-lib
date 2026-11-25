import Langlands.LinearAlgebra.Symplectic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.RingInvo

/-!
# `ε`-Hermitian forms over a division ring with involution

GKT Appendix B.2.1 (Definitions B.4, B.7, Proposition B.16) and §4.2.1 (the orthogonal
complement, Lemma 4.11 (b), (c)), §4.3.1 (Lemma 4.18).

Let `D` be a division ring with an involution `τ` (a `RingInvo D`, `d ↦ d^τ`) and `ε = ±1`.
An `ε`-Hermitian form on a left `D`-module `V` is a biadditive map `h : V → V → D` with
`h (a • x) y = a * h x y` and `h y x = ε * (h x y)^τ`; it follows that
`h x (a • y) = h x y * a^τ` (GKT Definition B.4, left spaces). Non-degeneracy is the separate
predicate `Nondegenerate`. The book's right `ε`-Hermitian spaces of chapter 4 are left spaces for
the twisted action `d · w = w d^τ` (GKT Proposition B.6); see the page.

The orthogonal complement `h.orthogonal U = {v | ∀ u ∈ U, h v u = 0}` satisfies
`dim U + dim U^⊥ = dim V` and `U^⊥⊥ = U` for a non-degenerate form on a finite-dimensional space;
a subspace on which `h` is non-degenerate is complementary to its orthogonal (Lemma 4.18).
-/

noncomputable section

namespace Langlands

open Module

section Conj

variable {D : Type*} [Ring D]

/-- The involution `τ` of a ring as a map `D → D`, `d ↦ d^τ` (GKT 4.1.1, B.1). -/
def RingInvo.conj (τ : _root_.RingInvo D) (d : D) : D := MulOpposite.unop (τ d)

namespace RingInvo

variable (τ : _root_.RingInvo D)

@[simp] theorem conj_conj (d : D) : conj τ (conj τ d) = d := τ.involution d

@[simp] theorem conj_add (a b : D) : conj τ (a + b) = conj τ a + conj τ b := by
  simp [conj, map_add]

@[simp] theorem conj_mul (a b : D) : conj τ (a * b) = conj τ b * conj τ a := by
  simp [conj, map_mul]

@[simp] theorem conj_zero : conj τ (0 : D) = 0 := by simp [conj]

@[simp] theorem conj_one : conj τ (1 : D) = 1 := by simp [conj]

@[simp] theorem conj_neg (a : D) : conj τ (-a) = -conj τ a := by simp [conj, map_neg]

@[simp] theorem conj_sub (a b : D) : conj τ (a - b) = conj τ a - conj τ b := by
  simp [conj, map_sub]

@[simp] theorem conj_intCast (n : ℤ) : conj τ (n : D) = n := by simp [conj, map_intCast]

@[simp] theorem conj_natCast (n : ℕ) : conj τ (n : D) = n := by simp [conj, map_natCast]

/-- The involution of a commutative ring given by an involutive ring endomorphism `c`, as a
`RingInvo` (`conj_ofInvolutive`: its `conj` is `c`). -/
def ofInvolutive {R : Type*} [CommRing R] (c : R →+* R) (hc : Function.Involutive c) :
    _root_.RingInvo R :=
  _root_.RingInvo.mk' ((RingEquiv.toOpposite R).toRingHom.comp c) fun r => hc r

@[simp] theorem conj_ofInvolutive {R : Type*} [CommRing R] (c : R →+* R)
    (hc : Function.Involutive c) (a : R) : conj (ofInvolutive c hc) a = c a :=
  rfl

@[simp] theorem conj_ofNat (n : ℕ) [n.AtLeastTwo] : conj τ (OfNat.ofNat n : D) = OfNat.ofNat n :=
  conj_natCast τ n

@[simp] theorem conj_two : conj τ (2 : D) = 2 := by
  have := conj_natCast τ 2
  rwa [Nat.cast_ofNat] at this

theorem conj_injective : Function.Injective (conj τ) :=
  Function.LeftInverse.injective (conj_conj τ)

theorem conj_surjective : Function.Surjective (conj τ) :=
  Function.RightInverse.surjective (conj_conj τ)

@[simp] theorem conj_eq_zero_iff {a : D} : conj τ a = 0 ↔ a = 0 :=
  ⟨fun h => conj_injective τ (by rw [h, RingInvo.conj_zero]),
    fun h => by rw [h, RingInvo.conj_zero]⟩

theorem conj_sum {ι : Type*} (s : Finset ι) (f : ι → D) :
    conj τ (∑ i ∈ s, f i) = ∑ i ∈ s, conj τ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, RingInvo.conj_add, ih]

@[simp] theorem conj_id_apply {R : Type*} [CommRing R] (d : R) :
    conj (_root_.RingInvo.id R) d = d := rfl

theorem conj_inv {K : Type*} [DivisionRing K] (σ : _root_.RingInvo K) (a : K) :
    conj σ a⁻¹ = (conj σ a)⁻¹ := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · refine (eq_inv_of_mul_eq_one_left ?_)
    rw [← RingInvo.conj_mul, mul_inv_cancel₀ ha, RingInvo.conj_one]

end RingInvo

end Conj

section Sign

variable {D : Type*} [Ring D]

/-- `ε · ε = 1` for `ε ∈ ℤˣ`, read in a ring. -/
theorem units_int_cast_mul_self' (ε : ℤˣ) : ((ε : ℤ) : D) * ((ε : ℤ) : D) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

/-- An integer commutes with every element. -/
theorem units_int_cast_commute (ε : ℤˣ) (a : D) : ((ε : ℤ) : D) * a = a * ((ε : ℤ) : D) :=
  (Int.cast_commute _ a)

end Sign

/-- An `ε`-Hermitian form on a left module `V` over a division ring `D` with involution `τ`
(GKT Definition B.4, without the non-degeneracy, which is `Nondegenerate`): a map
`h : V → V → D`, additive and left `D`-linear in the first variable, with
`h y x = ε (h x y)^τ`. -/
structure EpsilonHermitianForm {D : Type*} [DivisionRing D] (τ : RingInvo D) (ε : ℤˣ)
    (V : Type*) [AddCommGroup V] [Module D V] where
  /-- The values of the form. -/
  toFun : V → V → D
  map_add_left' : ∀ x y z, toFun (x + y) z = toFun x z + toFun y z
  map_smul_left' : ∀ (a : D) x y, toFun (a • x) y = a * toFun x y
  conj_swap' : ∀ x y, toFun y x = ((ε : ℤ) : D) * RingInvo.conj τ (toFun x y)

namespace EpsilonHermitianForm

open Langlands.RingInvo (conj conj_conj)

variable {D : Type*} [DivisionRing D] {τ : _root_.RingInvo D} {ε : ℤˣ}
  {V : Type*} [AddCommGroup V] [Module D V]

instance : FunLike (EpsilonHermitianForm τ ε V) V (V → D) where
  coe h := h.toFun
  coe_injective h h' e := by cases h; cases h'; congr

variable (h : EpsilonHermitianForm τ ε V)

@[simp] theorem toFun_eq_coe : h.toFun = ⇑h := rfl

@[ext] theorem ext {h h' : EpsilonHermitianForm τ ε V} (H : ∀ x y, h x y = h' x y) : h = h' :=
  DFunLike.coe_injective (funext fun x => funext fun y => H x y)

theorem map_add_left (x y z : V) : h (x + y) z = h x z + h y z := h.map_add_left' x y z

theorem map_smul_left (a : D) (x y : V) : h (a • x) y = a * h x y := h.map_smul_left' a x y

/-- The symmetry `h(y, x) = ε h(x, y)^τ`. -/
theorem conj_swap (x y : V) : h y x = ((ε : ℤ) : D) * conj τ (h x y) := h.conj_swap' x y

theorem conj_apply (x y : V) : conj τ (h x y) = ((ε : ℤ) : D) * h y x := by
  rw [h.conj_swap y x, RingInvo.conj_mul, conj_conj, RingInvo.conj_intCast,
    units_int_cast_commute]

theorem map_add_right (x y z : V) : h x (y + z) = h x y + h x z := by
  rw [h.conj_swap, h.map_add_left, RingInvo.conj_add, mul_add, ← h.conj_swap, ← h.conj_swap]

theorem map_smul_right (a : D) (x y : V) : h x (a • y) = h x y * conj τ a := by
  rw [h.conj_swap, h.map_smul_left, RingInvo.conj_mul, ← mul_assoc, ← h.conj_swap]

@[simp] theorem map_zero_left (y : V) : h 0 y = 0 := by
  simpa using h.map_smul_left 0 0 y

@[simp] theorem map_zero_right (x : V) : h x 0 = 0 := by
  simpa using h.map_smul_right 0 x 0

@[simp] theorem map_neg_left (x y : V) : h (-x) y = -h x y := by
  rw [← neg_one_smul D x, h.map_smul_left, neg_one_mul]

@[simp] theorem map_neg_right (x y : V) : h x (-y) = -h x y := by
  rw [← neg_one_smul D y, h.map_smul_right, RingInvo.conj_neg, RingInvo.conj_one, mul_neg_one]

theorem map_sub_left (x y z : V) : h (x - y) z = h x z - h y z := by
  rw [sub_eq_add_neg, h.map_add_left, h.map_neg_left, ← sub_eq_add_neg]

theorem map_sub_right (x y z : V) : h x (y - z) = h x y - h x z := by
  rw [sub_eq_add_neg, h.map_add_right, h.map_neg_right, ← sub_eq_add_neg]

theorem map_sum_left {ι : Type*} (s : Finset ι) (f : ι → V) (y : V) :
    h (∑ i ∈ s, f i) y = ∑ i ∈ s, h (f i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.map_add_left, ih]

theorem map_sum_right {ι : Type*} (s : Finset ι) (x : V) (f : ι → V) :
    h x (∑ i ∈ s, f i) = ∑ i ∈ s, h x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.map_add_right, ih]

/-- The form vanishes at `(x, y)` if and only if it vanishes at `(y, x)`. -/
theorem apply_eq_zero_comm {x y : V} : h x y = 0 ↔ h y x = 0 := by
  rw [h.conj_swap x y]
  constructor
  · intro e; rw [e, RingInvo.conj_zero, mul_zero]
  · intro e
    have : conj τ (h x y) = 0 := by
      have := congrArg (((ε : ℤ) : D) * ·) e
      simpa [← mul_assoc, units_int_cast_mul_self'] using this
    simpa using this

/-- The value `h(x, x)` satisfies `h(x, x)^τ = ε h(x, x)`. -/
theorem conj_apply_self (x : V) : conj τ (h x x) = ((ε : ℤ) : D) * h x x := h.conj_apply x x

/-- The `D`-linear functional `v ↦ h v y`. -/
def flipApply (y : V) : V →ₗ[D] D where
  toFun v := h v y
  map_add' a b := h.map_add_left a b y
  map_smul' a v := by simp [h.map_smul_left]

@[simp] theorem flipApply_apply (y v : V) : h.flipApply y v = h v y := rfl

/-! ### Restriction, negation, scaling -/

/-- The restriction of the form to a submodule. -/
def restrict (U : Submodule D V) : EpsilonHermitianForm τ ε U where
  toFun x y := h x y
  map_add_left' x y z := h.map_add_left x y z
  map_smul_left' a x y := h.map_smul_left a x y
  conj_swap' x y := h.conj_swap x y

@[simp] theorem restrict_apply (U : Submodule D V) (x y : U) : h.restrict U x y = h x y := rfl

/-- The pullback of the form along a linear map. -/
def comp {V' : Type*} [AddCommGroup V'] [Module D V'] (f : V' →ₗ[D] V) :
    EpsilonHermitianForm τ ε V' where
  toFun x y := h (f x) (f y)
  map_add_left' x y z := by rw [map_add, h.map_add_left]
  map_smul_left' a x y := by rw [map_smul, h.map_smul_left]
  conj_swap' x y := h.conj_swap _ _

@[simp] theorem comp_apply {V' : Type*} [AddCommGroup V'] [Module D V'] (f : V' →ₗ[D] V)
    (x y : V') : h.comp f x y = h (f x) (f y) := rfl

instance : Neg (EpsilonHermitianForm τ ε V) where
  neg h :=
    { toFun := fun x y => -h x y
      map_add_left' := fun x y z => by rw [h.map_add_left, neg_add]
      map_smul_left' := fun a x y => by rw [h.map_smul_left, mul_neg]
      conj_swap' := fun x y => by rw [RingInvo.conj_neg, mul_neg, ← h.conj_swap] }

@[simp] theorem neg_apply (x y : V) : (-h) x y = -h x y := rfl

/-- The form multiplied by a central element `a` fixed by `τ` (GKT 4.3.4, 4.5.7). -/
def smul (a : D) (ha : ∀ d : D, a * d = d * a) (hτ : conj τ a = a) :
    EpsilonHermitianForm τ ε V where
  toFun x y := a * h x y
  map_add_left' x y z := by rw [h.map_add_left, mul_add]
  map_smul_left' b x y := by rw [h.map_smul_left, ← mul_assoc, ha b, mul_assoc]
  conj_swap' x y := by
    rw [RingInvo.conj_mul, hτ, ← mul_assoc, ← h.conj_swap, ha]

@[simp] theorem smul_apply (a : D) (ha : ∀ d : D, a * d = d * a) (hτ : conj τ a = a) (x y : V) :
    h.smul a ha hτ x y = a * h x y := rfl

/-! ### Non-degeneracy and orthogonal complements -/

/-- The form is non-degenerate: `h x y = 0` for all `y` only for `x = 0`. -/
def Nondegenerate : Prop := ∀ x, (∀ y, h x y = 0) → x = 0

variable {h}

theorem Nondegenerate.eq_zero_of_right (hh : h.Nondegenerate) {y : V} (H : ∀ x, h x y = 0) :
    y = 0 :=
  hh y fun x => (h.apply_eq_zero_comm).1 (H x)

theorem Nondegenerate.ext_left (hh : h.Nondegenerate) {x x' : V} (H : ∀ y, h x y = h x' y) :
    x = x' :=
  sub_eq_zero.1 (hh _ fun y => by rw [h.map_sub_left, H y, sub_self])

theorem Nondegenerate.ext_right (hh : h.Nondegenerate) {y y' : V} (H : ∀ x, h x y = h x y') :
    y = y' :=
  sub_eq_zero.1 (hh.eq_zero_of_right fun x => by rw [h.map_sub_right, H x, sub_self])

variable (h)

/-- The orthogonal complement `U^⊥ = {v | ∀ u ∈ U, h v u = 0}` (GKT §4.2.1). -/
def orthogonal (U : Submodule D V) : Submodule D V where
  carrier := {v | ∀ u ∈ U, h v u = 0}
  add_mem' {a b} ha hb u hu := by
    simp only [Set.mem_ofPred_eq] at *
    rw [h.map_add_left, ha u hu, hb u hu, add_zero]
  zero_mem' u _ := h.map_zero_left u
  smul_mem' c v hv u hu := by
    simp only [Set.mem_ofPred_eq] at *
    rw [h.map_smul_left, hv u hu, mul_zero]

variable {h}

theorem mem_orthogonal {U : Submodule D V} {v : V} :
    v ∈ h.orthogonal U ↔ ∀ u ∈ U, h v u = 0 := Iff.rfl

theorem mem_orthogonal' {U : Submodule D V} {v : V} :
    v ∈ h.orthogonal U ↔ ∀ u ∈ U, h u v = 0 :=
  ⟨fun H u hu => h.apply_eq_zero_comm.1 (H u hu), fun H u hu => h.apply_eq_zero_comm.1 (H u hu)⟩

theorem orthogonal_le_orthogonal {U U' : Submodule D V} (hU : U ≤ U') :
    h.orthogonal U' ≤ h.orthogonal U :=
  fun _ hv u hu => hv u (hU hu)

theorem le_orthogonal_orthogonal (U : Submodule D V) : U ≤ h.orthogonal (h.orthogonal U) :=
  fun u hu _ hv => h.apply_eq_zero_comm.1 (hv u hu)

theorem le_orthogonal_iff {U U' : Submodule D V} : U ≤ h.orthogonal U' ↔ U' ≤ h.orthogonal U :=
  ⟨fun H u hu _ hv => h.apply_eq_zero_comm.1 (H hv u hu),
    fun H u hu _ hv => h.apply_eq_zero_comm.1 (H hv u hu)⟩

@[simp] theorem orthogonal_bot : h.orthogonal ⊥ = ⊤ := by
  ext v
  simp only [mem_orthogonal, Submodule.mem_bot, forall_eq, map_zero_right, Submodule.mem_top]

theorem orthogonal_top (hh : h.Nondegenerate) : h.orthogonal ⊤ = ⊥ := by
  ext v
  simp only [mem_orthogonal, Submodule.mem_top, forall_const, Submodule.mem_bot]
  exact ⟨hh v, fun e y => by rw [e, map_zero_left]⟩

theorem orthogonal_sup (U U' : Submodule D V) :
    h.orthogonal (U ⊔ U') = h.orthogonal U ⊓ h.orthogonal U' := by
  apply le_antisymm
  · exact le_inf (orthogonal_le_orthogonal le_sup_left) (orthogonal_le_orthogonal le_sup_right)
  · intro v ⟨hv, hv'⟩ w hw
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.1 hw
    rw [h.map_add_right, hv u hu, hv' u' hu', add_zero]

theorem mem_orthogonal_span_singleton {x v : V} :
    v ∈ h.orthogonal (D ∙ x) ↔ h v x = 0 := by
  constructor
  · intro H; exact H x (Submodule.mem_span_singleton_self x)
  · intro H u hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
    rw [h.map_smul_right, H, zero_mul]

theorem orthogonal_iSup {ι : Type*} (U : ι → Submodule D V) :
    h.orthogonal (⨆ i, U i) = ⨅ i, h.orthogonal (U i) := by
  apply le_antisymm
  · exact le_iInf fun i => orthogonal_le_orthogonal (le_iSup U i)
  · intro v hv
    rw [Submodule.mem_iInf] at hv
    have : ⨆ i, U i ≤ h.orthogonal (D ∙ v) := iSup_le fun i u hu => by
      rw [mem_orthogonal_span_singleton]; exact h.apply_eq_zero_comm.1 (hv i u hu)
    intro u hu
    exact h.apply_eq_zero_comm.1 (mem_orthogonal_span_singleton.1 (this hu))

/-! ### Dimension of the orthogonal complement -/

section FiniteDimensional

variable [FiniteDimensional D V]

/-- The linear map `V → D^m`, `v ↦ (h v (b i))ᵢ`, for a basis `b` of `U`. -/
private def coordMap (h : EpsilonHermitianForm τ ε V) (U : Submodule D V) :
    V →ₗ[D] (Fin (finrank D U) → D) :=
  LinearMap.pi fun i => h.flipApply ((Module.finBasis D U i : U) : V)

private theorem coordMap_apply (U : Submodule D V) (v : V) (i : Fin (finrank D U)) :
    coordMap h U v i = h v ((Module.finBasis D U i : U) : V) := rfl

private theorem ker_coordMap (U : Submodule D V) :
    LinearMap.ker (coordMap h U) = h.orthogonal U := by
  ext v
  rw [LinearMap.mem_ker, mem_orthogonal]
  constructor
  · intro H u hu
    have hv : ∀ i, h v ((Module.finBasis D U i : U) : V) = 0 := fun i => by
      rw [← coordMap_apply, H, Pi.zero_apply]
    have hu' := (Module.finBasis D U).sum_repr ⟨u, hu⟩
    have : u = ∑ i, (Module.finBasis D U).repr ⟨u, hu⟩ i • ((Module.finBasis D U i : U) : V) := by
      have := congrArg Subtype.val hu'
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    rw [this, h.map_sum_right]
    exact Finset.sum_eq_zero fun i _ => by rw [h.map_smul_right, hv i, zero_mul]
  · intro H
    funext i
    rw [coordMap_apply, Pi.zero_apply]
    exact H _ (Module.finBasis D U i).2

private theorem coordMap_surjective (hh : h.Nondegenerate) (U : Submodule D V) :
    Function.Surjective (coordMap h U) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨f, hf, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  set b := Module.finBasis D U
  set c : Fin (finrank D U) → D := fun i => f (Pi.single i 1)
  have hfc : ∀ y, f y = ∑ i, y i * c i := by
    intro y
    conv_lhs => rw [show y = ∑ i, y i • (Pi.single i (1 : D) : Fin (finrank D U) → D) from by
      ext j; simp [Pi.single_apply]]
    simp [map_sum, map_smul, c]
  have key : ∀ v : V, h v (∑ i, conj τ (c i) • ((b i : U) : V)) = 0 := by
    intro v
    have := hle (LinearMap.mem_range_self (coordMap h U) v)
    rw [LinearMap.mem_ker, hfc] at this
    rw [h.map_sum_right]
    simpa [coordMap, h.map_smul_right, LinearMap.pi_apply] using this
  have hz := hh.eq_zero_of_right key
  have hz' : ∑ i, conj τ (c i) • b i = 0 := by
    apply Subtype.ext
    simpa [Submodule.coe_sum] using hz
  have hc : ∀ i, c i = 0 := by
    intro i
    have := (Fintype.linearIndependent_iff.1 b.linearIndependent) _ hz' i
    simpa using this
  apply hf
  apply LinearMap.ext
  intro y
  rw [hfc]
  simp [hc]

/-- `dim U + dim U^⊥ = dim V` for a non-degenerate form on a finite-dimensional space
(GKT Lemma 4.11 (c), for every subspace). -/
theorem finrank_add_finrank_orthogonal (hh : h.Nondegenerate) (U : Submodule D V) :
    finrank D U + finrank D (h.orthogonal U) = finrank D V := by
  have := LinearMap.finrank_range_add_finrank_ker (coordMap h U)
  rwa [LinearMap.range_eq_top.2 (coordMap_surjective hh U), finrank_top, Module.finrank_fin_fun,
    ker_coordMap] at this

/-- `U^⊥⊥ = U` (GKT Lemma 4.11 (b)). -/
theorem orthogonal_orthogonal (hh : h.Nondegenerate) (U : Submodule D V) :
    h.orthogonal (h.orthogonal U) = U := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq (le_orthogonal_orthogonal U)
  have h1 := finrank_add_finrank_orthogonal hh U
  have h2 := finrank_add_finrank_orthogonal hh (h.orthogonal U)
  omega

theorem orthogonal_le_orthogonal_iff (hh : h.Nondegenerate) {U U' : Submodule D V} :
    h.orthogonal U ≤ h.orthogonal U' ↔ U' ≤ U :=
  ⟨fun H => by
    simpa [orthogonal_orthogonal hh] using orthogonal_le_orthogonal (h := h) H,
    orthogonal_le_orthogonal⟩

theorem orthogonal_injective (hh : h.Nondegenerate) : Function.Injective h.orthogonal :=
  fun U U' e => by rw [← orthogonal_orthogonal hh U, e, orthogonal_orthogonal hh]

theorem orthogonal_inf (hh : h.Nondegenerate) (U U' : Submodule D V) :
    h.orthogonal (U ⊓ U') = h.orthogonal U ⊔ h.orthogonal U' := by
  rw [← orthogonal_orthogonal hh (h.orthogonal U ⊔ h.orthogonal U'), orthogonal_sup,
    orthogonal_orthogonal hh, orthogonal_orthogonal hh]

theorem orthogonal_eq_bot_iff (hh : h.Nondegenerate) {U : Submodule D V} :
    h.orthogonal U = ⊥ ↔ U = ⊤ := by
  constructor
  · intro e; rw [← orthogonal_orthogonal hh U, e, orthogonal_bot]
  · rintro rfl; exact orthogonal_top hh

end FiniteDimensional

/-! ### Non-degenerate subspaces (GKT Lemma 4.18) -/

theorem restrict_nondegenerate_iff {U : Submodule D V} :
    (h.restrict U).Nondegenerate ↔ U ⊓ h.orthogonal U = ⊥ := by
  constructor
  · intro H
    rw [eq_bot_iff]
    rintro v ⟨hvU, hv⟩
    have := H ⟨v, hvU⟩ fun y => hv y y.2
    simpa using congrArg Subtype.val this
  · intro H x hx
    have : (x : V) ∈ U ⊓ h.orthogonal U := ⟨x.2, fun u hu => hx ⟨u, hu⟩⟩
    rw [H] at this
    exact Subtype.ext ((Submodule.mem_bot D).1 this)

/-- A subspace on which the form is non-degenerate is complementary to its orthogonal
(GKT Lemma 4.18). -/
theorem isCompl_orthogonal_of_restrict_nondegenerate [FiniteDimensional D V]
    (hh : h.Nondegenerate) {U : Submodule D V} (hU : (h.restrict U).Nondegenerate) :
    IsCompl U (h.orthogonal U) := by
  have hd : Disjoint U (h.orthogonal U) := by
    rw [disjoint_iff]; exact restrict_nondegenerate_iff.1 hU
  refine ⟨hd, codisjoint_iff.2 ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  have := Submodule.finrank_sup_add_finrank_inf_eq U (h.orthogonal U)
  rw [disjoint_iff.1 hd, finrank_bot, add_zero, finrank_add_finrank_orthogonal hh] at this
  exact this

/-- The orthogonal of a non-degenerate subspace is non-degenerate (GKT Lemma 4.18). -/
theorem restrict_orthogonal_nondegenerate [FiniteDimensional D V] (hh : h.Nondegenerate)
    {U : Submodule D V} (hU : (h.restrict U).Nondegenerate) :
    (h.restrict (h.orthogonal U)).Nondegenerate := by
  rw [restrict_nondegenerate_iff, orthogonal_orthogonal hh, inf_comm]
  exact restrict_nondegenerate_iff.1 hU

/-! ### Isometries -/

variable (h) in
/-- The isometry group `U(V) = {g ∈ GL_D(V) | h(gv, gv') = h(v, v')}` (GKT B.2.3; the group
`G(W)` of §4.1.3). -/
def isometryGroup : Subgroup (V ≃ₗ[D] V) where
  carrier := {g | ∀ x y, h (g x) (g y) = h x y}
  mul_mem' {g g'} hg hg' x y := by
    change h (g (g' x)) (g (g' y)) = h x y
    rw [hg, hg']
  one_mem' _ _ := rfl
  inv_mem' {g} hg x y := by
    rw [← hg (g⁻¹ x) (g⁻¹ y)]
    change h (g (g.symm x)) (g (g.symm y)) = h x y
    simp

theorem mem_isometryGroup_iff {g : V ≃ₗ[D] V} :
    g ∈ h.isometryGroup ↔ ∀ x y, h (g x) (g y) = h x y := Iff.rfl

@[simp] theorem isometryGroup_apply (g : h.isometryGroup) (x y : V) :
    h ((g : V ≃ₗ[D] V) x) ((g : V ≃ₗ[D] V) y) = h x y := g.2 x y

@[simp] theorem isometryGroup_coe_mul_apply (g g' : h.isometryGroup) (x : V) :
    ((g * g' : h.isometryGroup) : V ≃ₗ[D] V) x = (g : V ≃ₗ[D] V) ((g' : V ≃ₗ[D] V) x) := rfl

@[simp] theorem isometryGroup_coe_one_apply (x : V) :
    ((1 : h.isometryGroup) : V ≃ₗ[D] V) x = x := rfl

@[simp] theorem isometryGroup_coe_inv_apply (g : h.isometryGroup) (x : V) :
    (g : V ≃ₗ[D] V) (((g⁻¹ : h.isometryGroup) : V ≃ₗ[D] V) x) = x :=
  (g : V ≃ₗ[D] V).apply_symm_apply x

@[simp] theorem isometryGroup_coe_inv_apply' (g : h.isometryGroup) (x : V) :
    ((g⁻¹ : h.isometryGroup) : V ≃ₗ[D] V) ((g : V ≃ₗ[D] V) x) = x :=
  (g : V ≃ₗ[D] V).symm_apply_apply x

/-- Two forms agreeing on all pairs of vectors of a basis are equal. -/
theorem ext_basis {ι : Type*} {h' : EpsilonHermitianForm τ ε V} (b : Module.Basis ι D V)
    (H : ∀ i j, h (b i) (b j) = h' (b i) (b j)) : h = h' := by
  have h1 : ∀ i y, h y (b i) = h' y (b i) := fun i y => by
    have : h.flipApply (b i) = h'.flipApply (b i) := b.ext fun j => H j i
    exact LinearMap.congr_fun this y
  have h2 : ∀ i y, h (b i) y = h' (b i) y := fun i y => by
    rw [h.conj_swap, h'.conj_swap, h1]
  ext x y
  have : h.flipApply y = h'.flipApply y := b.ext fun i => h2 i y
  exact LinearMap.congr_fun this x

/-- A linear automorphism is an isometry as soon as it preserves the form on a basis. -/
theorem mem_isometryGroup_of_basis {ι : Type*} (b : Module.Basis ι D V) {g : V ≃ₗ[D] V}
    (H : ∀ i j, h (g (b i)) (g (b j)) = h (b i) (b j)) : g ∈ h.isometryGroup := by
  have := ext_basis (h := h.comp g.toLinearMap) (h' := h) b H
  intro x y
  exact congrArg (fun k : EpsilonHermitianForm τ ε V => k x y) this

/-- An isometry maps orthogonal complements to orthogonal complements. -/
theorem map_orthogonal (g : h.isometryGroup) (U : Submodule D V) :
    (h.orthogonal U).map (g : V ≃ₗ[D] V).toLinearMap =
      h.orthogonal (U.map (g : V ≃ₗ[D] V).toLinearMap) := by
  ext v
  simp only [Submodule.mem_map, LinearEquiv.coe_coe, mem_orthogonal]
  constructor
  · rintro ⟨w, hw, rfl⟩ u ⟨u', hu', rfl⟩
    rw [isometryGroup_apply]; exact hw u' hu'
  · intro H
    refine ⟨((g⁻¹ : h.isometryGroup) : V ≃ₗ[D] V) v, fun u hu => ?_, by simp⟩
    have := H _ ⟨u, hu, rfl⟩
    rwa [← isometryGroup_coe_inv_apply g v, isometryGroup_apply] at this

/-- A linear endomorphism preserving a non-degenerate form is injective. -/
theorem injective_of_map_apply (hh : h.Nondegenerate) {f : V →ₗ[D] V}
    (hf : ∀ x y, h (f x) (f y) = h x y) : Function.Injective f := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  exact (Submodule.mem_bot D).2 (hh v fun y => by rw [← hf, hv, map_zero_left])

/-- A linear endomorphism of a finite-dimensional space preserving a non-degenerate form, as an
element of the isometry group. -/
def ofLinearMap [FiniteDimensional D V] (hh : h.Nondegenerate) (f : V →ₗ[D] V)
    (hf : ∀ x y, h (f x) (f y) = h x y) : h.isometryGroup :=
  ⟨LinearEquiv.ofBijective f ⟨injective_of_map_apply hh hf,
    LinearMap.injective_iff_surjective.1 (injective_of_map_apply hh hf)⟩, hf⟩

@[simp] theorem ofLinearMap_apply [FiniteDimensional D V] (hh : h.Nondegenerate) (f : V →ₗ[D] V)
    (hf : ∀ x y, h (f x) (f y) = h x y) (v : V) :
    ((ofLinearMap hh f hf : h.isometryGroup) : V ≃ₗ[D] V) v = f v := rfl

/-- An additive bijection preserving a non-degenerate form is `D`-linear (GKT Proposition B.16). -/
theorem map_smul_of_map_apply (hh : h.Nondegenerate) (g : V ≃+ V)
    (hg : ∀ x y, h (g x) (g y) = h x y) (a : D) (x : V) : g (a • x) = a • g x := by
  apply hh.ext_left
  intro y
  obtain ⟨y', rfl⟩ := g.surjective y
  rw [hg, h.map_smul_left, h.map_smul_left, hg]

/-- An isometry between two `ε`-Hermitian spaces (GKT Definition B.7). -/
structure IsometryEquiv {V' : Type*} [AddCommGroup V'] [Module D V']
    (h : EpsilonHermitianForm τ ε V) (h' : EpsilonHermitianForm τ ε V') extends V ≃ₗ[D] V' where
  map_app' : ∀ x y, h' (toFun x) (toFun y) = h x y

namespace IsometryEquiv

variable {V' V'' : Type*} [AddCommGroup V'] [Module D V'] [AddCommGroup V''] [Module D V'']
  {h' : EpsilonHermitianForm τ ε V'} {h'' : EpsilonHermitianForm τ ε V''}

instance : EquivLike (IsometryEquiv h h') V V' where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g e _ := by
    rcases f with ⟨f, _⟩; rcases g with ⟨g, _⟩
    congr
    exact LinearEquiv.toEquiv_injective (Equiv.coe_fn_injective e)

instance : SemilinearEquivClass (IsometryEquiv h h') (RingHom.id D) V V' where
  map_add f := f.toLinearEquiv.map_add
  map_smulₛₗ f := f.toLinearEquiv.map_smul

theorem coe_toLinearEquiv (f : IsometryEquiv h h') : ⇑f.toLinearEquiv = ⇑f := rfl

@[simp] theorem map_app (f : IsometryEquiv h h') (x y : V) : h' (f x) (f y) = h x y :=
  f.map_app' x y

/-- An isometry carries orthogonal complements to orthogonal complements. -/
theorem map_orthogonal (f : IsometryEquiv h h') (U : Submodule D V) :
    (h.orthogonal U).map f.toLinearEquiv.toLinearMap =
      h'.orthogonal (U.map f.toLinearEquiv.toLinearMap) := by
  ext v
  simp only [Submodule.mem_map, LinearEquiv.coe_coe, coe_toLinearEquiv, mem_orthogonal]
  constructor
  · rintro ⟨w, hw, rfl⟩ u ⟨u', hu', rfl⟩
    rw [f.map_app]; exact hw u' hu'
  · intro H
    refine ⟨f.toLinearEquiv.symm v, fun u hu => ?_, f.toLinearEquiv.apply_symm_apply v⟩
    have := H _ ⟨u, hu, rfl⟩
    rwa [← f.toLinearEquiv.apply_symm_apply v, coe_toLinearEquiv, f.map_app] at this

/-- The identity isometry. -/
def refl (h : EpsilonHermitianForm τ ε V) : IsometryEquiv h h where
  toLinearEquiv := LinearEquiv.refl D V
  map_app' _ _ := rfl

/-- The inverse isometry. -/
def symm (f : IsometryEquiv h h') : IsometryEquiv h' h where
  toLinearEquiv := f.toLinearEquiv.symm
  map_app' x y := by
    rw [← f.map_app]
    change h' (f.toLinearEquiv (f.toLinearEquiv.symm x)) (f.toLinearEquiv (f.toLinearEquiv.symm y))
      = h' x y
    simp

/-- The composition of isometries. -/
def trans (f : IsometryEquiv h h') (f' : IsometryEquiv h' h'') : IsometryEquiv h h'' where
  toLinearEquiv := f.toLinearEquiv.trans f'.toLinearEquiv
  map_app' x y := by
    change h'' (f' (f x)) (f' (f y)) = h x y
    simp

@[simp] theorem refl_apply (x : V) : refl h x = x := rfl

@[simp] theorem symm_apply_apply (f : IsometryEquiv h h') (x : V) : f.symm (f x) = x :=
  f.toLinearEquiv.symm_apply_apply x

@[simp] theorem apply_symm_apply (f : IsometryEquiv h h') (x : V') : f (f.symm x) = x :=
  f.toLinearEquiv.apply_symm_apply x

@[simp] theorem trans_apply (f : IsometryEquiv h h') (f' : IsometryEquiv h' h'') (x : V) :
    f.trans f' x = f' (f x) := rfl

end IsometryEquiv

/-! ### The symmetric and the alternating bilinear case -/

section Bilinear

variable {F : Type*} [Field F]

/-- A bilinear form `B` with `B y x = ε B x y` is an `ε`-Hermitian form for the trivial involution
(GKT Case 1: `D = F`). -/
def ofBilinForm {W : Type*} [AddCommGroup W] [Module F W] (B : LinearMap.BilinForm F W)
    (hB : ∀ x y, B y x = ((ε : ℤ) : F) * B x y) :
    EpsilonHermitianForm (_root_.RingInvo.id F) ε W where
  toFun x y := B x y
  map_add_left' x y z := by simp
  map_smul_left' a x y := by simp
  conj_swap' x y := hB x y

@[simp] theorem ofBilinForm_apply {W : Type*} [AddCommGroup W] [Module F W]
    (B : LinearMap.BilinForm F W) (hB : ∀ x y, B y x = ((ε : ℤ) : F) * B x y) (x y : W) :
    ofBilinForm B hB x y = B x y := rfl

/-- For a bilinear form, the isometry group is the isometry group of
`Langlands/LinearAlgebra/Symplectic.lean` (for an alternating form, `Sp(W)`). -/
theorem isometryGroup_ofBilinForm {W : Type*} [AddCommGroup W] [Module F W]
    (B : LinearMap.BilinForm F W) (hB : ∀ x y, B y x = ((ε : ℤ) : F) * B x y) :
    (ofBilinForm B hB).isometryGroup = LinearMap.BilinForm.isometryGroup B := rfl

end Bilinear

end EpsilonHermitianForm

/-! ### Right spaces (GKT Proposition B.6) -/

section Right

variable {D : Type*} [DivisionRing D]

/-- A right `D`-module `W` (a module over `Dᵐᵒᵖ`) viewed as a left `D`-module through the
involution, `d · w = w d^τ` (the space `^τW` of GKT Proposition B.6 and §4.1.1). -/
def TwistedRight (_τ : _root_.RingInvo D) (W : Type*) : Type _ := W

namespace TwistedRight

variable (τ : _root_.RingInvo D) (W : Type*) [AddCommGroup W] [Module Dᵐᵒᵖ W]

instance : AddCommGroup (TwistedRight τ W) := ‹AddCommGroup W›

instance : Module D (TwistedRight τ W) :=
  Module.compHom W (τ : D ≃+* Dᵐᵒᵖ).toRingHom

variable {τ W}

/-- The identity map `W → ^τW`. -/
def mk (w : W) : TwistedRight τ W := w

/-- The identity map `^τW → W`. -/
def get (w : TwistedRight τ W) : W := w

theorem smul_def (d : D) (w : TwistedRight τ W) :
    d • w = mk (MulOpposite.op (RingInvo.conj τ d) • get w) := by
  change (τ d) • (get w : W) = (MulOpposite.op (RingInvo.conj τ d) • get w : W)
  simp [RingInvo.conj]

end TwistedRight

variable {τ : _root_.RingInvo D} {ε : ℤˣ} {W : Type*} [AddCommGroup W] [Module Dᵐᵒᵖ W]

/-- GKT Proposition B.6: a right `ε`-Hermitian form on `W` (biadditive,
`⟨w d, w' d'⟩ = d^τ ⟨w, w'⟩ d'`, `⟨w, w'⟩ = ε ⟨w', w⟩^τ`) is, with the same values, a left
`ε`-Hermitian form on `^τW`. -/
def EpsilonHermitianForm.ofRight (f : W → W → D)
    (map_add_left : ∀ x y z, f (x + y) z = f x z + f y z)
    (map_smul_left : ∀ (d : D) x y, f (MulOpposite.op d • x) y = RingInvo.conj τ d * f x y)
    (conj_swap : ∀ x y, f y x = ((ε : ℤ) : D) * RingInvo.conj τ (f x y)) :
    EpsilonHermitianForm τ ε (TwistedRight τ W) where
  toFun x y := f (TwistedRight.get x) (TwistedRight.get y)
  map_add_left' x y z := map_add_left x y z
  map_smul_left' d x y := by
    rw [TwistedRight.smul_def]
    change f (MulOpposite.op (RingInvo.conj τ d) • TwistedRight.get x) _ = _
    rw [map_smul_left, RingInvo.conj_conj]
  conj_swap' x y := conj_swap _ _

end Right

end Langlands

end
