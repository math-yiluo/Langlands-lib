import Langlands.Shimura.Unitary.Involution
import Mathlib.Algebra.Module.Lattice
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! # Finite full orders preserved by an algebra involution -/

noncomputable section

namespace Langlands.Shimura.PEL

section Denominators

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Membership in a rational span allows an integer denominator to be cleared. -/
theorem exists_int_multiple_mem (L : Submodule ℤ V) {x : V}
    (hx : x ∈ Submodule.span ℚ (L : Set V)) :
    ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ L := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨n, hn, hy⟩ := hy
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    simp only [smul_add, mul_smul]
    rw [smul_comm m n x]
    exact L.add_mem (L.smul_mem n hx) (L.smul_mem m hy)
  | smul q x _ hx =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨d, c, hc⟩ :=
      IsLocalization.exists_integer_multiple (nonZeroDivisors ℤ) q
    refine ⟨(d : ℤ) * m,
      mul_ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp d.prop) hm, ?_⟩
    have he : ((d : ℤ) * m) • (q • x) = c • (m • x) := by
      calc
        ((d : ℤ) * m) • (q • x) = m • ((d : ℤ) • (q • x)) := by
          rw [mul_smul, smul_comm]
        _ = m • (((d : ℤ) • q) • x) := by rw [smul_assoc]
        _ = m • ((algebraMap ℤ ℚ c) • x) := by rw [hc]
        _ = c • (m • x) := by rw [algebraMap_smul, smul_comm]
    rw [he]
    exact L.smul_mem c hx

/-- A full rational span permits simultaneous denominator clearing on a finite set. -/
theorem exists_common_int_multiple {ι : Type*} (L : Submodule ℤ V)
    (hL : Submodule.span ℚ (L : Set V) = ⊤) (s : Finset ι) (f : ι → V) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ i ∈ s, m • f i ∈ L := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert i s _ ih =>
    obtain ⟨m, hm, hs⟩ := ih
    obtain ⟨n, hn, hi⟩ := exists_int_multiple_mem L (x := f i) (by rw [hL]; trivial)
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · rw [mul_smul]
      exact L.smul_mem m hi
    · rw [mul_comm, mul_smul]
      exact L.smul_mem n (hs j hj)

end Denominators

section Orders

variable {A : Type*} [Ring A]

/-- The algebra of left multipliers preserving an actual integer submodule. -/
def latticeStabilizer (L : Submodule ℤ A) : Subalgebra ℤ A where
  carrier := {a | ∀ x ∈ L, a * x ∈ L}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' ha hb x hx := by simpa [add_mul] using L.add_mem (ha x hx) (hb x hx)
  mul_mem' ha hb x hx := by simpa [mul_assoc] using ha _ (hb x hx)
  algebraMap_mem' n x hx := by simpa [Algebra.smul_def] using L.smul_mem n hx

@[simp] theorem mem_latticeStabilizer (L : Submodule ℤ A) (a : A) :
    a ∈ latticeStabilizer L ↔ ∀ x ∈ L, a * x ∈ L := Iff.rfl

/-- Left multiplication is a ring action on the actual lattice. -/
def latticeStabilizerAction (L : Submodule ℤ A) :
    latticeStabilizer L →+* Module.End ℤ L where
  toFun a :=
    { toFun := fun x => ⟨a * x, a.prop x x.prop⟩
      map_add' := fun x y => Subtype.ext (mul_add (a : A) x y)
      map_smul' := fun n x => Subtype.ext (mul_smul_comm n (a : A) (x : A)) }
  map_zero' := by ext x; exact zero_mul (x : A)
  map_one' := by ext x; exact one_mul (x : A)
  map_add' := by intros; ext x; exact add_mul _ _ (x : A)
  map_mul' := by intros; ext x; exact mul_assoc _ _ (x : A)

@[simp] theorem latticeStabilizerAction_apply (L : Submodule ℤ A)
    (a : latticeStabilizer L) (x : L) :
    (latticeStabilizerAction L a x : A) = (a : A) * x := rfl

/-- Evaluation at 1 proves that this lattice action is faithful. -/
theorem latticeStabilizerAction_injective (L : Submodule ℤ A) (h1 : (1 : A) ∈ L) :
    Function.Injective (latticeStabilizerAction L) := by
  intro a b h
  apply Subtype.ext
  simpa only [latticeStabilizerAction_apply, mul_one] using
    congrArg (fun f : Module.End ℤ L => (f ⟨1, h1⟩ : A)) h

/-- If the lattice contains 1, evaluation at 1 places the stabilizer in it. -/
def latticeStabilizerEmbedding (L : Submodule ℤ A) (h1 : (1 : A) ∈ L) :
    latticeStabilizer L →ₗ[ℤ] L where
  toFun a := ⟨a, by simpa using a.prop 1 h1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem latticeStabilizer_finite (L : Submodule ℤ A) (hfg : L.FG)
    (h1 : (1 : A) ∈ L) : Module.Finite ℤ (latticeStabilizer L) := by
  have : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hfg
  exact Module.Finite.of_injective (latticeStabilizerEmbedding L h1)
    (fun a b h => Subtype.ext (congrArg (fun x : L => (x : A)) h))

variable [Algebra ℚ A]

/-- Every rational algebra element has an integer multiple preserving a full finite lattice. -/
theorem exists_int_multiple_mem_latticeStabilizer (L : Submodule ℤ A)
    (hfg : L.FG) (hfull : Submodule.span ℚ (L : Set A) = ⊤) (a : A) :
    ∃ m : ℤ, m ≠ 0 ∧ m • a ∈ latticeStabilizer L := by
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨m, hm, hmul⟩ := exists_common_int_multiple L hfull s (fun x => a * x)
  refine ⟨m, hm, ?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => simpa only [smul_mul_assoc] using hmul x hx
  | zero => simp
  | add x y _ _ hx hy => simpa only [mul_add] using L.add_mem hx hy
  | smul n x _ hx => simpa only [mul_smul_comm] using L.smul_mem n hx

/-- An integer-multiple criterion implies fullness over the rational numbers. -/
theorem span_eq_top_of_int_multiples (L : Submodule ℤ A)
    (h : ∀ a : A, ∃ m : ℤ, m ≠ 0 ∧ m • a ∈ L) :
    Submodule.span ℚ (L : Set A) = ⊤ := by
  apply eq_top_iff.mpr
  intro a _
  obtain ⟨m, hm, ha⟩ := h a
  have hma : (m : ℚ) • a ∈ Submodule.span ℚ (L : Set A) := by
    change (algebraMap ℤ ℚ m) • a ∈ _
    rw [algebraMap_smul]
    exact Submodule.subset_span ha
  have hc : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using
    (Submodule.span ℚ (L : Set A)).smul_mem ((m : ℚ)⁻¹) hma

/-- The largest subalgebra of an integer subalgebra preserved by the involution. -/
def involutionStableCore (σ : AlgebraInvolution ℚ A) (O : Subalgebra ℤ A) :
    Subalgebra ℤ A where
  carrier := {a | a ∈ O ∧ σ a ∈ O}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' ha hb := ⟨O.add_mem ha.1 hb.1, by simpa using O.add_mem ha.2 hb.2⟩
  mul_mem' ha hb := ⟨O.mul_mem ha.1 hb.1, by simpa using O.mul_mem hb.2 ha.2⟩
  algebraMap_mem' n := ⟨O.algebraMap_mem n, by
    rw [Algebra.algebraMap_eq_smul_one]
    change σ.linear (n • (1 : A)) ∈ O
    rw [σ.linear.map_smul_of_tower, σ.map_one]
    exact O.smul_mem O.one_mem n⟩

@[simp] theorem mem_involutionStableCore (σ : AlgebraInvolution ℚ A)
    (O : Subalgebra ℤ A) (a : A) :
    a ∈ involutionStableCore σ O ↔ a ∈ O ∧ σ a ∈ O := Iff.rfl

theorem involutionStableCore_le (σ : AlgebraInvolution ℚ A) (O : Subalgebra ℤ A) :
    involutionStableCore σ O ≤ O := fun _ h => h.1

/-- The constructed core is preserved in both directions by the actual involution. -/
@[simp] theorem involution_mem_involutionStableCore (σ : AlgebraInvolution ℚ A)
    (O : Subalgebra ℤ A) (a : A) :
    σ a ∈ involutionStableCore σ O ↔ a ∈ involutionStableCore σ O := by
  simp only [mem_involutionStableCore, σ.apply_apply, and_comm]

theorem involutionStableCore_finite (σ : AlgebraInvolution ℚ A)
    (O : Subalgebra ℤ A) [Module.Finite ℤ O] :
    Module.Finite ℤ (involutionStableCore σ O) :=
  Module.Finite.of_injective
    (Submodule.inclusion (show (involutionStableCore σ O).toSubmodule ≤ O.toSubmodule from
      involutionStableCore_le σ O))
    (Submodule.inclusion_injective _)

/-- Simultaneous multiples of an element and its involution make the core full. -/
theorem exists_int_multiple_mem_involutionStableCore (σ : AlgebraInvolution ℚ A)
    (O : Subalgebra ℤ A)
    (hO : ∀ a : A, ∃ m : ℤ, m ≠ 0 ∧ m • a ∈ O) (a : A) :
    ∃ m : ℤ, m ≠ 0 ∧ m • a ∈ involutionStableCore σ O := by
  obtain ⟨m, hm, ha⟩ := hO a
  obtain ⟨n, hn, hσa⟩ := hO (σ a)
  refine ⟨m * n, mul_ne_zero hm hn, ?_, ?_⟩
  · rw [mul_comm, mul_smul]
    exact O.smul_mem ha n
  · rw [show σ ((m * n) • a) = (m * n) • σ a from σ.linear.map_smul_of_tower (m * n) a,
      mul_smul]
    exact O.smul_mem hσa m

variable (A) [FiniteDimensional ℚ A]

/-- An actual finite full integer lattice containing 1, obtained from a rational basis. -/
def basisLattice : Submodule ℤ A :=
  Submodule.span ℤ (insert 1 (Set.range (Module.finBasis ℚ A)))

@[simp] theorem one_mem_basisLattice : (1 : A) ∈ basisLattice A :=
  Submodule.subset_span (Set.mem_insert 1 _)

instance basisLattice_isLattice : Submodule.IsLattice ℚ (basisLattice A) where
  fg := Submodule.fg_span ((Set.finite_range (Module.finBasis ℚ A)).insert 1)
  span_eq_top := by
    apply eq_top_iff.mpr
    rw [← (Module.finBasis ℚ A).span_eq]
    apply Submodule.span_mono
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span (Set.mem_insert_of_mem 1 (Set.mem_range_self i))

/-- Construct a finite full integer order preserved by the specified involution. -/
def integralOrder (σ : AlgebraInvolution ℚ A) : Subalgebra ℤ A :=
  involutionStableCore σ (latticeStabilizer (basisLattice A))

instance integralOrder_finite (σ : AlgebraInvolution ℚ A) :
    Module.Finite ℤ (integralOrder A σ) := by
  have := latticeStabilizer_finite (basisLattice A)
    (Submodule.IsLattice.fg (A := ℚ)) (one_mem_basisLattice A)
  exact involutionStableCore_finite σ _

theorem exists_int_multiple_mem_integralOrder (σ : AlgebraInvolution ℚ A) (a : A) :
    ∃ m : ℤ, m ≠ 0 ∧ m • a ∈ integralOrder A σ :=
  exists_int_multiple_mem_involutionStableCore σ _
    (exists_int_multiple_mem_latticeStabilizer (basisLattice A)
      (Submodule.IsLattice.fg (A := ℚ)) (Submodule.IsLattice.span_eq_top (A := ℚ))) a

/-- The order has full rational span, as a theorem about the constructed subalgebra. -/
instance integralOrder_isLattice (σ : AlgebraInvolution ℚ A) :
    Submodule.IsLattice ℚ (integralOrder A σ).toSubmodule where
  fg := Module.Finite.iff_fg.mp (integralOrder_finite A σ)
  span_eq_top := span_eq_top_of_int_multiples _ (exists_int_multiple_mem_integralOrder A σ)

@[simp] theorem involution_mem_integralOrder (σ : AlgebraInvolution ℚ A) (a : A) :
    σ a ∈ integralOrder A σ ↔ a ∈ integralOrder A σ :=
  involution_mem_involutionStableCore σ _ a

/-- The rational involution restricts to an integer-linear order involution. -/
def integralOrderInvolution (σ : AlgebraInvolution ℚ A) :
    AlgebraInvolution ℤ (integralOrder A σ) where
  linear :=
    { toFun := fun a => ⟨σ a, (involution_mem_integralOrder A σ a).mpr a.prop⟩
      map_add' := fun a b => Subtype.ext (σ.apply_add a b)
      map_smul' := fun n a => Subtype.ext (σ.linear.map_smul_of_tower n (a : A)) }
  map_one := Subtype.ext σ.apply_one
  map_mul a b := Subtype.ext (σ.apply_mul a b)
  involutive a := Subtype.ext (σ.apply_apply a)

@[simp] theorem integralOrderInvolution_apply (σ : AlgebraInvolution ℚ A)
    (a : integralOrder A σ) :
    (integralOrderInvolution A σ a : A) = σ a := rfl

/-- The order acts by actual integer-linear endomorphisms of its chosen lattice. -/
def integralOrderAction (σ : AlgebraInvolution ℚ A) :
    integralOrder A σ →+* Module.End ℤ (basisLattice A) :=
  (latticeStabilizerAction (basisLattice A)).comp
    (Subalgebra.inclusion (involutionStableCore_le σ _)).toRingHom

@[simp] theorem integralOrderAction_apply (σ : AlgebraInvolution ℚ A)
    (a : integralOrder A σ) (x : basisLattice A) :
    (integralOrderAction A σ a x : A) = (a : A) * x := rfl

theorem integralOrderAction_injective (σ : AlgebraInvolution ℚ A) :
    Function.Injective (integralOrderAction A σ) := by
  intro a b h
  apply Subtype.ext
  simpa only [integralOrderAction_apply, mul_one] using
    congrArg (fun f : Module.End ℤ (basisLattice A) =>
      (f ⟨1, one_mem_basisLattice A⟩ : A)) h

/-- The order acts on the concrete lattice used in its construction. -/
theorem integralOrder_mul_mem_basisLattice (σ : AlgebraInvolution ℚ A)
    {a x : A} (ha : a ∈ integralOrder A σ) (hx : x ∈ basisLattice A) :
    a * x ∈ basisLattice A := ha.1 x hx

end Orders

end Langlands.Shimura.PEL
