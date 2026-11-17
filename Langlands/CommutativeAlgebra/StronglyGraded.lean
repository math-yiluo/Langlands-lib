import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Strong group gradings and their degree-zero ring -/

noncomputable section

universe u v

open scoped DirectSum TensorProduct

namespace Langlands.CommutativeAlgebra.StronglyGraded

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M]

/-- The coefficient identities of a group grading, expressed by its coaction. -/
structure IsGrading (c : A →+* AddMonoidAlgebra A M) : Prop where
  sum_coeff : ∀ a, (c a).coeff.sum (fun _ a => a) = a
  homogeneous_coeff : ∀ a m, c ((c a).coeff m) =
    AddMonoidAlgebra.single m ((c a).coeff m)

variable {c : A →+* AddMonoidAlgebra A M} (hc : IsGrading c)

/-- The ring of homogeneous elements of degree zero. -/
def degreeZero : Subring A where
  carrier := {a | c a = AddMonoidAlgebra.single 0 a}
  zero_mem' := by simp
  one_mem' := by change c 1 = _; rw [map_one]; rfl
  add_mem' := by
    intro a b ha hb
    dsimp at ha hb ⊢
    rw [map_add, ha, hb, AddMonoidAlgebra.single_add]
  neg_mem' := by
    intro a ha
    dsimp at ha ⊢
    rw [map_neg, ha, AddMonoidAlgebra.single_neg]
  mul_mem' := by
    intro a b ha hb
    dsimp at ha hb ⊢
    rw [map_mul, ha, hb, AddMonoidAlgebra.single_mul_single, zero_add]

/-- The degree-zero inclusion makes the graded ring an algebra. -/
instance : Algebra (degreeZero (c := c)) A := (degreeZero (c := c)).subtype.toAlgebra

@[simp] theorem algebraMap_degreeZero (r : degreeZero (c := c)) :
    algebraMap (degreeZero (c := c)) A r = r := rfl

/-- Each homogeneous piece is a module over the degree-zero ring. -/
def component (m : M) : Submodule (degreeZero (c := c)) A where
  carrier := {a | c a = AddMonoidAlgebra.single m a}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    dsimp at ha hb ⊢
    rw [map_add, ha, hb, AddMonoidAlgebra.single_add]
  smul_mem' := by
    intro r a ha
    change c ((r : A) * a) = AddMonoidAlgebra.single m ((r : A) * a)
    rw [map_mul, r.property, ha, AddMonoidAlgebra.single_mul_single, zero_add]

@[simp] theorem mem_component {m : M} {a : A} :
    a ∈ component (c := c) m ↔ c a = AddMonoidAlgebra.single m a := Iff.rfl

/-- Homogeneous degrees add under multiplication. -/
theorem mul_mem_component {m n : M} {a b : A}
    (ha : a ∈ component (c := c) m) (hb : b ∈ component (c := c) n) :
    a * b ∈ component (c := c) (m + n) := by
  change c (a * b) = _
  rw [map_mul, ha, hb, AddMonoidAlgebra.single_mul_single]

/-- A homogeneous coefficient is the indicated projection onto a homogeneous piece. -/
def projection (m : M) : A →ₗ[degreeZero (c := c)] A where
  toFun a := (c a).coeff m
  map_add' a b := by rw [map_add]; rfl
  map_smul' r a := by
    change (c ((r : A) * a)).coeff m = (r : A) * (c a).coeff m
    rw [map_mul, r.property, AddMonoidAlgebra.coeff_single_mul_apply]
    simp

@[simp] theorem projection_apply (m : M) (a : A) :
    projection (c := c) m a = (c a).coeff m := rfl

include hc in
/-- A projection lands in its homogeneous piece. -/
theorem projection_mem (m : M) (a : A) :
    projection (c := c) m a ∈ component (c := c) m := hc.homogeneous_coeff a m

/-- Projections on a homogeneous element have the expected Kronecker values. -/
theorem projection_of_mem [DecidableEq M] {m : M} {a : A}
    (ha : a ∈ component (c := c) m) (n : M) :
    projection (c := c) n a = if n = m then a else 0 := by
  classical
  rw [projection_apply, ha, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases h : n = m
  · subst n
    rw [if_pos rfl]
  · simp only [h, Ne.symm h, if_false]

include hc in
/-- Every element is the finite sum of its homogeneous projections. -/
theorem sum_projection (a : A) :
    ∑ m ∈ (c a).coeff.support, projection (c := c) m a = a := hc.sum_coeff a

/-- Recomposition from the direct sum of the homogeneous components. -/
def recompose : (⨁ m, component (c := c) m) →ₗ[degreeZero (c := c)] A := by
  classical
  exact DirectSum.coeLinearMap (component (c := c))

/-- A coefficient of a recomposed element recovers its direct-sum coordinate. -/
theorem projection_recompose (m : M) (x : ⨁ m, component (c := c) m) :
    projection (c := c) m (recompose (c := c) x) = (x m : A) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n a =>
    simp only [recompose, DirectSum.coeLinearMap_of]
    rw [projection_of_mem a.property]
    by_cases hmn : m = n
    · subst n
      simp [DirectSum.of_eq_same]
    · simp [hmn, DirectSum.of_eq_of_ne]
  | add x y hx hy =>
    simpa only [map_add, DirectSum.add_apply, Submodule.coe_add]
      using congrArg₂ (· + ·) hx hy

include hc in
/-- Homogeneous components form an internal direct sum. -/
theorem recompose_bijective : Function.Bijective (recompose (c := c)) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply DFinsupp.ext
    intro m
    apply Subtype.ext
    have h := projection_recompose (c := c) m x
    rw [hx, map_zero] at h
    exact h.symm
  · intro a
    refine ⟨∑ m ∈ (c a).coeff.support,
      DirectSum.of (fun m => component (c := c) m) m
        ⟨projection (c := c) m a, projection_mem hc m a⟩, ?_⟩
    simpa [recompose] using sum_projection hc a

/-- The graded ring is linearly equivalent to the direct sum of its components. -/
def decomposition : A ≃ₗ[degreeZero (c := c)] ⨁ m, component (c := c) m :=
  (LinearEquiv.ofBijective (recompose (c := c)) (recompose_bijective hc)).symm

/-- The finite partition of unity supplied by a strong grading in one degree. -/
def HasDualFamily (m : M) : Prop :=
  ∃ (n : ℕ) (x y : Fin n → A),
    (∀ i, x i ∈ component (c := c) m) ∧
    (∀ i, y i ∈ component (c := c) (-m)) ∧ ∑ i, x i * y i = 1

/-- Strong grading, in the finite dual-family form used for the quotient construction. -/
def IsStrong : Prop := ∀ m : M, HasDualFamily (c := c) m

/-- Each component of a strongly graded commutative ring is projective over
its degree-zero ring. -/
theorem projective_component {m : M} (hs : HasDualFamily (c := c) m) :
    Module.Projective (degreeZero (c := c)) (component (c := c) m) := by
  classical
  obtain ⟨n, x, y, hx, hy, hsum⟩ := hs
  let toFree : component (c := c) m →ₗ[degreeZero (c := c)] (Fin n → degreeZero (c := c)) :=
    { toFun := fun a i => ⟨y i * a, by
        change c (y i * (a : A)) = AddMonoidAlgebra.single 0 (y i * (a : A))
        simpa only [neg_add_cancel, mem_component] using
          mul_mem_component (hy i) a.property⟩
      map_add' := by intros; ext i; simp [mul_add]
      map_smul' := by intros; ext i; simp [Algebra.smul_def, mul_left_comm] }
  let fromFree : (Fin n → degreeZero (c := c)) →ₗ[degreeZero (c := c)]
      component (c := c) m :=
    { toFun := fun r => ∑ i, r i • (⟨x i, hx i⟩ : component (c := c) m)
      map_add' := by
        intro r s
        change (∑ i, (r i + s i) • (⟨x i, hx i⟩ : component (c := c) m)) = _
        simp only [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.smul_sum, mul_smul] }
  apply Module.Projective.of_split toFree fromFree
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  simp only [fromFree, toFree, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum,
    Submodule.coe_smul, Algebra.smul_def, algebraMap_degreeZero]
  change (∑ i, (y i * (a : A)) * x i) = a
  calc
    (∑ i, (y i * (a : A)) * x i) = (∑ i, x i * y i) * a := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = a := by rw [hsum, one_mul]

include hc in
/-- A strongly graded commutative ring is projective over its degree-zero ring. -/
theorem projective (hs : IsStrong (c := c)) : Module.Projective (degreeZero (c := c)) A := by
  let (m : M) := projective_component (hs m)
  exact Module.Projective.of_equiv (decomposition hc).symm

end Langlands.CommutativeAlgebra.StronglyGraded
