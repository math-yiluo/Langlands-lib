/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Exactness on a graded piece of a symmetric algebra

Source: Stacks Project, Algebra, Lemma 00DO (blueprint: lem-weil-pbc-symmetric-degree-exact).
-/

@[expose] public section

universe u v

namespace SymmetricAlgebra

open scoped TensorProduct

set_option linter.unusedVariables false in
/-- Source: Stacks Project, Algebra, Lemma 00DO
(blueprint: lem-weil-pbc-symmetric-degree-exact).
The induced map on the degree-`n` submodules exists; this auxiliary statement
supplies the codomain restriction used in the exactness statement. -/
theorem degree_map_exists (R : Type u) (M₁ M : Type v) [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M] [Module R M]
    (p : M₁ →ₗ[R] M) (n : ℕ) :
    ∃ h : ∀ x : ((TensorAlgebra.ι R : M₁ →ₗ[R] TensorAlgebra R M₁).range ^ n).map
          (algHom R M₁).toLinearMap,
      (lift ((ι R M).comp p)).toLinearMap x ∈
        ((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ n).map
          (algHom R M).toLinearMap, True := by
  let f := lift ((ι R M).comp p)
  have hdegree (N : Type v) [AddCommGroup N] [Module R N] (k : ℕ) :
      ((TensorAlgebra.ι R : N →ₗ[R] TensorAlgebra R N).range ^ k).map
        (algHom R N).toLinearMap = (ι R N).range ^ k := by
    rw [Submodule.map_pow, ← LinearMap.range_comp]
    rfl
  have hmap : ((ι R M₁).range).map f.toLinearMap ≤ (ι R M).range := by
    rintro z ⟨x, ⟨y, rfl⟩, rfl⟩
    exact ⟨p y, (lift_ι_apply ((ι R M).comp p) y).symm⟩
  refine ⟨?_, trivial⟩
  intro x
  have hx : (x : SymmetricAlgebra R M₁) ∈ (ι R M₁).range ^ n := by
    simpa only [hdegree] using x.property
  rw [hdegree]
  have hm : ((ι R M₁).range ^ n).map f.toLinearMap ≤ (ι R M).range ^ n := by
    rw [Submodule.map_pow]
    exact pow_le_pow_left' hmap n
  exact hm ⟨x, hx, rfl⟩

/-- Source: Stacks Project, Algebra, Lemma 00DO
(blueprint: lem-weil-pbc-symmetric-degree-exact).
Restriction of the symmetric-algebra map induced by `p` to degree `n`. -/
noncomputable def degreeMap (R : Type u) (M₁ M : Type v) [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M] [Module R M]
    (p : M₁ →ₗ[R] M) (n : ℕ) :
    (((TensorAlgebra.ι R : M₁ →ₗ[R] TensorAlgebra R M₁).range ^ n).map
        (algHom R M₁).toLinearMap) →ₗ[R]
      (((TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M).range ^ n).map
        (algHom R M).toLinearMap) :=
  (lift ((ι R M).comp p)).toLinearMap.domRestrict _ |>.codRestrict _
    (Classical.choose (degree_map_exists R M₁ M p n))

private theorem degree_eq_range_pow (R : Type u) (N : Type v) [CommRing R]
    [AddCommGroup N] [Module R N] (k : ℕ) :
    ((TensorAlgebra.ι R : N →ₗ[R] TensorAlgebra R N).range ^ k).map
      (algHom R N).toLinearMap = (ι R N).range ^ k := by
  rw [Submodule.map_pow, ← LinearMap.range_comp]
  rfl

private theorem degree_surjective (R : Type u) (M₁ M : Type v) [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M] [Module R M]
    (p : M₁ →ₗ[R] M) (hp : Function.Surjective p) (n : ℕ) :
    Function.Surjective (degreeMap R M₁ M p n) := by
  let f := lift ((ι R M).comp p)
  have hmap : ((ι R M₁).range).map f.toLinearMap = (ι R M).range := by
    rw [← LinearMap.range_comp]
    have hcomp : f.toLinearMap.comp (ι R M₁) = (ι R M).comp p := by
      ext x
      exact lift_ι_apply ((ι R M).comp p) x
    rw [hcomp, LinearMap.range_comp, LinearMap.range_eq_top.mpr hp, Submodule.map_top]
  intro z
  have hz : (z : SymmetricAlgebra R M) ∈
      ((ι R M₁).range ^ n).map f.toLinearMap := by
    rw [Submodule.map_pow, hmap]
    simpa only [degree_eq_range_pow] using z.property
  obtain ⟨x, hx, hfx⟩ := hz
  refine ⟨⟨x, ?_⟩, ?_⟩
  · rw [degree_eq_range_pow]
    exact hx
  · exact Subtype.ext hfx

private theorem lift_kernel (R : Type u) (M₂ M₁ M : Type v) [CommRing R]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M] [Module R M]
    (a : M₂ →ₗ[R] M₁) (p : M₁ →ₗ[R] M) (hp : Function.Surjective p)
    (hker : LinearMap.range a = LinearMap.ker p) :
    RingHom.ker (lift ((ι R M).comp p)).toRingHom =
      Ideal.span (Set.range (fun y ↦ ι R M₁ (a y))) := by
  let I := Ideal.span (Set.range (fun y ↦ ι R M₁ (a y)))
  let q := Ideal.Quotient.mkₐ R I
  have hq : LinearMap.ker p ≤ LinearMap.ker (q.toLinearMap.comp (ι R M₁)) := by
    intro x hx
    rw [← hker] at hx
    obtain ⟨y, rfl⟩ := hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨y, rfl⟩)
  let g : M →ₗ[R] SymmetricAlgebra R M₁ ⧸ I :=
    ((LinearMap.ker p).liftQ (q.toLinearMap.comp (ι R M₁)) hq).comp
      (p.quotKerEquivOfSurjective hp).symm.toLinearMap
  have hg (x : M₁) : g (p x) = q (ι R M₁ x) := by
    simp [g, LinearMap.quotKerEquivOfSurjective_symm_apply]
  have heq : (lift g).comp (lift ((ι R M).comp p)) = q := by
    apply algHom_ext
    ext x
    change lift g (lift ((ι R M).comp p) (ι R M₁ x)) = q (ι R M₁ x)
    rw [lift_ι_apply]
    change lift g (ι R M (p x)) = q (ι R M₁ x)
    rw [lift_ι_apply]
    exact hg x
  apply le_antisymm
  · intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hx' : lift ((ι R M).comp p) x = 0 := hx
    change q x = 0
    rw [← heq, AlgHom.comp_apply, hx', map_zero]
  · apply Ideal.span_le.mpr
    rintro _ ⟨y, rfl⟩
    change lift ((ι R M).comp p) (ι R M₁ (a y)) = 0
    rw [lift_ι_apply]
    have hay : p (a y) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [← hker]
      exact ⟨y, rfl⟩
    simp [hay]

/-- Source: Stacks Project, Algebra, Lemma 00DO (blueprint: lem-weil-pbc-symmetric-degree-exact).
For an exact sequence `M₂ → M₁ → M → 0`, the sequence on every positive
symmetric degree is exact. The first map sends `y ⊗ s` to
`ι (a y) * s`, and the second is the restriction of `Sym(p)`.
Proof steps: construct the induced algebra and tensor maps from the universal
properties; prove degreewise surjectivity using lifts along `p`; identify the
kernel of the algebra map with the ideal generated by `ι (a y)` using the
universal property; identify its degree-`n` part using the grading; conclude
kernel-image exactness. -/
theorem symmetric_degree_exact (R : Type u) (M₂ M₁ M : Type v) [CommRing R]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M] [Module R M]
    (a : M₂ →ₗ[R] M₁) (p : M₁ →ₗ[R] M)
    (hp : Function.Surjective p)
    (hker : LinearMap.range a = LinearMap.ker p) (n : ℕ) (hn : 1 ≤ n) :
    ∃ φ : M₂ ⊗[R]
        (((TensorAlgebra.ι R : M₁ →ₗ[R] TensorAlgebra R M₁).range ^ (n - 1)).map
          (algHom R M₁).toLinearMap) →ₗ[R]
        (((TensorAlgebra.ι R : M₁ →ₗ[R] TensorAlgebra R M₁).range ^ n).map
          (algHom R M₁).toLinearMap),
      (∀ y s, (φ (y ⊗ₜ[R] s) : SymmetricAlgebra R M₁) =
        (ι R M₁ (a y)) * (s : SymmetricAlgebra R M₁)) ∧
      (∀ (ψ : (M₂ ⊗[R]
        (((TensorAlgebra.ι R : M₁ →ₗ[R] TensorAlgebra R M₁).range ^ (n - 1)).map
          (algHom R M₁).toLinearMap)) →ₗ[R]
        (((TensorAlgebra.ι R : M₁ →ₗ[R] TensorAlgebra R M₁).range ^ n).map
          (algHom R M₁).toLinearMap)),
        (∀ (y : M₂) (s :
          (((TensorAlgebra.ι R : M₁ →ₗ[R] TensorAlgebra R M₁).range ^ (n - 1)).map
            (algHom R M₁).toLinearMap)),
          (ψ (y ⊗ₜ[R] s) : SymmetricAlgebra R M₁) =
        (ι R M₁ (a y)) * (s : SymmetricAlgebra R M₁)) → ψ = φ) ∧
      Function.Surjective (degreeMap R M₁ M p n) ∧
      LinearMap.range φ = LinearMap.ker (degreeMap R M₁ M p n) := by
  let D : ℕ → Submodule R (SymmetricAlgebra R M₁) := fun k ↦
    ((TensorAlgebra.ι R : M₁ →ₗ[R] TensorAlgebra R M₁).range ^ k).map
      (algHom R M₁).toLinearMap
  have hmul (y : M₂) (s : D (n - 1)) : ι R M₁ (a y) * s ∈ D n := by
    simp only [D, degree_eq_range_pow]
    have hy : ι R M₁ (a y) ∈ (ι R M₁).range := ⟨a y, rfl⟩
    have hs : (s : SymmetricAlgebra R M₁) ∈ (ι R M₁).range ^ (n - 1) := by
      simpa only [D, degree_eq_range_pow] using s.property
    have h := Submodule.mul_mem_mul hy hs
    simpa only [← pow_succ', Nat.sub_add_cancel hn] using h
  let β : M₂ →ₗ[R] D (n - 1) →ₗ[R] D n :=
    LinearMap.mk₂ R (fun y s ↦ ⟨ι R M₁ (a y) * s, hmul y s⟩)
      (by intros; apply Subtype.ext; simp [add_mul])
      (by intros; apply Subtype.ext; simp)
      (by intros; apply Subtype.ext; simp [mul_add])
      (by intros; apply Subtype.ext; simp)
  let φ := TensorProduct.lift β
  have hφ (y : M₂) (s : D (n - 1)) :
      (φ (y ⊗ₜ[R] s) : SymmetricAlgebra R M₁) = ι R M₁ (a y) * s := rfl
  refine ⟨φ, hφ, ?_, degree_surjective R M₁ M p hp n, ?_⟩
  · intro ψ hψ
    apply TensorProduct.ext'
    intro y s
    apply Subtype.ext
    exact (hψ y s).trans (hφ y s).symm
  · apply le_antisymm
    · rintro z ⟨t, rfl⟩
      change degreeMap R M₁ M p n (φ t) = 0
      apply Subtype.ext
      change lift ((ι R M).comp p) (φ t : SymmetricAlgebra R M₁) = 0
      induction t using TensorProduct.inductionOn with
      | tmul y s =>
        rw [hφ, map_mul, lift_ι_apply]
        have hay : p (a y) = 0 := by
          apply LinearMap.mem_ker.mp
          rw [← hker]
          exact ⟨y, rfl⟩
        simp [hay]
      | add t t' ht ht' => simp [ht, ht']
    · intro z hz
      have hz' : lift ((ι R M).comp p) (z : SymmetricAlgebra R M₁) = 0 :=
        congrArg Subtype.val (LinearMap.mem_ker.mp hz)
      have hI : (z : SymmetricAlgebra R M₁) ∈
          Ideal.span (Set.range (fun y ↦ ι R M₁ (a y))) := by
        rw [← lift_kernel R M₂ M₁ M a p hp hker]
        exact hz'
      obtain ⟨_, _, _, _, hD, hDmul⟩ := graded_by_tensor_images R M₁
      change DirectSum.IsInternal D at hD
      change ∀ k l, D k * D l ≤ D (k + l) at hDmul
      let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap D) hD
      let π : SymmetricAlgebra R M₁ →ₗ[R] SymmetricAlgebra R M₁ :=
        (D n).subtype.comp ((DirectSum.component R ℕ (fun k ↦ D k) n).comp
          e.symm.toLinearMap)
      have hπself (x : SymmetricAlgebra R M₁) (hx : x ∈ D n) : π x = x := by
        exact congrArg Subtype.val (hD.ofBijective_coeLinearMap_of_mem hx)
      have hπother (k : ℕ) (hk : k ≠ n) (x : SymmetricAlgebra R M₁)
          (hx : x ∈ D k) : π x = 0 := by
        exact congrArg Subtype.val (hD.ofBijective_coeLinearMap_of_mem_ne hk hx)
      let K := (LinearMap.range φ).map (D n).subtype
      have hgen (y : M₂) (r : SymmetricAlgebra R M₁) :
          π (r * ι R M₁ (a y)) ∈ K := by
        obtain ⟨t, rfl⟩ := hD.surjective r
        refine DirectSum.induction_on t ?_ ?_ ?_
        · simp only [map_zero, zero_mul]
          exact K.zero_mem
        · intro k s
          change π ((DirectSum.coeLinearMap D)
            (DirectSum.of (fun k ↦ D k) k s) * ι R M₁ (a y)) ∈ K
          rw [DirectSum.coeLinearMap_of]
          have hy : ι R M₁ (a y) ∈ D 1 := by
            simp only [D, degree_eq_range_pow, pow_one]
            exact ⟨a y, rfl⟩
          have hm : (s : SymmetricAlgebra R M₁) * ι R M₁ (a y) ∈ D (k + 1) :=
            hDmul k 1 (Submodule.mul_mem_mul s.property hy)
          by_cases hk : k + 1 = n
          · have hkn : k = n - 1 := by omega
            subst k
            rw [hk] at hm
            rw [hπself _ hm]
            refine ⟨φ (y ⊗ₜ[R] s), ⟨y ⊗ₜ[R] s, rfl⟩, ?_⟩
            exact (hφ y s).trans (mul_comm _ _)
          · rw [hπother (k + 1) hk _ hm]
            exact K.zero_mem
        · intro t t' ht ht'
          simp only [map_add, add_mul]
          exact K.add_mem ht ht'
      have hproj (x : SymmetricAlgebra R M₁)
          (hx : x ∈ Ideal.span (Set.range (fun y ↦ ι R M₁ (a y)))) :
          ∀ r : SymmetricAlgebra R M₁, π (r * x) ∈ K := by
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨y, rfl⟩ := hx
          exact fun r ↦ hgen y r
        | zero =>
          intro r
          simp only [mul_zero, map_zero]
          exact K.zero_mem
        | add x x' hx hx' ih ih' =>
          intro r
          rw [mul_add, map_add]
          exact K.add_mem (ih r) (ih' r)
        | smul c x hx ih =>
          intro r
          simpa only [smul_eq_mul, ← mul_assoc] using ih (r * c)
      have hzK : (z : SymmetricAlgebra R M₁) ∈ K := by
        have h := hproj z hI 1
        rwa [one_mul, hπself z z.property] at h
      obtain ⟨w, hw, hwz⟩ := hzK
      have hwz' : w = z := Subtype.ext hwz
      exact hwz' ▸ hw

end SymmetricAlgebra
