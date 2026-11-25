/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.TheoremOfCube

/-!
# The theorem of the cube

For an invertible module `L` on an abelian variety `A` the seven pullbacks of `L` along the
partial sum maps `A × A × A ⟶ A` satisfy the cube relation, and as a consequence the pullback of
a symmetric invertible module along multiplication by `n` is its `n²`-th tensor power.

The partial sum maps are written using the group structure on `X ⟶ A` coming from
`CategoryTheory.GrpObj.Hom.group`: writing `p₁ = fst _ _ ≫ fst _ _`, `p₂ = fst _ _ ≫ snd _ _`
and `p₃ = snd _ _` for the three projections `(A ⊗ A) ⊗ A ⟶ A`, the partial sum `m_{i₁…i_t}` is
the product `p_{i₁} * ⋯ * p_{i_t}`. Naming the eight vertices of the cube `(ε₁, ε₂, ε₃)` with
`εᵢ ∈ {0, 1}`, the relation below is the alternating product over the vertices:

```
        (0,1,1) ───────── (1,1,1)
         ╱ │               ╱ │
   (0,1,0) ─┼───────(1,1,0)  │
      │   (0,0,1) ──────│── (1,0,1)
      │  ╱              │  ╱
   (0,0,0) ─────────(1,0,0)
```

the vertex `(ε₁, ε₂, ε₃)` contributing `m_{i : εᵢ = 1}^* L` with sign `(-1)^(ε₁ + ε₂ + ε₃)`.

## Main statements

- `AlgebraicGeometry.nonempty_iso_cube`: the theorem of the cube.
- `AlgebraicGeometry.nonempty_iso_overPullback_npow_id`: `[n]^* N ≅ N^{⊗ n²}` for symmetric `N`.

## TODO

Both statements throw the isomorphism away by asserting only `Nonempty`. The mathematical
content is the isomorphism itself, so once they can be proved they should become `def`s
returning the isomorphism, with the `Nonempty` form derived.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

open Scheme.Modules

variable {K : Type u} [Field K]

/-- Pullback along a composite, on isomorphism classes. -/
private lemma toSkeleton_overPullback_comp {B C D : Over (Spec (.of K))} (s : B ⟶ C) (g : C ⟶ D)
    (L : D.left.Modules) :
    toSkeleton (overPullback s (overPullback g L)) = toSkeleton (overPullback (s ≫ g) L) :=
  toSkeleton_eq_toSkeleton_iff.2 ⟨(pullbackComp s.left g.left).app L⟩

/-- Pullback is multiplicative on isomorphism classes. -/
private lemma toSkeleton_overPullback_tensorObj {B C : Over (Spec (.of K))} (s : B ⟶ C)
    (M N : C.left.Modules) :
    toSkeleton (overPullback s (M ⊗ N)) =
      toSkeleton (overPullback s M) * toSkeleton (overPullback s N) := by
  rw [← Skeleton.toSkeleton_tensorObj]
  exact toSkeleton_eq_toSkeleton_iff.2 (nonempty_pullback_tensorObj_iso _ _ _)

/-- The pullback of an invertible module on a group scheme along the constant map `1` is
trivial. -/
private lemma toSkeleton_overPullback_one (A : Over (Spec (.of K))) [GrpObj A]
    (L : A.left.Modules) [L.IsInvertible] (B : Over (Spec (.of K))) :
    toSkeleton (overPullback (1 : B ⟶ A) L) = 1 := by
  rw [Hom.one_def, ← toSkeleton_overPullback_comp, Skeleton.one_eq]
  obtain ⟨e⟩ := IsInvertible.nonempty_iso_unit (X := Spec (.of K))
    (IsLocalRing.closedPoint K) (overPullback η[A] L)
  exact toSkeleton_eq_toSkeleton_iff.2
    ⟨(Scheme.Modules.pullback _).mapIso e ≪≫ pullbackObjUnitIso _⟩

/-- Blueprint `theorem-theorem-cube`: The theorem of the cube.

Let `A` be an abelian variety over a field `K` and let `L` be an invertible `𝒪_A`-module. For
`1 ≤ i₁ < ⋯ < i_t ≤ 3` let `m_{i₁…i_t} : A × A × A ⟶ A` be the partial sum map
`(x₁, x₂, x₃) ↦ x_{i₁} + ⋯ + x_{i_t}`. Then
`m₁₂₃^* L ⊗ m₁^* L ⊗ m₂^* L ⊗ m₃^* L ≅ m₁₂^* L ⊗ m₁₃^* L ⊗ m₂₃^* L`.

This is also blueprint `proposition-pullback-multiplication-n--1`. The proof applies the general
theorem of the cube `AlgebraicGeometry.nonempty_iso_of_nonempty_iso_overPullback_slices` with
`X = Y = Z = A` and the unit as rational point: on each of the slices `{e} × A × A`, `A × {e} × A`
and `A × A × {e}` both sides restrict to `n₁₂^* L ⊗ n₁^* L ⊗ n₂^* L`, since `e^* L` is trivial. -/
theorem nonempty_iso_cube (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (L : A.left.Modules) [L.IsInvertible] :
    Nonempty
      (Scheme.Modules.tensorObj
          (overPullback ((fst (A ⊗ A) A ≫ fst A A) * (fst (A ⊗ A) A ≫ snd A A) *
            snd (A ⊗ A) A) L)
          (Scheme.Modules.tensorObj (overPullback (fst (A ⊗ A) A ≫ fst A A) L)
            (Scheme.Modules.tensorObj (overPullback (fst (A ⊗ A) A ≫ snd A A) L)
              (overPullback (snd (A ⊗ A) A) L))) ≅
        Scheme.Modules.tensorObj
          (overPullback ((fst (A ⊗ A) A ≫ fst A A) * (fst (A ⊗ A) A ≫ snd A A)) L)
          (Scheme.Modules.tensorObj
            (overPullback ((fst (A ⊗ A) A ≫ fst A A) * snd (A ⊗ A) A) L)
            (overPullback ((fst (A ⊗ A) A ≫ snd A A) * snd (A ⊗ A) A) L))) := by
  -- Compare isomorphism classes in the commutative monoid `Skeleton`, where pullback is
  -- multiplicative and the pullback of `L` along the constant map `1` is trivial.
  have hone (B : Over (Spec (.of K))) :
      toSkeleton (overPullback (toUnit B ≫ η[A]) L) = 1 :=
    toSkeleton_overPullback_one A L B
  have hunit_mul {B : Over (Spec (.of K))} (f : B ⟶ A) : (toUnit B ≫ η[A]) * f = f :=
    one_mul f
  have mul_hunit {B : Over (Spec (.of K))} (f : B ⟶ A) : f * (toUnit B ≫ η[A]) = f := mul_one f
  refine nonempty_iso_of_nonempty_iso_overPullback_slices A A A η[A] η[A] η[A] _ _ ?_ ?_ ?_ <;>
    refine toSkeleton_eq_toSkeleton_iff.1 ?_ <;>
    simp only [toSkeleton_overPullback_tensorObj, toSkeleton_overPullback_comp, comp_mul,
      lift_fst_assoc, lift_fst, lift_snd, Category.id_comp, hunit_mul, mul_hunit, hone]
  · rw [_root_.one_mul]; ac_rfl
  · rw [_root_.one_mul]; ac_rfl
  · rw [_root_.mul_one]

/-- The theorem of the cube pulled back along `(a, b, c) : B ⟶ A × A × A`, on isomorphism
classes: `(a + b + c)^* L ⊗ a^* L ⊗ b^* L ⊗ c^* L ≅ (a + b)^* L ⊗ (a + c)^* L ⊗ (b + c)^* L`. -/
private lemma toSkeleton_cube (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    (L : A.left.Modules) [L.IsInvertible] {B : Over (Spec (.of K))} (a b c : B ⟶ A) :
    toSkeleton (overPullback (a * b * c) L) * (toSkeleton (overPullback a L) *
        (toSkeleton (overPullback b L) * toSkeleton (overPullback c L))) =
      toSkeleton (overPullback (a * b) L) *
        (toSkeleton (overPullback (a * c) L) * toSkeleton (overPullback (b * c) L)) := by
  obtain ⟨e⟩ := nonempty_iso_cube A L
  have :=
    toSkeleton_eq_toSkeleton_iff.2 ⟨(Scheme.Modules.pullback (lift (lift a b) c).left).mapIso e⟩
  simpa only [toSkeleton_overPullback_tensorObj, toSkeleton_overPullback_comp, comp_mul,
    lift_fst_assoc, lift_fst, lift_snd] using this

/-- Blueprint `proposition-pullback-multiplication-n--2`: Pullback of symmetric modules under
multiplication by `n`.

Let `A` be an abelian variety over `K` and let `N` be an invertible `𝒪_A`-module which is
*symmetric*, that is `[-1]^* N ≅ N`. Then `[n]^* N ≅ N^{⊗ n²}` for every `n`.

This is also blueprint `proposition-pullback-multiplication-n--2`. The proof compares isomorphism
classes in the commutative monoid `Skeleton A.left.Modules`, in which the class of `N` is a unit
since `N` is invertible. Pulling back the theorem of the cube `AlgebraicGeometry.nonempty_iso_cube`
along `x ↦ (x, x, -x)` gives `[2]^* N ≅ N^{⊗ 4}`, and along `x ↦ (x, x, [n] x)` gives
`[n + 2]^* N ⊗ N^{⊗ 2} ⊗ [n]^* N ≅ [2]^* N ⊗ ([n + 1]^* N)^{⊗ 2}`, from which the claim follows
by induction on `n`. -/
theorem nonempty_iso_overPullback_npow_id (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianVariety A] (N : A.left.Modules) [N.IsInvertible]
    (hsymm : Nonempty (overPullback ι[A] N ≅ N)) (n : ℕ) :
    Nonempty (overPullback (𝟙 A ^ n) N ≅ N.tensorPow (n ^ 2)) := by
  set t : ℕ → Skeleton A.left.Modules := fun m ↦ toSkeleton (overPullback (𝟙 A ^ m) N)
    with ht
  set u := toSkeleton N with hu
  have hpow (m : ℕ) : toSkeleton (N.tensorPow m) = u ^ m := by
    induction m with
    | zero => rfl
    | succ m ih => rw [tensorPow_succ, Skeleton.toSkeleton_tensorObj, ih, pow_succ']
  have hunit : IsUnit u := by
    obtain ⟨e⟩ := nonempty_tensorObj_dual_iso_unit N
    refine isUnit_iff_exists_inv.2 ⟨toSkeleton Nᵛ, ?_⟩
    rw [hu, ← Skeleton.toSkeleton_tensorObj, Skeleton.one_eq]
    exact toSkeleton_eq_toSkeleton_iff.2 ⟨e⟩
  have h1 : t 1 = u := by
    simp only [ht, pow_one]
    exact toSkeleton_eq_toSkeleton_iff.2 ⟨(pullbackId _).app N⟩
  have h2 : t 2 = u ^ 4 := by
    have hc := toSkeleton_cube A N (𝟙 A) (𝟙 A) ι[A]
    have h1' : toSkeleton (overPullback (𝟙 A) N) = u := by simpa only [ht, pow_one] using h1
    rw [GrpObj.inv_eq_inv, mul_inv_cancel_right, mul_inv_cancel, toSkeleton_overPullback_one,
      ← GrpObj.inv_eq_inv, toSkeleton_eq_toSkeleton_iff.2 hsymm, ← pow_two, _root_.one_mul,
      _root_.mul_one] at hc
    rw [← hu, h1'] at hc
    change _ = t 2 at hc
    rw [← hc]
    simp only [pow_succ, pow_zero, _root_.one_mul, _root_.mul_assoc]
  have key (m : ℕ) : t m = u ^ (m ^ 2) ∧ t (m + 1) = u ^ ((m + 1) ^ 2) := by
    induction m with
    | zero => exact ⟨toSkeleton_overPullback_one A N A, by simpa using h1⟩
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have hc := toSkeleton_cube A N (𝟙 A) (𝟙 A) (𝟙 A ^ m)
      have h1' : toSkeleton (overPullback (𝟙 A) N) = u := by simpa only [ht, pow_one] using h1
      rw [h1', ← pow_two, ← pow_add, ← pow_succ', add_comm 2 m] at hc
      change t (m + 2) * (u * (u * t m)) = t 2 * (t (m + 1) * t (m + 1)) at hc
      rw [ih.1, ih.2, h2, ← pow_succ', ← pow_succ', ← pow_add, ← pow_add] at hc
      refine (hunit.pow (m ^ 2 + 1 + 1)).mul_right_cancel ?_
      change t (m + 2) * _ = _
      rw [hc, ← pow_add]
      congr 1
      ring
  obtain ⟨e⟩ := toSkeleton_eq_toSkeleton_iff.1 ((key n).1.trans (hpow _).symm)
  exact ⟨e⟩

end AlgebraicGeometry
