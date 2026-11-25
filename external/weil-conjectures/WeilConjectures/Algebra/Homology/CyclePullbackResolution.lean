/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Abelian.Basic
import WeilConjectures.Algebra.Homology.CyclePullbackCore
import WeilConjectures.Algebra.Homology.CyclePullbackLifting

/-!
# Functorial cycle-pullback constructions

Source: Stacks Project, Derived Categories, Lemma 05T7 (1), and Cohomology on Sites,
Lemma 06YS (blueprint: lem-pc-functorial-cycle-pullback-construction).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A functorial epimorphic cover by objects of `S` produces a bounded-above
cycle-pullback construction. Its augmentation has the local lifting property for a
cycle in the next degree and a compatible element of the target in the current degree.
This statement concerns the recursive construction, not its homology.

Source: Stacks Project, Derived Categories, Lemma 05T7 (1), and Cohomology on Sites,
Lemma 06YS (blueprint: lem-pc-functorial-cycle-pullback-construction).

Proof: Put zero in all degrees above `N`. Starting at `N` and descending, form
`P^i = F^i ×_{F^{i+1}} ker(d_E^{i+1})` and put `E^i = T(P^i)`.
The two projections, composed with `π`, define the augmentation and differential.
The second projection lands in the kernel, so consecutive differentials compose to zero;
the pullback equation gives the chain-map equation. Terms satisfy `S` by `hT`, or by
`hzero` above the bound. A compatible pair `(y,x)` factors uniquely through `P^i`;
pull back the epimorphism `π.app P^i` along this factorization. The pullback projection
is an epimorphism and its other projection supplies the asserted lift `z`.
For a map of bounded complexes, descending induction gives maps between the kernels
and the pullbacks, and applying `T` gives the component maps. Naturality of `π` and
the pullback equations give the chain-map and augmentation equations. Uniqueness in
the kernel and pullback universal properties, and the functor laws of `T`, prove
identity and composition laws. This defines `Q` and `ε`. -/
theorem exists_functorial_cyclePullback_construction
    {A : Type u} [Category.{v} A] [Abelian A] (S : ObjectProperty A)
    (hzero : ∀ X : A, IsZero X → S X)
    (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (hT : ∀ X : A, S (T.obj X)) (hπ : ∀ X : A, Epi (π.app X)) (N : ℤ) :
    let P : ObjectProperty (CochainComplex A ℤ) :=
      fun F ↦ ∀ i : ℤ, N < i → IsZero (F.X i)
    ∃ Q : P.FullSubcategory ⥤ CochainComplex A ℤ,
      ∃ ε : Q ⟶ P.ι, ∀ F : P.FullSubcategory,
        (∀ i : ℤ, S ((Q.obj F).X i)) ∧
        (∀ i : ℤ, N < i → IsZero ((Q.obj F).X i)) ∧
        ∀ (i : ℤ) (B : A) (x : B ⟶ (Q.obj F).X (i + 1))
          (y : B ⟶ F.obj.X i),
          x ≫ (Q.obj F).d (i + 1) (i + 1 + 1) = 0 →
          x ≫ (ε.app F).f (i + 1) = y ≫ F.obj.d i (i + 1) →
          ∃ (B' : A) (p : B' ⟶ B) (_ : Epi p) (z : B' ⟶ (Q.obj F).X i),
            z ≫ (ε.app F).f i = p ≫ y ∧
              z ≫ (Q.obj F).d i (i + 1) = p ≫ x := by
  dsimp
  obtain ⟨Q, ε, hQ⟩ := exists_functorial_cyclePullback_core S hzero T π hT N
  refine ⟨Q, ε, ?_⟩
  intro F
  obtain ⟨hS, hbound, hcompare⟩ := hQ F
  refine ⟨hS, hbound, ?_⟩
  intro i B x y hx hy
  by_cases hi : i ≤ N
  · obtain ⟨c, he₁, he₂⟩ := hcompare i hi
    let e := c.hom ≫ π.app _
    let : ∀ X : A, Epi (π.app X) := hπ
    have he₁' : e ≫ pullback.fst _ _ = (ε.app F).f i := by
      simpa only [e, Category.assoc] using he₁
    have he₂' : e ≫ pullback.snd _ _ ≫ kernel.ι _ = (Q.obj F).d i (i + 1) := by
      simpa only [e, Category.assoc] using he₂
    exact cyclePullback_lifting_pointwise (ε.app F) i e he₁' he₂' B x y hx hy
  · have hNi : N < i := lt_of_not_ge hi
    have hy0 : y = 0 := (F.property i hNi).eq_zero_of_tgt y
    have hx0 : x = 0 := (hbound (i + 1) (lt_trans hNi (Int.lt_succ i))).eq_zero_of_tgt x
    refine ⟨B, 𝟙 B, inferInstance, 0, ?_, ?_⟩ <;> simp [hy0, hx0]

end CochainComplex
