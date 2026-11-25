/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import WeilConjectures.Algebra.Homology.ExactCouple.Reindex

/-!
# The exact couple of a tower of distinguished triangles

Let `T` be a pretriangulated category and `H : T ⥤ C` a homological functor to an abelian
category, together with a shift sequence `H.shift n` (for instance the homology functors on a
derived category). A *tower of distinguished triangles* in `T` is an increasing family of
objects `X q` (`q ∈ ℤ`) with distinguished triangles

`X (q - 1) ⟶ X q ⟶ Y q ⟶ X (q - 1)⟦1⟧`.

Applying `H` gives long exact sequences which assemble into an exact couple indexed by
`(q, n) ∈ ℤ × ℤ`, with `D (q, n) = Hⁿ(X q)` and `E (q, n) = Hⁿ(Y q)`, the map
`α : Hⁿ(X (q - 1)) ⟶ Hⁿ(X q)` (of degree `(1, 0)`), the map `g : Hⁿ(X q) ⟶ Hⁿ(Y q)` (of degree
`0`) and the connecting map `f : Hⁿ(Y q) ⟶ Hⁿ⁺¹(X (q - 1))` (of degree `(-1, 1)`).

Reindexing along `(q, n) ↦ (n - q, n)` gives a couple indexed by filtration degree `p = n - q`
and total degree `n` whose maps have degrees `(-1, 0)`, `(2, 1)` and `0`
(`CategoryTheory.TriangleTower.exactCoupleTotal`), the convention of
`WeilConjectures/Algebra/Homology/ExactCouple/Convergence.lean`; reindexing along
`(q, n) ↦ (-q, n)` gives a couple of the type of the couple of a filtered complex, with degrees
`(-1, 0)`, `(1, 1)` and `0` (`CategoryTheory.TriangleTower.exactCoupleNeg`).

## Main definitions

- `CategoryTheory.TriangleTower`: towers of distinguished triangles.
- `CategoryTheory.TriangleTower.exactCouple`: the exact couple of a tower of distinguished
  triangles under a homological functor.
- `CategoryTheory.TriangleTower.exactCoupleTotal`, `CategoryTheory.TriangleTower.exactCoupleNeg`:
  its reindexings.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory

variable (T : Type*) [Category* T] [HasZeroObject T] [HasShift T ℤ] [Preadditive T]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

/-- A *tower of distinguished triangles* in a pretriangulated category: objects `X q` and `Y q`
for `q ∈ ℤ` together with distinguished triangles `X (q - 1) ⟶ X q ⟶ Y q ⟶ X (q - 1)⟦1⟧`. -/
structure TriangleTower where
  /-- The objects `X q` of the tower. -/
  X : ℤ → T
  /-- The cones `Y q` of the maps `X (q - 1) ⟶ X q`. -/
  Y : ℤ → T
  /-- The maps `X (q - 1) ⟶ X q` of the tower. -/
  mor₁ (q : ℤ) : X (q - 1) ⟶ X q
  /-- The maps `X q ⟶ Y q`. -/
  mor₂ (q : ℤ) : X q ⟶ Y q
  /-- The connecting maps `Y q ⟶ X (q - 1)⟦1⟧`. -/
  mor₃ (q : ℤ) : Y q ⟶ (X (q - 1))⟦(1 : ℤ)⟧
  distinguished (q : ℤ) : Triangle.mk (mor₁ q) (mor₂ q) (mor₃ q) ∈ distTriang T

namespace TriangleTower

variable {T} (P : TriangleTower T)

/-- The distinguished triangle `X (q - 1) ⟶ X q ⟶ Y q ⟶ X (q - 1)⟦1⟧` of a tower. -/
abbrev triangle (q : ℤ) : Triangle T := Triangle.mk (P.mor₁ q) (P.mor₂ q) (P.mor₃ q)

section Map

variable {T' : Type*} [Category* T'] [HasZeroObject T'] [HasShift T' ℤ] [Preadditive T']
  [∀ n : ℤ, (shiftFunctor T' n).Additive] [Pretriangulated T']
  (G : T ⥤ T') [G.CommShift ℤ] [G.IsTriangulated]

/-- The image of a tower of distinguished triangles under a triangulated functor. -/
@[simps]
noncomputable def map : TriangleTower T' where
  X q := G.obj (P.X q)
  Y q := G.obj (P.Y q)
  mor₁ q := G.map (P.mor₁ q)
  mor₂ q := G.map (P.mor₂ q)
  mor₃ q := G.map (P.mor₃ q) ≫ (G.commShiftIso (1 : ℤ)).hom.app (P.X (q - 1))
  distinguished q := G.map_distinguished _ (P.distinguished q)

end Map

variable {C : Type*} [Category* C] [Abelian C] (H : T ⥤ C) [H.ShiftSequence ℤ]

/-- The connecting homomorphism `Hⁿ(Y q) ⟶ Hⁿ'(X (q - 1))` of the triangle of index `q`, for
`n + 1 = n'`. -/
noncomputable def δ (q n n' : ℤ) (h : n + 1 = n') :
    (H.shift n).obj (P.Y q) ⟶ (H.shift n').obj (P.X (q - 1)) :=
  H.homologySequenceδ (P.triangle q) n n' h

/-- The maps `α : Hⁿ(X (q - 1)) ⟶ Hⁿ(X q)` of the exact couple of a tower, induced by the maps
of the tower. -/
noncomputable def coupleα (i j : ℤ × ℤ) :
    (H.shift i.2).obj (P.X i.1) ⟶ (H.shift j.2).obj (P.X j.1) :=
  if h : i.1 = j.1 - 1 ∧ i.2 = j.2 then
    eqToHom (by rw [h.1, h.2]) ≫ (H.shift j.2).map (P.mor₁ j.1)
  else 0

/-- The maps `g : Hⁿ(X q) ⟶ Hⁿ(Y q)` of the exact couple of a tower. -/
noncomputable def coupleg (i j : ℤ × ℤ) :
    (H.shift i.2).obj (P.X i.1) ⟶ (H.shift j.2).obj (P.Y j.1) :=
  if h : i = j then (H.shift i.2).map (P.mor₂ i.1) ≫ eqToHom (by rw [h]) else 0

/-- The maps `f : Hⁿ(Y q) ⟶ Hⁿ⁺¹(X (q - 1))` of the exact couple of a tower: the connecting
homomorphisms of the long exact sequences. -/
noncomputable def couplef (i j : ℤ × ℤ) :
    (H.shift i.2).obj (P.Y i.1) ⟶ (H.shift j.2).obj (P.X j.1) :=
  if h : j.1 = i.1 - 1 ∧ i.2 + 1 = j.2 then
    P.δ H i.1 i.2 j.2 h.2 ≫ eqToHom (by rw [h.1])
  else 0

/-- The map `α : Hⁿ(X (q - 1)) ⟶ Hⁿ(X q)` is induced by the map of the tower. -/
lemma coupleα_self (q n : ℤ) :
    P.coupleα H (q - 1, n) (q, n) = (H.shift n).map (P.mor₁ q) := by
  rw [coupleα, dite_eq_left ⟨rfl, rfl⟩, eqToHom_refl, Category.id_comp]

/-- The map `α : Hⁿ(X q) ⟶ Hⁿ(X q')` for `q = q' - 1`. -/
lemma coupleα_eq (q q' n : ℤ) (h : q = q' - 1) :
    P.coupleα H (q, n) (q', n) =
      (H.shift n).map (eqToHom (congrArg P.X h) ≫ P.mor₁ q') := by
  subst h
  rw [coupleα_self, eqToHom_refl, Category.id_comp]

/-- The map `g : Hⁿ(X q) ⟶ Hⁿ(Y q)` is induced by the map of the triangle. -/
lemma coupleg_self (q n : ℤ) :
    P.coupleg H (q, n) (q, n) = (H.shift n).map (P.mor₂ q) := by
  rw [coupleg, dite_eq_left rfl, eqToHom_refl, Category.comp_id]

/-- The map `f : Hⁿ(Y q) ⟶ Hⁿ⁺¹(X (q - 1))` is the connecting homomorphism. -/
lemma couplef_self (q n n' : ℤ) (h : n + 1 = n') :
    P.couplef H (q, n) (q - 1, n') = P.δ H q n n' h := by
  rw [couplef, dite_eq_left ⟨rfl, h⟩, eqToHom_refl, Category.comp_id]

/-- The maps `α` vanish off degree `(1, 0)`. -/
lemma coupleα_eq_zero (i j : ℤ × ℤ) (h : i + ((1, 0) : ℤ × ℤ) ≠ j) :
    P.coupleα H i j = 0 := by
  rw [coupleα, dite_eq_right]
  rintro ⟨h₁, h₂⟩
  exact h (Prod.ext (by simp; omega) (by simp [h₂]))

/-- The maps `f` vanish off degree `(-1, 1)`. -/
lemma couplef_eq_zero (i j : ℤ × ℤ) (h : i + ((-1, 1) : ℤ × ℤ) ≠ j) :
    P.couplef H i j = 0 := by
  rw [couplef, dite_eq_right]
  rintro ⟨h₁, h₂⟩
  exact h (Prod.ext (by simp; omega) (by simp; omega))

/-- The maps `g` vanish off degree `0`. -/
lemma coupleg_eq_zero (i j : ℤ × ℤ) (h : i + 0 ≠ j) : P.coupleg H i j = 0 := by
  rw [coupleg, dite_eq_right]
  rintro rfl
  exact h (add_zero _)

variable [H.IsHomological]

/-- The composite `g ∘ α` vanishes. -/
lemma coupleα_coupleg (i j k : ℤ × ℤ) : P.coupleα H i j ≫ P.coupleg H j k = 0 := by
  by_cases hij : i + ((1, 0) : ℤ × ℤ) = j
  · by_cases hjk : j = k
    · subst hjk
      obtain ⟨q, n⟩ := j
      obtain rfl : i = (q - 1, n) := by
        rw [Prod.ext_iff] at hij ⊢
        simp at hij
        omega
      rw [coupleα_self, coupleg_self]
      exact H.homologySequence_comp _ (P.distinguished q) n
    · rw [P.coupleg_eq_zero H j k (by simpa using hjk), comp_zero]
  · rw [P.coupleα_eq_zero H i j hij, zero_comp]

/-- The composite `f ∘ g` vanishes. -/
lemma coupleg_couplef (i j k : ℤ × ℤ) : P.coupleg H i j ≫ P.couplef H j k = 0 := by
  by_cases hij : i = j
  · subst hij
    by_cases hjk : i + ((-1, 1) : ℤ × ℤ) = k
    · obtain ⟨q, n⟩ := i
      obtain rfl : k = (q - 1, n + 1) := by
        rw [← hjk]
        ext
        · simp
          omega
        · simp
      rw [coupleg_self, couplef_self _ _ _ _ _ rfl]
      exact H.comp_homologySequenceδ _ (P.distinguished q) n (n + 1) rfl
    · rw [P.couplef_eq_zero H _ k hjk, comp_zero]
  · rw [P.coupleg_eq_zero H i j (by simpa using hij), zero_comp]

/-- The composite `α ∘ f` vanishes. -/
lemma couplef_coupleα (i j k : ℤ × ℤ) : P.couplef H i j ≫ P.coupleα H j k = 0 := by
  by_cases hij : i + ((-1, 1) : ℤ × ℤ) = j
  · by_cases hjk : j + ((1, 0) : ℤ × ℤ) = k
    · obtain ⟨q, n⟩ := i
      obtain rfl : j = (q - 1, n + 1) := by
        rw [← hij]
        ext
        · simp
          omega
        · simp
      obtain rfl : k = (q, n + 1) := by
        rw [← hjk]
        ext <;> simp
      rw [couplef_self _ _ _ _ _ rfl, coupleα_self]
      exact H.homologySequenceδ_comp _ (P.distinguished q) n (n + 1) rfl
    · rw [P.coupleα_eq_zero H j k hjk, comp_zero]
  · rw [P.couplef_eq_zero H i j hij, zero_comp]

/-- Exactness of a short complex can be checked after rewriting its maps. -/
private lemma exact_mk_of_eq {X₁ X₂ X₃ : C} {f f' : X₁ ⟶ X₂} {g g' : X₂ ⟶ X₃}
    (w : f ≫ g = 0) (w' : f' ≫ g' = 0) (hf : f = f') (hg : g = g')
    (h : (ShortComplex.mk f' g' w').Exact) : (ShortComplex.mk f g w).Exact := by
  subst hf hg
  exact h

/-- **The exact couple of a tower of distinguished triangles.** For a tower of distinguished
triangles `X (q - 1) ⟶ X q ⟶ Y q ⟶ X (q - 1)⟦1⟧` and a homological functor `H` with a shift
sequence, the long exact sequences of the triangles form an exact couple indexed by `(q, n)`
with `D (q, n) = Hⁿ(X q)`, `E (q, n) = Hⁿ(Y q)`, `α : Hⁿ(X (q - 1)) ⟶ Hⁿ(X q)` of degree
`(1, 0)`, `g : Hⁿ(X q) ⟶ Hⁿ(Y q)` of degree `0`, and the connecting maps
`f : Hⁿ(Y q) ⟶ Hⁿ⁺¹(X (q - 1))` of degree `(-1, 1)`. -/
noncomputable def exactCouple : ExactCouple C ((1, 0) : ℤ × ℤ) (-1, 1) 0 where
  D i := (H.shift i.2).obj (P.X i.1)
  E i := (H.shift i.2).obj (P.Y i.1)
  α := P.coupleα H
  f := P.couplef H
  g := P.coupleg H
  shape_α := P.coupleα_eq_zero H
  shape_f := P.couplef_eq_zero H
  shape_g := P.coupleg_eq_zero H
  α_g := P.coupleα_coupleg H
  g_f := P.coupleg_couplef H
  f_α := P.couplef_coupleα H
  exact_α_g i j k hij hjk := by
    obtain ⟨q, n⟩ := j
    obtain rfl : k = (q, n) := by simpa using hjk.symm
    obtain rfl : i = (q - 1, n) := by
      rw [Prod.ext_iff] at hij ⊢
      simp at hij
      omega
    exact exact_mk_of_eq _ _ (P.coupleα_self H q n) (P.coupleg_self H q n)
      (H.homologySequence_exact₂ _ (P.distinguished q) n)
  exact_g_f i j k hij hjk := by
    obtain rfl : j = i := by simpa using hij.symm
    obtain ⟨q, n⟩ := j
    obtain rfl : k = (q - 1, n + 1) := by
      rw [← hjk]
      ext
      · simp
        omega
      · simp
    exact exact_mk_of_eq _ _ (P.coupleg_self H q n) (P.couplef_self H q n (n + 1) rfl)
      (H.homologySequence_exact₃ _ (P.distinguished q) n (n + 1) rfl)
  exact_f_α i j k hij hjk := by
    obtain ⟨q, n⟩ := i
    obtain rfl : j = (q - 1, n + 1) := by
      rw [← hij]
      ext
      · simp
        omega
      · simp
    obtain rfl : k = (q, n + 1) := by
      rw [← hjk]
      ext <;> simp
    exact exact_mk_of_eq _ _ (P.couplef_self H q n (n + 1) rfl) (P.coupleα_self H q (n + 1))
      (H.homologySequence_exact₁ _ (P.distinguished q) n (n + 1) rfl)

/-- The `D`-objects of the couple of a tower. -/
@[simp] lemma exactCouple_D (i : ℤ × ℤ) :
    (P.exactCouple H).D i = (H.shift i.2).obj (P.X i.1) := rfl
/-- The `E`-objects of the couple of a tower. -/
@[simp] lemma exactCouple_E (i : ℤ × ℤ) :
    (P.exactCouple H).E i = (H.shift i.2).obj (P.Y i.1) := rfl
/-- The maps `α` of the couple of a tower. -/
@[simp] lemma exactCouple_α (i j : ℤ × ℤ) : (P.exactCouple H).α i j = P.coupleα H i j := rfl
/-- The maps `f` of the couple of a tower. -/
@[simp] lemma exactCouple_f (i j : ℤ × ℤ) : (P.exactCouple H).f i j = P.couplef H i j := rfl
/-- The maps `g` of the couple of a tower. -/
@[simp] lemma exactCouple_g (i j : ℤ × ℤ) : (P.exactCouple H).g i j = P.coupleg H i j := rfl

/-- The additive automorphism `(q, n) ↦ (n - q, n)` of `ℤ × ℤ`, passing from the indexing of
the couple of a tower by `(q, n)` to the indexing by filtration degree `p = n - q` and total
degree `n`. -/
def totalEquiv : ℤ × ℤ ≃+ ℤ × ℤ where
  toFun i := (i.2 - i.1, i.2)
  invFun i := (i.2 - i.1, i.2)
  left_inv i := by ext <;> simp
  right_inv i := by ext <;> simp
  map_add' i j := by
    ext
    · simp
      abel
    · simp

/-- The formula for `totalEquiv`. -/
@[simp] lemma totalEquiv_apply (i : ℤ × ℤ) : totalEquiv i = (i.2 - i.1, i.2) := rfl
/-- The formula for the inverse of `totalEquiv`. -/
@[simp] lemma totalEquiv_symm_apply (i : ℤ × ℤ) : totalEquiv.symm i = (i.2 - i.1, i.2) := rfl

/-- The additive automorphism `(q, n) ↦ (-q, n)` of `ℤ × ℤ`. -/
def negFstEquiv : ℤ × ℤ ≃+ ℤ × ℤ where
  toFun i := (-i.1, i.2)
  invFun i := (-i.1, i.2)
  left_inv i := by ext <;> simp
  right_inv i := by ext <;> simp
  map_add' i j := by
    ext
    · simp
      abel
    · simp

/-- The formula for `negFstEquiv`. -/
@[simp] lemma negFstEquiv_apply (i : ℤ × ℤ) : negFstEquiv i = (-i.1, i.2) := rfl
/-- The formula for the inverse of `negFstEquiv`. -/
@[simp] lemma negFstEquiv_symm_apply (i : ℤ × ℤ) : negFstEquiv.symm i = (-i.1, i.2) := rfl

/-- The exact couple of a tower of distinguished triangles, indexed by filtration degree
`p = n - q` and total degree `n`: `D (p, n) = Hⁿ(X (n - p))`, `E (p, n) = Hⁿ(Y (n - p))`, with
`α` of degree `(-1, 0)`, `f` of degree `(2, 1)` and `g` of degree `0`. Written in the
coordinates `(p, q) = (p, n - p)`, the maps have the bidegrees `(-1, 1)`, `(2, -1)` and `(0, 0)`
of a couple whose spectral sequence starts on page `2`. -/
noncomputable def exactCoupleTotal : ExactCouple C ((-1, 0) : ℤ × ℤ) (2, 1) 0 :=
  (P.exactCouple H).reindex totalEquiv _ _ _ (by ext <;> simp) (by ext <;> simp) (by simp)

/-- The `D`-objects of `exactCoupleTotal`: `D (p, n) = Hⁿ(X (n - p))`. -/
@[simp] lemma exactCoupleTotal_D (p n : ℤ) :
    (P.exactCoupleTotal H).D (p, n) = (H.shift n).obj (P.X (n - p)) := rfl
/-- The `E`-objects of `exactCoupleTotal`: `E (p, n) = Hⁿ(Y (n - p))`. -/
@[simp] lemma exactCoupleTotal_E (p n : ℤ) :
    (P.exactCoupleTotal H).E (p, n) = (H.shift n).obj (P.Y (n - p)) := rfl
/-- The maps `α` of `exactCoupleTotal`. -/
lemma exactCoupleTotal_α (i j : ℤ × ℤ) :
    (P.exactCoupleTotal H).α i j = P.coupleα H (totalEquiv.symm i) (totalEquiv.symm j) := rfl
/-- The maps `f` of `exactCoupleTotal`. -/
lemma exactCoupleTotal_f (i j : ℤ × ℤ) :
    (P.exactCoupleTotal H).f i j = P.couplef H (totalEquiv.symm i) (totalEquiv.symm j) := rfl
/-- The maps `g` of `exactCoupleTotal`. -/
lemma exactCoupleTotal_g (i j : ℤ × ℤ) :
    (P.exactCoupleTotal H).g i j = P.coupleg H (totalEquiv.symm i) (totalEquiv.symm j) := rfl

/-- The exact couple of a tower of distinguished triangles, indexed by `(-q, n)`: this has the
shape of the exact couple of a filtered complex, with `α` of degree `(-1, 0)`, `f` of degree
`(1, 1)` and `g` of degree `0`. -/
noncomputable def exactCoupleNeg : ExactCouple C ((-1, 0) : ℤ × ℤ) (1, 1) 0 :=
  (P.exactCouple H).reindex negFstEquiv _ _ _ (by ext <;> simp) (by ext <;> simp) (by simp)

/-- The `D`-objects of `exactCoupleNeg`: `D (p, n) = Hⁿ(X (-p))`. -/
@[simp] lemma exactCoupleNeg_D (p n : ℤ) :
    (P.exactCoupleNeg H).D (p, n) = (H.shift n).obj (P.X (-p)) := rfl
/-- The `E`-objects of `exactCoupleNeg`: `E (p, n) = Hⁿ(Y (-p))`. -/
@[simp] lemma exactCoupleNeg_E (p n : ℤ) :
    (P.exactCoupleNeg H).E (p, n) = (H.shift n).obj (P.Y (-p)) := rfl
/-- The maps `α` of `exactCoupleNeg`. -/
lemma exactCoupleNeg_α (i j : ℤ × ℤ) :
    (P.exactCoupleNeg H).α i j = P.coupleα H (negFstEquiv.symm i) (negFstEquiv.symm j) := rfl
/-- The maps `f` of `exactCoupleNeg`. -/
lemma exactCoupleNeg_f (i j : ℤ × ℤ) :
    (P.exactCoupleNeg H).f i j = P.couplef H (negFstEquiv.symm i) (negFstEquiv.symm j) := rfl
/-- The maps `g` of `exactCoupleNeg`. -/
lemma exactCoupleNeg_g (i j : ℤ × ℤ) :
    (P.exactCoupleNeg H).g i j = P.coupleg H (negFstEquiv.symm i) (negFstEquiv.symm j) := rfl

end TriangleTower

end CategoryTheory
