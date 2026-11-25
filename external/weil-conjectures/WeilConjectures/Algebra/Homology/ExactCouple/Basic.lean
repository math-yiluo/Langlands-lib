/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# Exact couples

An *exact couple* in an abelian category `C`, indexed by an additive group `κ` (typically
`ℤ × ℤ`), consists of two families of objects `D i`, `E i` and three families of morphisms

`α : D i ⟶ D (i + a)`, `f : E i ⟶ D (i + b)`, `g : D i ⟶ E (i + c)`

forming exact triangles `D ⟶ D ⟶ E ⟶ D ⟶ D`. As usual for homological complexes in Mathlib, the
morphisms are defined between any two indices and vanish when the indices are not related by
the corresponding degree; this avoids casts along equalities of indices. The degrees `a` of `α`
and `b` of `f` and `c` of `g` are parameters of the type `ExactCouple C a b c`, so that
morphisms of couples and of their iterated derived couples are well-typed.

The composite `d = g ∘ f : E i ⟶ E (i + b + c)` squares to zero, and the *derived couple* has
`D' = im α`, `E' = H(E, d)`, with the induced maps `α' = α|_{D'}`, `f' = f|_{ker d}` and
`g'(α y) = [g y]`, of degrees `a`, `b` and `c - a`. Iterating, the homology objects of the
successive derived couples form a spectral sequence
(`CategoryTheory.ExactCouple.spectralSequence`): the `r`-th page is the complex `(E, d)` of the
`(r - r₀)`-th derived couple, and its homology is the next page.

## Main definitions

- `CategoryTheory.ExactCouple`: exact couples.
- `CategoryTheory.ExactCouple.dComplex`: the complex `(E, d = g ∘ f)`.
- `CategoryTheory.ExactCouple.derived`: the derived couple.
- `CategoryTheory.ExactCouple.derivedIter`: the iterated derived couples.
- `CategoryTheory.ExactCouple.spectralSequence`: the spectral sequence of an exact couple.

## Main statements

- `CategoryTheory.ExactCouple.exists_epi_comp_ιIter`: the `D`-objects of the `n`-th derived
  couple are the images of the `n`-fold composites of `α`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Abelian C] {κ : Type w} [AddCommGroup κ]

/-- An *exact couple* `(D, E, α, f, g)` in an abelian category, indexed by an additive group `κ`:
families of objects `D i`, `E i` and morphisms `α : D i ⟶ D (i + a)`, `f : E i ⟶ D (i + b)`,
`g : D i ⟶ E (i + c)` such that the composite of two consecutive structure maps vanishes and

`ker (α : D j ⟶ D (j + a)) = im (f : E (j - b) ⟶ D j)`,
`ker (f : E j ⟶ D (j + b)) = im (g : D (j - c) ⟶ E j)`,
`ker (g : D j ⟶ E (j + c)) = im (α : D (j - a) ⟶ D j)`.

The morphisms are given between any two indices, and vanish when the indices are not related by
the corresponding degree.

With `κ = ℤ × ℤ`, `a = (-1, 1)`, `b = (2, -1)` and `c = (0, 0)` these are the exact couples
of blueprint `def-sp-exact-couple`; the exact couple of a filtered complex has `b = (1, 0)`
instead.

(blueprint: `def-sp-exact-couple`) -/
structure ExactCouple (a b c : κ) where
  /-- The objects `D i`. -/
  D : κ → C
  /-- The objects `E i`. -/
  E : κ → C
  /-- The morphisms `α : D i ⟶ D (i + a)`. -/
  α (i j : κ) : D i ⟶ D j
  /-- The morphisms `f : E i ⟶ D (i + b)`. -/
  f (i j : κ) : E i ⟶ D j
  /-- The morphisms `g : D i ⟶ E (i + c)`. -/
  g (i j : κ) : D i ⟶ E j
  shape_α (i j : κ) : i + a ≠ j → α i j = 0
  shape_f (i j : κ) : i + b ≠ j → f i j = 0
  shape_g (i j : κ) : i + c ≠ j → g i j = 0
  α_g (i j k : κ) : α i j ≫ g j k = 0
  g_f (i j k : κ) : g i j ≫ f j k = 0
  f_α (i j k : κ) : f i j ≫ α j k = 0
  exact_α_g (i j k : κ) (hij : i + a = j) (hjk : j + c = k) :
    (ShortComplex.mk _ _ (α_g i j k)).Exact
  exact_g_f (i j k : κ) (hij : i + c = j) (hjk : j + b = k) :
    (ShortComplex.mk _ _ (g_f i j k)).Exact
  exact_f_α (i j k : κ) (hij : i + b = j) (hjk : j + a = k) :
    (ShortComplex.mk _ _ (f_α i j k)).Exact

namespace ExactCouple

variable {C} {a b c : κ} (X : ExactCouple C a b c)

attribute [reassoc (attr := simp)] α_g g_f f_α

/-- The differential `d = g ∘ f : E i ⟶ E (i + b + c)`. -/
noncomputable def d (i j : κ) : X.E i ⟶ X.E j :=
  X.f i (i + b) ≫ X.g (i + b) j

lemma d_eq (i k j : κ) (h : i + b = k) : X.d i j = X.f i k ≫ X.g k j := by
  subst h
  rfl

lemma shape_d (i j : κ) (h : i + (b + c) ≠ j) : X.d i j = 0 := by
  rw [d, X.shape_g, comp_zero]
  rwa [← add_assoc] at h

@[reassoc (attr := simp)]
lemma d_d (i j k : κ) : X.d i j ≫ X.d j k = 0 := by
  simp [d]

/-- The complex `(E, d)` of an exact couple, of shape `ComplexShape.up' (b + c)`. -/
noncomputable def dComplex : HomologicalComplex C (ComplexShape.up' (b + c)) where
  X := X.E
  d := X.d
  shape i j h := X.shape_d i j h
  d_comp_d' i j k _ _ := X.d_d i j k

@[simp]
lemma dComplex_X (i : κ) : X.dComplex.X i = X.E i := rfl

@[simp]
lemma dComplex_d (i j : κ) : X.dComplex.d i j = X.d i j := rfl

lemma dComplex_next (i : κ) :
    (ComplexShape.up' (b + c)).next i = i + (b + c) :=
  (ComplexShape.up' _).next_eq' rfl

lemma dComplex_prev (i : κ) :
    (ComplexShape.up' (b + c)).prev i = i - (b + c) :=
  (ComplexShape.up' _).prev_eq' (sub_add_cancel _ _)

/-! ### The derived couple -/

/-- The objects `D' i = im (α : D (i - a) ⟶ D i)` of the derived couple. -/
noncomputable def D' (i : κ) : C := image (X.α (i - a) i)

/-- The inclusion `D' i ⟶ D i`. -/
noncomputable def ιD (i : κ) : X.D' i ⟶ X.D i := image.ι _

/-- The projection `D (i - a) ⟶ D' i`. -/
noncomputable def πD (i : κ) : X.D (i - a) ⟶ X.D' i := factorThruImage _

instance (i : κ) : Mono (X.ιD i) := by dsimp [ιD]; infer_instance

instance (i : κ) : Epi (X.πD i) := by dsimp [πD]; infer_instance

@[reassoc (attr := simp)]
lemma πD_ιD (i : κ) : X.πD i ≫ X.ιD i = X.α (i - a) i :=
  image.fac _

/-- `α` lands in `D'`. -/
@[reassoc (attr := simp)]
lemma α_cokernelπ (k i : κ) : X.α k i ≫ cokernel.π (X.ιD i) = 0 := by
  by_cases h : k + a = i
  · obtain rfl : k = i - a := eq_sub_of_add_eq h
    rw [← X.πD_ιD, Category.assoc, cokernel.condition, comp_zero]
  · rw [X.shape_α _ _ h, zero_comp]

/-- A morphism to `D i` which is killed by `g` lands in `D' i`. -/
lemma comp_cokernelπ_eq_zero {A : C} {i l : κ} (x : A ⟶ X.D i) (hl : i + c = l)
    (hx : x ≫ X.g i l = 0) : x ≫ cokernel.π (X.ιD i) = 0 := by
  obtain ⟨A', π, _, y, hy⟩ := (X.exact_α_g (i - a) i l (sub_add_cancel _ _)
    hl).exact_up_to_refinements x hx
  rw [← cancel_epi π, ← Category.assoc, hy]
  simp

@[reassoc (attr := simp)]
lemma ιD_g (i l : κ) : X.ιD i ≫ X.g i l = 0 := by
  rw [← cancel_epi (X.πD i), X.πD_ιD_assoc, X.α_g, comp_zero]

@[reassoc (attr := simp)]
lemma f_πD (k i : κ) : X.f k (i - a) ≫ X.πD i = 0 := by
  rw [← cancel_mono (X.ιD i), Category.assoc, X.πD_ιD, X.f_α, zero_comp]

/-- The morphisms `α' : D' i ⟶ D' j` of the derived couple, restrictions of `α`. -/
noncomputable def α' (i j : κ) : X.D' i ⟶ X.D' j :=
  Abelian.monoLift (X.ιD j) (X.ιD i ≫ X.α i j) (by simp)

@[reassoc (attr := simp)]
lemma α'_ιD (i j : κ) : X.α' i j ≫ X.ιD j = X.ιD i ≫ X.α i j :=
  Abelian.monoLift_comp _ _ _

lemma shape_α' (i j : κ) (h : i + a ≠ j) : X.α' i j = 0 := by
  rw [← cancel_mono (X.ιD j), X.α'_ιD, X.shape_α _ _ h, comp_zero, zero_comp]

/-- `πD` intertwines `α` and `α'`. -/
@[reassoc]
lemma πD_α' (j : κ) :
    X.πD (j - a) ≫ X.α' (j - a) j = X.α (j - a - a) (j - a) ≫ X.πD j := by
  rw [← cancel_mono (X.ιD j)]
  simp

/-- The cycles of `(E, d)`. -/
noncomputable abbrev cycles (i : κ) : C := X.dComplex.cycles i

/-- The homology `E' i = H(E, d)` of `(E, d)`: the objects `E'` of the derived couple. -/
noncomputable abbrev E' (i : κ) : C := X.dComplex.homology i

/-- `f` restricted to the cycles, landing in `D'`. -/
noncomputable def fCycles (i j : κ) : X.cycles i ⟶ X.D' j :=
  Abelian.monoLift (X.ιD j) (X.dComplex.iCycles i ≫ X.f i j) (by
    by_cases h : i + b = j
    · refine X.comp_cokernelπ_eq_zero _ (l := j + c) rfl ?_
      rw [Category.assoc, ← X.d_eq i j _ h]
      exact X.dComplex.iCycles_d i _
    · rw [X.shape_f _ _ h]
      simp)

@[reassoc (attr := simp)]
lemma fCycles_ιD (i j : κ) : X.fCycles i j ≫ X.ιD j = X.dComplex.iCycles i ≫ X.f i j :=
  Abelian.monoLift_comp _ _ _

lemma toCycles_fCycles (i j : κ) :
    X.dComplex.toCycles (i - (b + c)) i ≫ X.fCycles i j = 0 := by
  rw [← cancel_mono (X.ιD j), Category.assoc, fCycles_ιD, ← Category.assoc,
    HomologicalComplex.toCycles_i]
  simp [d]

/-- The morphisms `f' : E' i ⟶ D' j` of the derived couple, induced by `f` on cycles. -/
noncomputable def f' (i j : κ) : X.E' i ⟶ X.D' j :=
  (X.dComplex.homologyIsCokernel (i - (b + c)) i (dComplex_prev i)).desc
    (CokernelCofork.ofπ (X.fCycles i j) (X.toCycles_fCycles i j))

@[reassoc (attr := simp)]
lemma homologyπ_f' (i j : κ) : X.dComplex.homologyπ i ≫ X.f' i j = X.fCycles i j :=
  (X.dComplex.homologyIsCokernel (i - (b + c)) i (dComplex_prev i)).fac _
    WalkingParallelPair.one

lemma shape_f' (i j : κ) (h : i + b ≠ j) : X.f' i j = 0 := by
  rw [← cancel_epi (X.dComplex.homologyπ i), homologyπ_f', ← cancel_mono (X.ιD j),
    fCycles_ιD, X.shape_f _ _ h]
  simp

/-- `g` as a morphism to the cycles of `(E, d)`. -/
noncomputable def gCycles (l k : κ) : X.D l ⟶ X.cycles k :=
  X.dComplex.liftCycles (X.g l k) (k + (b + c)) (dComplex_next k) (by simp [d])

@[reassoc (attr := simp)]
lemma gCycles_i (l k : κ) : X.gCycles l k ≫ X.dComplex.iCycles k = X.g l k := by
  simp [gCycles]

@[reassoc]
lemma f_gCycles (m l k : κ) (h : m + b = l) :
    X.f m l ≫ X.gCycles l k = X.dComplex.toCycles m k := by
  rw [← cancel_mono (X.dComplex.iCycles k)]
  simp [X.d_eq m l k h]

/-- The morphisms `g' : D' i ⟶ E' k` of the derived couple, `g'(α y) = [g y]`. -/
noncomputable def g' (i k : κ) : X.D' i ⟶ X.E' k :=
  Abelian.epiDesc (X.πD i) (X.gCycles (i - a) k ≫ X.dComplex.homologyπ k) (by
    have h₁ : kernel.ι (X.πD i) ≫ X.α (i - a) i = 0 := by
      rw [← X.πD_ιD, kernel.condition_assoc, zero_comp]
    obtain ⟨A', π, _, y, hy⟩ := (X.exact_f_α (i - a - b) (i - a) i
      (sub_add_cancel _ _) (sub_add_cancel _ _)).exact_up_to_refinements _ h₁
    rw [← cancel_epi π, ← Category.assoc, hy]
    dsimp
    rw [comp_zero, Category.assoc, X.f_gCycles_assoc _ _ _ (sub_add_cancel _ _),
      HomologicalComplex.toCycles_comp_homologyπ, comp_zero])

@[reassoc (attr := simp)]
lemma πD_g' (i k : κ) :
    X.πD i ≫ X.g' i k = X.gCycles (i - a) k ≫ X.dComplex.homologyπ k :=
  Abelian.comp_epiDesc _ _ _

lemma shape_g' (i k : κ) (h : i + (c - a) ≠ k) : X.g' i k = 0 := by
  rw [← cancel_epi (X.πD i), πD_g', comp_zero]
  have : X.g (i - a) k = 0 := X.shape_g _ _ (by intro h'; apply h; rw [← h']; abel)
  have h' : X.gCycles (i - a) k = 0 := by
    rw [← cancel_mono (X.dComplex.iCycles k), gCycles_i, this, zero_comp]
  rw [h', zero_comp]

@[reassoc (attr := simp)]
lemma α'_g' (i j k : κ) : X.α' i j ≫ X.g' j k = 0 := by
  by_cases h : i + a = j
  · obtain rfl : i = j - a := eq_sub_of_add_eq h
    have : X.α (j - a - a) (j - a) ≫ X.gCycles (j - a) k = 0 := by
      rw [← cancel_mono (X.dComplex.iCycles k)]
      simp
    rw [← cancel_epi (X.πD (j - a)), X.πD_α'_assoc, πD_g', reassoc_of% this]
    simp
  · rw [X.shape_α' _ _ h, zero_comp]

@[reassoc (attr := simp)]
lemma g'_f' (i j k : κ) : X.g' i j ≫ X.f' j k = 0 := by
  rw [← cancel_epi (X.πD i), πD_g'_assoc, homologyπ_f', comp_zero, ← cancel_mono (X.ιD k)]
  simp

@[reassoc (attr := simp)]
lemma f'_α' (i j k : κ) : X.f' i j ≫ X.α' j k = 0 := by
  rw [← cancel_epi (X.dComplex.homologyπ i), homologyπ_f'_assoc, comp_zero,
    ← cancel_mono (X.ιD k)]
  simp

lemma exact_α'_g' (i j k : κ) (hij : i + a = j) (hjk : j + (c - a) = k) :
    (ShortComplex.mk _ _ (X.α'_g' i j k)).Exact := by
  obtain rfl : i = j - a := eq_sub_of_add_eq hij
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x hx
  dsimp at x hx ⊢
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ := surjective_up_to_refinements_of_epi (X.πD j) x
  have h₁ : (x₁ ≫ X.gCycles (j - a) k) ≫ X.dComplex.homologyπ k = 0 := by
    rw [Category.assoc, ← πD_g', ← Category.assoc, ← hx₁, Category.assoc, hx, comp_zero]
  obtain ⟨A₂, π₂, _, z, hz⟩ := (X.dComplex.comp_homologyπ_eq_zero_iff_up_to_refinements
    (k - (b + c)) k (dComplex_prev k) _).1 h₁
  have hm : k - (b + c) + b = j - a := by
    rw [← hjk]; abel
  have hgk : j - a + c = k := by
    rw [← hjk]; abel
  have h₂ : (π₂ ≫ x₁ - z ≫ X.f (k - (b + c)) (j - a)) ≫ X.g (j - a) k = 0 := by
    have := hz =≫ X.dComplex.iCycles k
    simp only [Category.assoc, gCycles_i, HomologicalComplex.toCycles_i, dComplex_d,
      X.d_eq _ _ _ hm] at this
    rw [Preadditive.sub_comp, Category.assoc, this, Category.assoc, sub_self]
  obtain ⟨A₃, π₃, _, w, hw⟩ := (X.exact_α_g (j - a - a) (j - a) k (sub_add_cancel _ _)
    hgk).exact_up_to_refinements _ h₂
  dsimp at hw
  refine ⟨A₃, π₃ ≫ π₂ ≫ π₁, inferInstance, w ≫ X.πD (j - a), ?_⟩
  have e₁ : (π₃ ≫ π₂ ≫ π₁) ≫ x = π₃ ≫ (π₂ ≫ x₁) ≫ X.πD j := by
    simp only [Category.assoc, hx₁]
  rw [e₁, Category.assoc w, X.πD_α', ← Category.assoc w, ← hw]
  simp [Preadditive.sub_comp]

lemma exact_g'_f' (i j k : κ) (hij : i + (c - a) = j) (hjk : j + b = k) :
    (ShortComplex.mk _ _ (X.g'_f' i j k)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x hx
  dsimp at x hx ⊢
  obtain ⟨A₁, π₁, _, z, hz, hπ⟩ := X.dComplex.eq_liftCycles_homologyπ_up_to_refinements x
    (j + (b + c)) (dComplex_next j)
  have h₁ : z ≫ X.f j k = 0 := by
    have : X.dComplex.liftCycles z _ (dComplex_next j) hz ≫ X.fCycles j k = 0 := by
      rw [← homologyπ_f', ← Category.assoc, ← hπ, Category.assoc, hx, comp_zero]
    have := this =≫ X.ιD k
    simpa using this
  have hij' : i - a + c = j := by
    rw [← hij]; abel
  obtain ⟨A₂, π₂, _, y, hy⟩ := (X.exact_g_f (i - a) j k hij' hjk).exact_up_to_refinements z h₁
  dsimp at hy
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, y ≫ X.πD i, ?_⟩
  rw [Category.assoc, hπ, Category.assoc, πD_g', ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono (X.dComplex.iCycles j)]
  simp [hy]

lemma exact_f'_α' (i j k : κ) (hij : i + b = j) (hjk : j + a = k) :
    (ShortComplex.mk _ _ (X.f'_α' i j k)).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x hx
  dsimp at x hx ⊢
  have h₁ : (x ≫ X.ιD j) ≫ X.α j k = 0 := by
    rw [Category.assoc, ← α'_ιD, ← Category.assoc, hx, zero_comp]
  obtain ⟨A₁, π₁, _, e, he⟩ := (X.exact_f_α i j k hij hjk).exact_up_to_refinements _ h₁
  dsimp at he
  have h₂ : e ≫ X.dComplex.d i (i + (b + c)) = 0 := by
    rw [dComplex_d, X.d_eq i j _ hij, ← Category.assoc, ← he]
    simp
  refine ⟨A₁, π₁, inferInstance,
    X.dComplex.liftCycles e _ (dComplex_next i) h₂ ≫ X.dComplex.homologyπ i, ?_⟩
  rw [← cancel_mono (X.ιD j), Category.assoc, he]
  simp

/-- The **derived couple** of an exact couple: `D' = im α`, `E' = H(E, d)`, `α' = α|_{D'}`,
`f'([x]) = f x` for `x ∈ ker d`, and `g'(α y) = [g y]`. The degree of `g'` is `c - a`.

(blueprint: `def-sp-exact-couple`) -/
noncomputable def derived : ExactCouple C a b (c - a) where
  D := X.D'
  E := X.E'
  α := X.α'
  f := X.f'
  g := X.g'
  shape_α := X.shape_α'
  shape_f := X.shape_f'
  shape_g := X.shape_g'
  α_g := X.α'_g'
  g_f := X.g'_f'
  f_α := X.f'_α'
  exact_α_g := X.exact_α'_g'
  exact_g_f := X.exact_g'_f'
  exact_f_α := X.exact_f'_α'

@[simp] lemma derived_D (i : κ) : X.derived.D i = X.D' i := rfl
@[simp] lemma derived_E (i : κ) : X.derived.E i = X.E' i := rfl
@[simp] lemma derived_α (i j : κ) : X.derived.α i j = X.α' i j := rfl
@[simp] lemma derived_f (i j : κ) : X.derived.f i j = X.f' i j := rfl
@[simp] lemma derived_g (i j : κ) : X.derived.g i j = X.g' i j := rfl

variable (a c) in
/-- The degree `c - n • a` of the map `g` of the `n`-th derived couple. -/
def degIter : ℕ → κ
  | 0 => c
  | n + 1 => degIter n - a

lemma degIter_eq (n : ℕ) : degIter a c n = c - (n : ℤ) • a := by
  induction n with
  | zero => simp [degIter]
  | succ n ih => simp [degIter, ih, add_smul, sub_add_eq_sub_sub]

/-- The iterated derived couples: `derivedIter 0 = X` and `derivedIter (n + 1)` is the derived
couple of `derivedIter n`. -/
noncomputable def derivedIter : (n : ℕ) → ExactCouple C a b (degIter a c n)
  | 0 => X
  | n + 1 => (derivedIter n).derived

@[simp] lemma derivedIter_zero : X.derivedIter 0 = X := rfl

@[simp] lemma derivedIter_succ (n : ℕ) : X.derivedIter (n + 1) = (X.derivedIter n).derived :=
  rfl

/-! ### The spectral sequence of an exact couple -/

lemma homology_dComplex_derivedIter (n m : ℕ) (h : m = n + 1) (pq : κ) :
    (X.derivedIter n).dComplex.homology pq = (X.derivedIter m).dComplex.X pq := by
  subst h
  rfl

variable (a b c) in
/-- The complex shapes of the pages of the spectral sequence of an exact couple, starting on
page `r₀`: the differential of the `r`-th page has degree `b + c - (r - r₀) • a`. -/
def pageShape (r₀ r : ℤ) : ComplexShape κ :=
  ComplexShape.up' (b + degIter a c (r - r₀).toNat)

/-- The **spectral sequence of an exact couple**, starting on page `r₀`: its `r`-th page is the
complex `(E, d)` of the `(r - r₀)`-th derived couple, whose homology is the `E`-object of the
next derived couple.

(blueprint: `def-sp-exact-couple`) -/
noncomputable def spectralSequence (r₀ : ℤ) : SpectralSequence C (pageShape a b c r₀) r₀ where
  page r _ := (X.derivedIter (r - r₀).toNat).dComplex
  iso r r' pq hrr' hr := eqToIso (X.homology_dComplex_derivedIter _ _ (by omega) pq)

lemma spectralSequence_page (r₀ r : ℤ) (hr : r₀ ≤ r) :
    (X.spectralSequence r₀).page r hr = (X.derivedIter (r - r₀).toNat).dComplex :=
  rfl


/-! ### The `D`-objects of the iterated derived couples -/

open Classical in
/-- The `n`-fold composite `D k ⟶ D (k + n • a)` of the maps `α`, as a morphism `D k ⟶ D i`
which vanishes unless `i = k + n • a`. -/
noncomputable def αPow : ℕ → (k i : κ) → X.D k ⟶ X.D i
  | 0, k, i => if h : k = i then eqToHom (congrArg X.D h) else 0
  | n + 1, k, i => αPow n k (i - a) ≫ X.α (i - a) i

/-- The inclusion of the `D`-objects of the `n`-th derived couple into those of `X`. -/
noncomputable def ιIter : (n : ℕ) → (i : κ) → (X.derivedIter n).D i ⟶ X.D i
  | 0, _ => 𝟙 _
  | n + 1, i => (X.derivedIter n).ιD i ≫ ιIter n i

instance (n : ℕ) (i : κ) : Mono (X.ιIter n i) := by
  induction n generalizing i with
  | zero => dsimp [ιIter]; infer_instance
  | succ n ih => dsimp [ιIter]; infer_instance

@[reassoc]
lemma α_ιIter (n : ℕ) (i j : κ) :
    (X.derivedIter n).α i j ≫ X.ιIter n j = X.ιIter n i ≫ X.α i j := by
  induction n generalizing i j with
  | zero => simp [ιIter]
  | succ n ih =>
    simp only [derivedIter_succ, derived_α, ιIter]
    rw [← Category.assoc, α'_ιD, Category.assoc, ih, Category.assoc]

/-- **The `D`-objects of the `n`-th derived couple are the images of `αⁿ`**: for
`k + n • a = i`, there is an epimorphism `D k ⟶ (derivedIter n).D i` whose composite with the
inclusion `ιIter n i` is `αⁿ : D k ⟶ D i`. -/
lemma exists_epi_comp_ιIter (n : ℕ) (k i : κ) (h : k + (n : ℤ) • a = i) :
    ∃ π : X.D k ⟶ (X.derivedIter n).D i, Epi π ∧ π ≫ X.ιIter n i = X.αPow n k i := by
  induction n generalizing k i with
  | zero =>
    simp only [Nat.cast_zero, zero_smul, add_zero] at h
    subst h
    exact ⟨𝟙 _, inferInstance, by simp [ιIter, αPow]⟩
  | succ n ih =>
    obtain ⟨π, _, hπ⟩ := ih k (i - a) (by rw [← h]; push_cast; rw [add_smul, one_smul]; abel)
    refine ⟨π ≫ (X.derivedIter n).πD i, inferInstance, ?_⟩
    simp only [ιIter, αPow]
    rw [Category.assoc, (X.derivedIter n).πD_ιD_assoc, α_ιIter, reassoc_of% hπ]

end ExactCouple

end CategoryTheory
