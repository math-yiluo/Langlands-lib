/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Data.Int.Interval
public import WeilConjectures.CategoryTheory.PBCFiltration

/-!
# The two filtrations of a first-quadrant total complex

Source: Stacks Project, Homological Algebra, Section 12.18, Tag 012Z, and the
blueprint's two filtrations and graded pieces (blueprint: def-sp-double-complex-total).

The bicomplex and total complex are Mathlib's `HomologicalComplex₂` and `total`.
First-quadrant vanishing is a hypothesis, not extra structure. Only the two finite
supremum filtrations are new definitions. The remaining clauses are theorem statements.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- First-quadrant vanishing implies existence of the diagonal coproducts.
Source: Stacks 12.18, following Tag 012Z (blueprint: def-sp-double-complex-total).
Proof: in degree n only indices 0 ≤ p ≤ n can be nonzero. Take their finite
coproduct, extending its cocone by the unique maps from the zero objects outside
that interval. The finite coproduct universal property gives the full diagonal colimit. -/
theorem hasTotal_of_firstQuadrant
    (hK : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((K.X p).X q)) :
    K.HasTotal (ComplexShape.up ℤ) := by
  classical
  intro n
  let D := {ij : ℤ × ℤ // ij.1 + ij.2 = n}
  let S := {ij : D // 0 ≤ ij.1.1 ∧ 0 ≤ ij.1.2}
  let g : S → ↥(Finset.Icc (0 : ℤ) n) := fun ij ↦
    ⟨ij.1.1.1, Finset.mem_Icc.mpr ⟨ij.2.1, by
      have := ij.1.2
      have := ij.2.2
      omega⟩⟩
  have hg : Function.Injective g := by
    intro i j h
    have hp : i.1.1.1 = j.1.1.1 := congrArg Subtype.val h
    have hi := i.1.2
    have hj := j.1.2
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext hp
    omega
  have : Finite S := Finite.of_injective g hg
  let X : D → C := fun ij ↦ (K.X ij.1.1).X ij.1.2
  let Y : S → C := fun ij ↦ X ij.1
  let c : Cofan X := Cofan.mk (∐ Y) (fun ij ↦
    if h : 0 ≤ ij.1.1 ∧ 0 ≤ ij.1.2 then Sigma.ι Y ⟨ij, h⟩ else 0)
  refine HasColimit.mk ⟨c, ?_⟩
  refine Cofan.IsColimit.mk c (fun t ↦ Sigma.desc (fun ij : S ↦ t.inj ij.1)) ?_ ?_
  · intro t ij
    dsimp [c]
    split_ifs with h
    · exact Sigma.ι_comp_desc _ _
    · exact (hK ij.1.1 ij.1.2 (by omega)).eq_of_src _ _
  · intro t m hm
    apply Sigma.hom_ext (f := Y)
    intro ij
    have hi := hm ij.1
    simpa [c, ij.2, Sigma.ι_comp_desc] using hi

variable [K.HasTotal (ComplexShape.up ℤ)]

/-- A subobject containing all diagonal coprojections is the whole total object. -/
private theorem eq_top_of_total_inclusions (n : ℤ)
    (S : Subobject ((K.total (ComplexShape.up ℤ)).X n))
    (hS : ∀ i j : ℤ, ∀ h : i + j = n,
      imageSubobject (K.ιTotal (ComplexShape.up ℤ) i j n h) ≤ S) : S = ⊤ := by
  let a := fun i j h ↦
    factorThruImageSubobject (K.ιTotal (ComplexShape.up ℤ) i j n h) ≫
      Subobject.ofLE _ S (hS i j h)
  let r := K.totalDesc a
  have hr : r ≫ S.arrow = 𝟙 _ := by
    apply total.hom_ext
    intro i j h
    simp [r, a]
  have : IsSplitEpi S.arrow := IsSplitEpi.mk' ⟨r, hr⟩
  have : IsIso S.arrow := isIso_of_mono_of_isSplitEpi S.arrow
  exact Subobject.eq_top_of_isIso_arrow S

/-- The finite supremum defining the first filtration decreases with its index.
Source: blueprint filtration formula (blueprint: def-sp-double-complex-total).
Proof: if p ≤ q, the interval [q,n] is contained in [p,n]. Every image in the
smaller supremum lies in the larger one; the finite supremum universal property
proves the inequality, including when either interval is empty. -/
theorem firstFiltration_antitone (n : ℤ) :
    Antitone (fun p : ℤ ↦ (Finset.Icc p n).sup
      (fun i ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n))) := by
  intro p q hpq
  apply Finset.sup_mono
  intro i hi
  simp only [Finset.mem_Icc] at hi ⊢
  exact ⟨hpq.trans hi.1, hi.2⟩

/-- Filtration by the first degree, as the finite sum of images of diagonal inclusions.
Source: blueprint filtration formula (blueprint: def-sp-double-complex-total).
Terms past n vanish for a first-quadrant bicomplex, so this finite supremum
is exactly the stated sum over indices at least p. -/
noncomputable def firstFiltration (n : ℤ) :
    PBCDecreasingFiltration ((K.total (ComplexShape.up ℤ)).X n) where
  step p := (Finset.Icc p n).sup
    (fun i ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n))
  antitone_step := K.firstFiltration_antitone n

/-- The finite supremum defining the second filtration decreases with its index.
Source: blueprint filtration formula (blueprint: def-sp-double-complex-total).
Proof: if p ≤ q, the interval [q,n] is contained in [p,n]. Every image in the
smaller supremum lies in the larger one; the finite supremum universal property
proves the inequality, including when either interval is empty. -/
theorem secondFiltration_antitone (n : ℤ) :
    Antitone (fun p : ℤ ↦ (Finset.Icc p n).sup
      (fun i ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n))) := by
  intro p q hpq
  apply Finset.sup_mono
  intro i hi
  simp only [Finset.mem_Icc] at hi ⊢
  exact ⟨hpq.trans hi.1, hi.2⟩

/-- Filtration by the second degree, as the finite sum of images of diagonal inclusions.
Source: blueprint filtration formula (blueprint: def-sp-double-complex-total).
Terms past n vanish for a first-quadrant bicomplex, so this finite supremum
is exactly the stated sum over indices at least p. -/
noncomputable def secondFiltration (n : ℤ) :
    PBCDecreasingFiltration ((K.total (ComplexShape.up ℤ)).X n) where
  step p := (Finset.Icc p n).sup
    (fun i ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n))
  antitone_step := K.secondFiltration_antitone n

/-- A morphism factors through any subobject containing its image. -/
private theorem factors_image (X Y : C) (f : X ⟶ Y) (S : Subobject Y)
    (h : imageSubobject f ≤ S) : S.Factors f := by
  apply Subobject.factors_of_le f h
  simpa using imageSubobject_factors_comp_self f (𝟙 X)

/-- Preservation of each generating image implies preservation of their finite supremum. -/
private theorem factors_finset_sup {I : Type*} (s : Finset I) {A : I → C}
    {X Y : C} (a : ∀ i, A i ⟶ X) (d : X ⟶ Y) (Q : Subobject Y)
    (h : ∀ i ∈ s, Q.Factors (a i ≫ d)) :
    Q.Factors ((s.sup (fun i ↦ imageSubobject (a i))).arrow ≫ d) := by
  let P := (Subobject.pullback d).obj Q
  have hs : s.sup (fun i ↦ imageSubobject (a i)) ≤ P := by
    apply Finset.sup_le
    intro i hi
    have hf := pullback_factors d Q (a i) (h i hi)
    exact imageSubobject_le (a i) (P.factorThru (a i) hf)
      (Subobject.factorThru_arrow _ _ _)
  apply (pullback_factors_iff d Q _).1
  exact Subobject.factors_of_le _ hs (Subobject.factors_self _)

/-- An integer multiple of a morphism has the same subobject factorization. -/
private theorem factors_zsmul {X Y : C} (Q : Subobject Y) (a : X ⟶ Y)
    (h : Q.Factors a) (z : ℤ) : Q.Factors (z • a) := by
  rw [← Subobject.factorThru_arrow Q a h, ← CategoryTheory.Preadditive.zsmul_comp]
  exact Subobject.factors_comp_arrow _

/-- The canonical lifts of the generating maps jointly detect maps from their image supremum. -/
private theorem finite_sup_hom_ext {I : Type*} (s : Finset I) {A : I → C}
    {X Y : C} (a : ∀ i, A i ⟶ X)
    (g h : ((s.sup (fun i ↦ imageSubobject (a i)) : Subobject X) : C) ⟶ Y)
    (w : ∀ i, ∀ hi : i ∈ s,
      (factorThruImageSubobject (a i) ≫ Subobject.ofLE _ _
        (Finset.le_sup (f := fun i ↦ imageSubobject (a i)) hi)) ≫ g =
      (factorThruImageSubobject (a i) ≫ Subobject.ofLE _ _
        (Finset.le_sup (f := fun i ↦ imageSubobject (a i)) hi)) ≫ h) :
    g = h := by
  let S := s.sup (fun i ↦ imageSubobject (a i))
  let e := equalizer.ι g h ≫ S.arrow
  have hs : S ≤ Subobject.mk e := by
    apply Finset.sup_le
    intro i hi
    let l := factorThruImageSubobject (a i) ≫ Subobject.ofLE _ S
      (Finset.le_sup (f := fun i ↦ imageSubobject (a i)) hi)
    apply imageSubobject_le_mk e (a i) (equalizer.lift l (w i hi))
    simp [e, l]
  let r := Subobject.ofLE S (Subobject.mk e) hs ≫ (Subobject.underlyingIso e).hom
  have hr : r ≫ equalizer.ι g h = 𝟙 _ := by
    apply (cancel_mono S.arrow).1
    rw [Category.assoc, Category.id_comp]
    change r ≫ e = S.arrow
    simp [r]
  have : IsSplitEpi (equalizer.ι g h) := IsSplitEpi.mk' ⟨r, hr⟩
  exact (cancel_epi (equalizer.ι g h)).1 (equalizer.condition g h)

/--
A projection onto one summand identifies the quotient by the remaining tail with that summand. -/
private theorem finite_sup_cokernel_iso {A : ℤ → C} {V : C}
    (a : ∀ i, A i ⟶ V) (p n : ℤ) (r : V ⟶ A p)
    (hr : a p ≫ r = 𝟙 _) (hri : ∀ i, i ≠ p → a i ≫ r = 0)
    (hz : n < p → IsZero (A p)) :
    (let S := (Finset.Icc p n).sup (fun i ↦ imageSubobject (a i))
    let T := (Finset.Icc (p + 1) n).sup (fun i ↦ imageSubobject (a i))
    let le : T ≤ S := Finset.sup_mono (by
      intro i hi
      simp only [Finset.mem_Icc] at hi ⊢
      omega)
    ∃ l : A p ⟶ (S : C), l ≫ S.arrow = a p ∧
      IsIso (l ≫ cokernel.π (Subobject.ofLE T S le))) := by
  dsimp only
  let S := (Finset.Icc p n).sup (fun i ↦ imageSubobject (a i))
  let T := (Finset.Icc (p + 1) n).sup (fun i ↦ imageSubobject (a i))
  have hTS : T ≤ S := Finset.sup_mono (by
    intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega)
  let f := Subobject.ofLE T S hTS
  have ha : S.Factors (a p) := by
    by_cases hpn : p ≤ n
    · apply factors_image
      exact Finset.le_sup (s := Finset.Icc p n)
        (f := fun i ↦ imageSubobject (a i)) (Finset.mem_Icc.mpr ⟨le_rfl, hpn⟩)
    · rw [(hz (by omega)).eq_zero_of_src (a p)]
      exact Subobject.factors_zero
  let l := S.factorThru (a p) ha
  have hl : l ≫ S.arrow = a p := Subobject.factorThru_arrow _ _ _
  have ht : T.arrow ≫ r = 0 := by
    apply (Subobject.bot_factors_iff_zero _).1
    apply factors_finset_sup (Finset.Icc (p + 1) n) a r ⊥
    intro i hi
    rw [hri i (by have := (Finset.mem_Icc.mp hi).1; omega)]
    exact Subobject.factors_zero
  have hf : f ≫ (S.arrow ≫ r) = 0 := by
    rw [← Category.assoc, Subobject.ofLE_arrow, ht]
  let b := cokernel.desc f (S.arrow ≫ r) hf
  have hb : cokernel.π f ≫ b = S.arrow ≫ r := cokernel.π_desc _ _ _
  have hab : (l ≫ cokernel.π f) ≫ b = 𝟙 _ := by
    rw [Category.assoc, hb, ← Category.assoc, hl, hr]
  have hba : b ≫ (l ≫ cokernel.π f) = 𝟙 _ := by
    apply (cancel_epi (cokernel.π f)).1
    rw [← Category.assoc, hb, Category.comp_id]
    apply finite_sup_hom_ext (Finset.Icc p n) a
    intro i hi
    let li := factorThruImageSubobject (a i) ≫ Subobject.ofLE _ S
      (Finset.le_sup (f := fun i ↦ imageSubobject (a i)) hi)
    have hli : li ≫ S.arrow = a i := by simp [li]
    change li ≫ ((S.arrow ≫ r) ≫ l ≫ cokernel.π f) = li ≫ cokernel.π f
    by_cases hip : i = p
    · subst i
      have hil : li = l := (cancel_mono S.arrow).1 (hli.trans hl.symm)
      rw [hil]
      simp only [Category.assoc, reassoc_of% hl, reassoc_of% hr]
    · have hit : i ∈ Finset.Icc (p + 1) n := by
        have := Finset.mem_Icc.mp hi
        exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
      let ti := factorThruImageSubobject (a i) ≫ Subobject.ofLE _ T
        (Finset.le_sup (f := fun i ↦ imageSubobject (a i)) hit)
      have hilt : li = ti ≫ f := by
        apply (cancel_mono S.arrow).1
        simp [li, ti, f]
      simp only [Category.assoc, reassoc_of% hli, reassoc_of% (hri i hip),
        CategoryTheory.Limits.zero_comp]
      rw [hilt, Category.assoc, cokernel.condition, CategoryTheory.Limits.comp_zero]
  have hiso : IsIso (l ≫ cokernel.π f) :=
    (⟨l ≫ cokernel.π f, b, hab, hba⟩ : A p ≅ cokernel f).isIso_hom
  exact ⟨l, hl, hiso⟩

/-- The first graded-piece isomorphism is induced by the original diagonal inclusion. -/
private theorem first_graded_iso
    (hK : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((K.X i).X j)) (p n : ℤ) :
    ∃ a : (K.X p).X (n - p) ⟶ ((K.firstFiltration n).step p : C),
      a ≫ ((K.firstFiltration n).step p).arrow =
        K.ιTotalOrZero (ComplexShape.up ℤ) p (n - p) n ∧
      IsIso (a ≫ cokernel.π (Subobject.ofLE ((K.firstFiltration n).step (p + 1))
        ((K.firstFiltration n).step p) ((K.firstFiltration n).antitone_step (by omega)))) := by
  classical
  let r : (K.total (ComplexShape.up ℤ)).X n ⟶ (K.X p).X (n - p) :=
    K.totalDesc (fun i j hij ↦ if hi : i = p then
      (K.XXIsoOfEq _ _ _ hi (by change i + j = n at hij; omega)).hom else 0)
  apply finite_sup_cokernel_iso
    (fun i ↦ K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n) p n r
  · rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) p (n - p) n (by
      change p + (n - p) = n; omega)]
    simp [r, XXIsoOfEq_rfl]
  · intro i hi
    rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) i (n - i) n (by
      change i + (n - i) = n; omega)]
    simp [r, hi]
  · intro hn
    exact hK p (n - p) (Or.inr (by omega))

/-- The second graded-piece isomorphism is induced by the original diagonal inclusion. -/
private theorem second_graded_iso
    (hK : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((K.X i).X j)) (p n : ℤ) :
    ∃ a : (K.X (n - p)).X p ⟶ ((K.secondFiltration n).step p : C),
      a ≫ ((K.secondFiltration n).step p).arrow =
        K.ιTotalOrZero (ComplexShape.up ℤ) (n - p) p n ∧
      IsIso (a ≫ cokernel.π (Subobject.ofLE ((K.secondFiltration n).step (p + 1))
        ((K.secondFiltration n).step p) ((K.secondFiltration n).antitone_step (by omega)))) := by
  classical
  let r : (K.total (ComplexShape.up ℤ)).X n ⟶ (K.X (n - p)).X p :=
    K.totalDesc (fun i j hij ↦ if hj : j = p then
      (K.XXIsoOfEq _ _ _ (by change i + j = n at hij; omega) hj).hom else 0)
  apply finite_sup_cokernel_iso
    (fun i ↦ K.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n) p n r
  · rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) (n - p) p n (by
      change (n - p) + p = n; omega)]
    simp [r, XXIsoOfEq_rfl]
  · intro i hi
    rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) (n - i) i n (by
      change (n - i) + i = n; omega)]
    simp [r, hi]
  · intro hn
    exact hK (n - p) p (Or.inl (by omega))

/-- Restrictions of a differential descend to graded pieces and still square to zero. -/
private theorem graded_differential (L : CochainComplex C ℤ)
    (F : ∀ n : ℤ, PBCDecreasingFiltration (L.X n)) (p : ℤ)
    (hF : ∀ q n : ℤ, ∃ f : ((F n).step q : C) ⟶ ((F (n + 1)).step q : C),
      f ≫ ((F (n + 1)).step q).arrow = ((F n).step q).arrow ≫ L.d n (n + 1)) :
    (let π := fun n : ℤ ↦ cokernel.π (Subobject.ofLE ((F n).step (p + 1))
      ((F n).step p) ((F n).antitone_step (by omega)))
    ∃ (f : ∀ n : ℤ, ((F n).step p : C) ⟶ ((F (n + 1)).step p : C))
      (δ : ∀ n : ℤ, (F n).gradedPiece p ⟶ (F (n + 1)).gradedPiece p),
      (∀ n : ℤ, f n ≫ ((F (n + 1)).step p).arrow =
        ((F n).step p).arrow ≫ L.d n (n + 1)) ∧
      (∀ n : ℤ, π n ≫ δ n = f n ≫ π (n + 1)) ∧
      (∀ n : ℤ, δ n ≫ δ (n + 1) = 0)) := by
  classical
  let f := fun q n ↦ (hF q n).choose
  have hf : ∀ q n, f q n ≫ ((F (n + 1)).step q).arrow =
      ((F n).step q).arrow ≫ L.d n (n + 1) := fun q n ↦ (hF q n).choose_spec
  let inc := fun n ↦ Subobject.ofLE ((F n).step (p + 1)) ((F n).step p)
    ((F n).antitone_step (by omega))
  let π := fun n ↦ cokernel.π (inc n)
  have hw : ∀ n, inc n ≫ f p n = f (p + 1) n ≫ inc (n + 1) := by
    intro n
    apply (cancel_mono ((F (n + 1)).step p).arrow).1
    dsimp only [inc]
    rw [Category.assoc, hf, ← Category.assoc, Subobject.ofLE_arrow,
      Category.assoc, Subobject.ofLE_arrow, hf]
  have hz : ∀ n, inc n ≫ (f p n ≫ π (n + 1)) = 0 := by
    intro n
    rw [← Category.assoc, hw, Category.assoc]
    simp [π]
  let δ := fun n ↦ cokernel.desc (inc n) (f p n ≫ π (n + 1)) (hz n)
  have hδ : ∀ n, π n ≫ δ n = f p n ≫ π (n + 1) := by
    intro n
    exact cokernel.π_desc _ _ _
  have hff : ∀ n, f p n ≫ f p (n + 1) = 0 := by
    intro n
    apply (cancel_mono ((F ((n + 1) + 1)).step p).arrow).1
    rw [Category.assoc, hf, ← Category.assoc, hf, Category.assoc,
      L.d_comp_d, CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]
  refine ⟨f p, δ, hf p, hδ, ?_⟩
  intro n
  apply (cancel_epi (π n)).1
  rw [← Category.assoc, hδ, Category.assoc, hδ, ← Category.assoc, hff,
    CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]

/-- A diagonal inclusion with first index at least p factors through the first step p. -/
private theorem firstFiltration_inclusion_factors
    (hK : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((K.X i).X j))
    (p i j n : ℤ) (hij : i + j = n) (hpi : p ≤ i) :
    ((K.firstFiltration n).step p).Factors
      (K.ιTotalOrZero (ComplexShape.up ℤ) i j n) := by
  by_cases hin : i ≤ n
  · apply factors_image
    have hm : i ∈ Finset.Icc p n := Finset.mem_Icc.mpr ⟨hpi, hin⟩
    have hh := Finset.le_sup (f := fun k ↦ imageSubobject
      (K.ιTotalOrZero (ComplexShape.up ℤ) k (n - k) n)) hm
    have hsub : n - i = j := by omega
    rw [hsub] at hh
    exact hh
  · rw [(hK i j (Or.inr (by omega))).eq_zero_of_src
      (K.ιTotalOrZero (ComplexShape.up ℤ) i j n)]
    exact Subobject.factors_zero

/-- A diagonal inclusion with second index at least p factors through the second step p. -/
private theorem secondFiltration_inclusion_factors
    (hK : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((K.X i).X j))
    (p i j n : ℤ) (hij : i + j = n) (hpi : p ≤ j) :
    ((K.secondFiltration n).step p).Factors
      (K.ιTotalOrZero (ComplexShape.up ℤ) i j n) := by
  by_cases hin : j ≤ n
  · apply factors_image
    have hm : j ∈ Finset.Icc p n := Finset.mem_Icc.mpr ⟨hpi, hin⟩
    have hh := Finset.le_sup (f := fun k ↦ imageSubobject
      (K.ιTotalOrZero (ComplexShape.up ℤ) (n - k) k n)) hm
    have hsub : n - j = i := by omega
    rw [hsub] at hh
    exact hh
  · rw [(hK i j (Or.inl (by omega))).eq_zero_of_src
      (K.ιTotalOrZero (ComplexShape.up ℤ) i j n)]
    exact Subobject.factors_zero

variable (hK : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((K.X p).X q))

include hK

/-- The negative degrees of the total complex vanish.
Source: Stacks 12.18, finite diagonals (blueprint: def-sp-double-complex-total).
Proof: p+q=n<0 forces p<0 or q<0, so every summand is zero. The coproduct
universal property makes the total object a zero object. -/
theorem total_isZero_of_neg (n : ℤ) (hn : n < 0) :
    IsZero ((K.total (ComplexShape.up ℤ)).X n) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply total.hom_ext
  intro i j hij
  have hsum : i + j = n := hij
  exact (hK i j (by omega)).eq_of_src _ _

/-- The first filtration is preserved by the total differential.
Source: blueprint subcomplex clause (blueprint: def-sp-double-complex-total).
Proof: on each summand the total differential is the horizontal map plus the
signed vertical map. Each preserves or raises the filtered index. Each image
therefore factors through the target step, and the finite sum does too. -/
theorem firstFiltration_subcomplex (p n : ℤ) :
    ∃ f : ((K.firstFiltration n).step p : C) ⟶
      ((K.firstFiltration (n + 1)).step p : C),
      f ≫ ((K.firstFiltration (n + 1)).step p).arrow =
        ((K.firstFiltration n).step p).arrow ≫
          (K.total (ComplexShape.up ℤ)).d n (n + 1) := by
  have _ := hK
  let Q := (K.firstFiltration (n + 1)).step p
  have hQ : Q.Factors (((K.firstFiltration n).step p).arrow ≫
      (K.total (ComplexShape.up ℤ)).d n (n + 1)) := by
    dsimp [firstFiltration]
    apply factors_finset_sup (Finset.Icc p n)
      (fun i ↦ K.ιTotalOrZero (ComplexShape.up ℤ)
        i (n - i) n) _ Q
    intro i hi
    have hpi : p ≤ i := (Finset.mem_Icc.mp hi).1
    have hin : i ≤ n := (Finset.mem_Icc.mp hi).2
    rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) i (n - i) n (by
      change i + (n - i) = n
      omega), total_d, CategoryTheory.Preadditive.comp_add, ι_D₁, ι_D₂]
    rw [K.d₁_eq' (ComplexShape.up ℤ) (show
        (ComplexShape.up ℤ).Rel i (i + 1) by rfl),
      K.d₂_eq' (ComplexShape.up ℤ) i (show
        (ComplexShape.up ℤ).Rel (n - i) ((n - i) + 1) by rfl)]
    apply Subobject.factors_add
    · apply factors_zsmul
      apply Subobject.factors_of_factors_right
      apply factors_image
      dsimp [Q, firstFiltration]
      have heq : (n + 1) - (i + 1) = n - i := by omega
      rw [← heq]
      exact Finset.le_sup (s := Finset.Icc p (n + 1))
        (f := fun k ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ)
          k ((n + 1) - k) (n + 1)))
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    · apply factors_zsmul
      apply Subobject.factors_of_factors_right
      apply factors_image
      dsimp [Q, firstFiltration]
      have heq : (n + 1) - i = (n - i) + 1 := by omega
      rw [← heq]
      exact Finset.le_sup (s := Finset.Icc p (n + 1))
        (f := fun k ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ)
          k ((n + 1) - k) (n + 1)))
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  exact ⟨Q.factorThru _ hQ, Subobject.factorThru_arrow _ _ _⟩

/-- The first filtration starts at the whole total object.
Source: blueprint degreewise bounds (blueprint: def-sp-double-complex-total).
Proof: first-quadrant vanishing leaves only the summands indexed by [0,n].
Their inclusions jointly generate the diagonal coproduct, so their image sum
is top. For n<0 both the diagonal and the empty image sum are zero. -/
theorem firstFiltration_zero (n : ℤ) : (K.firstFiltration n).step 0 = ⊤ := by
  apply K.eq_top_of_total_inclusions n
  intro i j hij
  by_cases hi : 0 ≤ i
  · by_cases hj : 0 ≤ j
    · have hm : i ∈ Finset.Icc (0 : ℤ) n := Finset.mem_Icc.mpr ⟨hi, by omega⟩
      have hsub : n - i = j := by omega
      have hι := K.ιTotalOrZero_eq (ComplexShape.up ℤ) i j n hij
      have hh := Finset.le_sup (f := fun k ↦ imageSubobject
        (K.ιTotalOrZero (ComplexShape.up ℤ) k (n - k) n)) hm
      rw [hsub, hι] at hh
      exact hh
    · rw [(hK i j (Or.inr (by omega))).eq_zero_of_src
        (K.ιTotal (ComplexShape.up ℤ) i j n hij)]
      simp
  · rw [(hK i j (Or.inl (by omega))).eq_zero_of_src
      (K.ιTotal (ComplexShape.up ℤ) i j n hij)]
    simp

/-- The first filtration vanishes past the diagonal.
Source: blueprint degreewise bounds (blueprint: def-sp-double-complex-total).
Proof: [n+1,n] is empty, so its finite supremum is bottom. -/
theorem firstFiltration_finite (n : ℤ) :
    (K.firstFiltration n).step (n + 1) = ⊥ := by
  have _ := hK
  simp [firstFiltration]

/-- The canonical summand maps identify the first graded pieces and their differential.
Source: blueprint graded-piece clause (blueprint: def-sp-double-complex-total).
Proof: lift the diagonal inclusion uniquely through the step's monomorphism.
The next step is the sum of the other summands, so projecting this lift to
its cokernel is an isomorphism. Restrict the total differential to the step;
it preserves the next step as well, hence descends uniquely to the cokernel.
In the quotient the differential raising the filtered index disappears; the
remaining differential is the signed vertical map. Its square is zero because the total
differential squares to zero and the quotient maps are epimorphisms.
The equations explicitly fix the isomorphisms by the original total inclusions. -/
theorem firstFiltration_graded (p : ℤ) :
    (let F := fun n : ℤ ↦ K.firstFiltration n
    let π := fun n : ℤ ↦ cokernel.π (Subobject.ofLE ((F n).step (p + 1))
      ((F n).step p) ((F n).antitone_step (by omega)))
    ∃ (a : ∀ n : ℤ, (K.X p).X (n - p) ⟶ ((F n).step p : C))
      (f : ∀ n : ℤ, ((F n).step p : C) ⟶ ((F (n + 1)).step p : C))
      (δ : ∀ n : ℤ, (F n).gradedPiece p ⟶ (F (n + 1)).gradedPiece p),
      (∀ n : ℤ, a n ≫ ((F n).step p).arrow =
        K.ιTotalOrZero (ComplexShape.up ℤ) p (n - p) n) ∧
      (∀ n : ℤ, IsIso (a n ≫ π n)) ∧
      (∀ n : ℤ, f n ≫ ((F (n + 1)).step p).arrow =
        ((F n).step p).arrow ≫ (K.total (ComplexShape.up ℤ)).d n (n + 1)) ∧
      (∀ n : ℤ, π n ≫ δ n = f n ≫ π (n + 1)) ∧
      (∀ n : ℤ, (a n ≫ π n) ≫ δ n =
        ((-1 : ℤ) ^ p.natAbs • (K.X p).d (n - p) ((n + 1) - p)) ≫ (a (n + 1) ≫ π (n + 1))) ∧
      (∀ n : ℤ, δ n ≫ δ (n + 1) = 0)) := by
  classical
  dsimp only
  let F := fun n : ℤ ↦ K.firstFiltration n
  let inc := fun n : ℤ ↦ Subobject.ofLE ((F n).step (p + 1)) ((F n).step p)
    ((F n).antitone_step (by omega))
  let π := fun n : ℤ ↦ cokernel.π (inc n)
  let a := fun n : ℤ ↦ (K.first_graded_iso hK p n).choose
  have ha : ∀ n, a n ≫ ((F n).step p).arrow =
      K.ιTotalOrZero (ComplexShape.up ℤ) p (n - p) n :=
    fun n ↦ (K.first_graded_iso hK p n).choose_spec.1
  have hai : ∀ n, IsIso (a n ≫ π n) :=
    fun n ↦ (K.first_graded_iso hK p n).choose_spec.2
  obtain ⟨f, δ, hf, hδ, hsq⟩ := graded_differential
    (K.total (ComplexShape.up ℤ)) F p (K.firstFiltration_subcomplex hK)
  refine ⟨a, f, δ, ha, hai, hf, hδ, ?_, hsq⟩
  intro n
  have ht := K.firstFiltration_inclusion_factors hK (p + 1) (p + 1) (n - p)
    (n + 1) (by omega) le_rfl
  let b := ((F (n + 1)).step (p + 1)).factorThru
    (K.ιTotalOrZero (ComplexShape.up ℤ) (p + 1) (n - p) (n + 1)) ht
  have hb : b ≫ ((F (n + 1)).step (p + 1)).arrow =
      K.ιTotalOrZero (ComplexShape.up ℤ) (p + 1) (n - p) (n + 1) :=
    Subobject.factorThru_arrow _ _ _
  have heq : a n ≫ f n = (K.d p (p + 1)).f (n - p) ≫ b ≫ inc (n + 1) +
      ((-1 : ℤ) ^ p.natAbs • (K.X p).d (n - p) ((n + 1) - p)) ≫ a (n + 1) := by
    apply (cancel_mono ((F (n + 1)).step p).arrow).1
    simp only [CategoryTheory.Preadditive.add_comp, Category.assoc, hf, ha,
      reassoc_of% (ha n), Subobject.ofLE_arrow, inc, hb]
    rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) p (n - p) n (by
      change p + (n - p) = n; omega), total_d,
      CategoryTheory.Preadditive.comp_add, ι_D₁, ι_D₂]
    rw [K.d₁_eq' (ComplexShape.up ℤ) (show
        (ComplexShape.up ℤ).Rel p (p + 1) by rfl),
      K.d₂_eq' (ComplexShape.up ℤ) p (show
        (ComplexShape.up ℤ).Rel (n - p) ((n + 1) - p) by
          change (n - p) + 1 = (n + 1) - p
          omega)]
    change (1 : ℤˣ) • _ + p.negOnePow • _ = _
    have hs : (p.negOnePow : ℤ) = (-1 : ℤ) ^ p.natAbs := Int.coe_negOnePow ℤ p
    simp only [one_smul, Units.smul_def, hs, CategoryTheory.Preadditive.zsmul_comp]
  rw [Category.assoc, hδ, ← Category.assoc, heq,
    CategoryTheory.Preadditive.add_comp]
  simp only [inc, Category.assoc, cokernel.condition, CategoryTheory.Limits.comp_zero,
    zero_add]
  rfl

/-- The second filtration is preserved by the total differential.
Source: blueprint subcomplex clause (blueprint: def-sp-double-complex-total).
Proof: on each summand the total differential is the horizontal map plus the
signed vertical map. Each preserves or raises the filtered index. Each image
therefore factors through the target step, and the finite sum does too. -/
theorem secondFiltration_subcomplex (p n : ℤ) :
    ∃ f : ((K.secondFiltration n).step p : C) ⟶
      ((K.secondFiltration (n + 1)).step p : C),
      f ≫ ((K.secondFiltration (n + 1)).step p).arrow =
        ((K.secondFiltration n).step p).arrow ≫
          (K.total (ComplexShape.up ℤ)).d n (n + 1) := by
  have _ := hK
  let Q := (K.secondFiltration (n + 1)).step p
  have hQ : Q.Factors (((K.secondFiltration n).step p).arrow ≫
      (K.total (ComplexShape.up ℤ)).d n (n + 1)) := by
    dsimp [secondFiltration]
    apply factors_finset_sup (Finset.Icc p n)
      (fun i ↦ K.ιTotalOrZero (ComplexShape.up ℤ)
        (n - i) i n) _ Q
    intro i hi
    have hpi : p ≤ i := (Finset.mem_Icc.mp hi).1
    have hin : i ≤ n := (Finset.mem_Icc.mp hi).2
    rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) (n - i) i n (by
      change (n - i) + i = n
      omega), total_d, CategoryTheory.Preadditive.comp_add, ι_D₁, ι_D₂]
    rw [K.d₁_eq' (ComplexShape.up ℤ) (show
        (ComplexShape.up ℤ).Rel (n - i) ((n - i) + 1) by rfl),
      K.d₂_eq' (ComplexShape.up ℤ) (n - i) (show
        (ComplexShape.up ℤ).Rel i (i + 1) by rfl)]
    apply Subobject.factors_add
    · apply factors_zsmul
      apply Subobject.factors_of_factors_right
      apply factors_image
      dsimp [Q, secondFiltration]
      have heq : (n + 1) - i = (n - i) + 1 := by omega
      rw [← heq]
      exact Finset.le_sup (s := Finset.Icc p (n + 1))
        (f := fun k ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ)
          ((n + 1) - k) k (n + 1)))
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    · apply factors_zsmul
      apply Subobject.factors_of_factors_right
      apply factors_image
      dsimp [Q, secondFiltration]
      have heq : (n + 1) - (i + 1) = n - i := by omega
      rw [← heq]
      exact Finset.le_sup (s := Finset.Icc p (n + 1))
        (f := fun k ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ)
          ((n + 1) - k) k (n + 1)))
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  exact ⟨Q.factorThru _ hQ, Subobject.factorThru_arrow _ _ _⟩

/-- The second filtration starts at the whole total object.
Source: blueprint degreewise bounds (blueprint: def-sp-double-complex-total).
Proof: first-quadrant vanishing leaves only the summands indexed by [0,n].
Their inclusions jointly generate the diagonal coproduct, so their image sum
is top. For n<0 both the diagonal and the empty image sum are zero. -/
theorem secondFiltration_zero (n : ℤ) : (K.secondFiltration n).step 0 = ⊤ := by
  apply K.eq_top_of_total_inclusions n
  intro i j hij
  by_cases hi : 0 ≤ i
  · by_cases hj : 0 ≤ j
    · have hm : j ∈ Finset.Icc (0 : ℤ) n := Finset.mem_Icc.mpr ⟨hj, by omega⟩
      have hsub : n - j = i := by omega
      have hι := K.ιTotalOrZero_eq (ComplexShape.up ℤ) i j n hij
      have hh := Finset.le_sup (f := fun k ↦ imageSubobject
        (K.ιTotalOrZero (ComplexShape.up ℤ) (n - k) k n)) hm
      rw [hsub, hι] at hh
      exact hh
    · rw [(hK i j (Or.inr (by omega))).eq_zero_of_src
        (K.ιTotal (ComplexShape.up ℤ) i j n hij)]
      simp
  · rw [(hK i j (Or.inl (by omega))).eq_zero_of_src
      (K.ιTotal (ComplexShape.up ℤ) i j n hij)]
    simp

/-- The second filtration vanishes past the diagonal.
Source: blueprint degreewise bounds (blueprint: def-sp-double-complex-total).
Proof: [n+1,n] is empty, so its finite supremum is bottom. -/
theorem secondFiltration_finite (n : ℤ) :
    (K.secondFiltration n).step (n + 1) = ⊥ := by
  have _ := hK
  simp [secondFiltration]

/-- The canonical summand maps identify the second graded pieces and their differential.
Source: blueprint graded-piece clause (blueprint: def-sp-double-complex-total).
Proof: lift the diagonal inclusion uniquely through the step's monomorphism.
The next step is the sum of the other summands, so projecting this lift to
its cokernel is an isomorphism. Restrict the total differential to the step;
it preserves the next step as well, hence descends uniquely to the cokernel.
In the quotient the differential raising the filtered index disappears; the
remaining differential is the horizontal map. Its square is zero because the total
differential squares to zero and the quotient maps are epimorphisms.
The equations explicitly fix the isomorphisms by the original total inclusions. -/
theorem secondFiltration_graded (p : ℤ) :
    (let F := fun n : ℤ ↦ K.secondFiltration n
    let π := fun n : ℤ ↦ cokernel.π (Subobject.ofLE ((F n).step (p + 1))
      ((F n).step p) ((F n).antitone_step (by omega)))
    ∃ (a : ∀ n : ℤ, (K.X (n - p)).X p ⟶ ((F n).step p : C))
      (f : ∀ n : ℤ, ((F n).step p : C) ⟶ ((F (n + 1)).step p : C))
      (δ : ∀ n : ℤ, (F n).gradedPiece p ⟶ (F (n + 1)).gradedPiece p),
      (∀ n : ℤ, a n ≫ ((F n).step p).arrow =
        K.ιTotalOrZero (ComplexShape.up ℤ) (n - p) p n) ∧
      (∀ n : ℤ, IsIso (a n ≫ π n)) ∧
      (∀ n : ℤ, f n ≫ ((F (n + 1)).step p).arrow =
        ((F n).step p).arrow ≫ (K.total (ComplexShape.up ℤ)).d n (n + 1)) ∧
      (∀ n : ℤ, π n ≫ δ n = f n ≫ π (n + 1)) ∧
      (∀ n : ℤ, (a n ≫ π n) ≫ δ n =
        (K.d (n - p) ((n + 1) - p)).f p ≫ (a (n + 1) ≫ π (n + 1))) ∧
      (∀ n : ℤ, δ n ≫ δ (n + 1) = 0)) := by
  classical
  dsimp only
  let F := fun n : ℤ ↦ K.secondFiltration n
  let inc := fun n : ℤ ↦ Subobject.ofLE ((F n).step (p + 1)) ((F n).step p)
    ((F n).antitone_step (by omega))
  let π := fun n : ℤ ↦ cokernel.π (inc n)
  let a := fun n : ℤ ↦ (K.second_graded_iso hK p n).choose
  have ha : ∀ n, a n ≫ ((F n).step p).arrow =
      K.ιTotalOrZero (ComplexShape.up ℤ) (n - p) p n :=
    fun n ↦ (K.second_graded_iso hK p n).choose_spec.1
  have hai : ∀ n, IsIso (a n ≫ π n) :=
    fun n ↦ (K.second_graded_iso hK p n).choose_spec.2
  obtain ⟨f, δ, hf, hδ, hsq⟩ := graded_differential
    (K.total (ComplexShape.up ℤ)) F p (K.secondFiltration_subcomplex hK)
  refine ⟨a, f, δ, ha, hai, hf, hδ, ?_, hsq⟩
  intro n
  have ht := K.secondFiltration_inclusion_factors hK (p + 1) (n - p) (p + 1)
    (n + 1) (by omega) le_rfl
  let b := ((F (n + 1)).step (p + 1)).factorThru
    (K.ιTotalOrZero (ComplexShape.up ℤ) (n - p) (p + 1) (n + 1)) ht
  have hb : b ≫ ((F (n + 1)).step (p + 1)).arrow =
      K.ιTotalOrZero (ComplexShape.up ℤ) (n - p) (p + 1) (n + 1) :=
    Subobject.factorThru_arrow _ _ _
  have heq : a n ≫ f n =
      (K.d (n - p) ((n + 1) - p)).f p ≫ a (n + 1) +
      ((n - p).negOnePow • (K.X (n - p)).d p (p + 1)) ≫ b ≫ inc (n + 1) := by
    apply (cancel_mono ((F (n + 1)).step p).arrow).1
    simp only [CategoryTheory.Preadditive.add_comp, Category.assoc, hf, ha,
      reassoc_of% (ha n), Subobject.ofLE_arrow, inc, hb]
    rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) (n - p) p n (by
      change (n - p) + p = n; omega), total_d,
      CategoryTheory.Preadditive.comp_add, ι_D₁, ι_D₂]
    rw [K.d₁_eq' (ComplexShape.up ℤ) (show
        (ComplexShape.up ℤ).Rel (n - p) ((n + 1) - p) by
          change (n - p) + 1 = (n + 1) - p
          omega),
      K.d₂_eq' (ComplexShape.up ℤ) (n - p) (show
        (ComplexShape.up ℤ).Rel p (p + 1) by rfl)]
    change (1 : ℤˣ) • _ + (n - p).negOnePow • _ = _
    simp only [one_smul, CategoryTheory.Linear.units_smul_comp]
  rw [Category.assoc, hδ, ← Category.assoc, heq,
    CategoryTheory.Preadditive.add_comp]
  simp only [inc, Category.assoc, cokernel.condition, CategoryTheory.Limits.comp_zero,
    add_zero]
  rfl

end HomologicalComplex₂
