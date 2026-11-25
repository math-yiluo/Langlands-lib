/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients

/-! # The second filtration for a double complex supported in a half-plane

Source: Stacks Project, Tags 012Z and 0132.
(blueprint: lem-sp-bounded-below-second-filtration).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

/-- A morphism factors through any subobject containing its image. -/
private theorem bounded_factors_image
    {C : Type u} [Category.{v} C] [Abelian C] (X Y : C) (f : X ⟶ Y) (S : Subobject Y)
    (h : imageSubobject f ≤ S) : S.Factors f := by
  apply Subobject.factors_of_le f h
  simpa using imageSubobject_factors_comp_self f (𝟙 X)

/-- Preservation of each generating image implies preservation of their finite supremum. -/
private theorem bounded_factors_finset_sup
    {C : Type u} [Category.{v} C] [Abelian C] {I : Type*} (s : Finset I) {A : I → C}
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
private theorem bounded_factors_zsmul
    {C : Type u} [Category.{v} C] [Abelian C] {X Y : C} (Q : Subobject Y) (a : X ⟶ Y)
    (h : Q.Factors a) (z : ℤ) : Q.Factors (z • a) := by
  rw [← Subobject.factorThru_arrow Q a h, ← CategoryTheory.Preadditive.zsmul_comp]
  exact Subobject.factors_comp_arrow _

/-- The finite image sums are preserved by the total differential without a support assumption.
Source: Stacks Tag 012Z; the calculation in `secondFiltration_subcomplex` of
`WeilConjectures.CategoryTheory.DoubleComplexTotal`,
with its unused first-quadrant hypothesis removed. -/
private theorem bounded_secondFiltration_subcomplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (p n : ℤ) :
    ∃ f : ((K.secondFiltration n).step p : C) ⟶
      ((K.secondFiltration (n + 1)).step p : C),
      f ≫ ((K.secondFiltration (n + 1)).step p).arrow =
        ((K.secondFiltration n).step p).arrow ≫
          (K.total (ComplexShape.up ℤ)).d n (n + 1) := by
  let Q := (K.secondFiltration (n + 1)).step p
  have hQ : Q.Factors (((K.secondFiltration n).step p).arrow ≫
      (K.total (ComplexShape.up ℤ)).d n (n + 1)) := by
    dsimp [secondFiltration]
    apply bounded_factors_finset_sup (Finset.Icc p n)
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
    · apply bounded_factors_zsmul
      apply Subobject.factors_of_factors_right
      apply bounded_factors_image
      dsimp [Q, secondFiltration]
      have heq : (n + 1) - i = (n - i) + 1 := by omega
      rw [← heq]
      exact Finset.le_sup (s := Finset.Icc p (n + 1))
        (f := fun k ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ)
          ((n + 1) - k) k (n + 1)))
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    · apply bounded_factors_zsmul
      apply Subobject.factors_of_factors_right
      apply bounded_factors_image
      dsimp [Q, secondFiltration]
      have heq : (n + 1) - (i + 1) = n - i := by omega
      rw [← heq]
      exact Finset.le_sup (s := Finset.Icc p (n + 1))
        (f := fun k ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ)
          ((n + 1) - k) k (n + 1)))
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  exact ⟨Q.factorThru _ hQ, Subobject.factorThru_arrow _ _ _⟩

/-- The second filtration assembles into subcomplexes and has degreewise bounds.
Source: Stacks Project, Tags 012Z and 0132; blueprint thm-sp-if-e1, proof paragraph 1.
(blueprint: lem-sp-bounded-below-second-filtration).

Proof.
For total degree n the nonzero summands have first index i nonnegative and second
index j at least b, with i+j=n. Thus b ≤ j ≤ n. For each p take the sum of the
images of the diagonal inclusions with j in [p,n]. On a diagonal summand the
horizontal differential preserves j and the vertical differential raises j by one.
Both therefore factor through the next degree's step. Their signed sum does too.
Choose these factorizations through the monomorphisms representing the steps.
The equations for the squares of the differentials and the inclusion morphism
follow by cancellation of those monomorphisms. This gives a subcomplex for each p.
The inclusions of the image sums for p ≤ q give compatible inclusions of the
subcomplexes, hence an antitone family of subobjects of the total complex.
Evaluation of its inclusions has exactly the stated images.
At p=b every nonzero diagonal summand occurs, so the coproduct universal property
makes the image sum top. At p=n+1 the indexing interval is empty, so it is bottom.
If n<b the total itself is zero, and these same equalities still hold. -/
theorem boundedBelow_secondFiltration
    {C : Type u} [Category.{v} C] [Abelian C]
    (J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [J.HasTotal (ComplexShape.up ℤ)]
    (b : ℤ)
    (hzero : ∀ i j : ℤ, i < 0 ∨ j < b → IsZero ((J.X i).X j)) :
    ∃ L : DecreasingFiltration (J.total (ComplexShape.up ℤ)),
      (∀ p n : ℤ, L.complexStep p n = (J.secondFiltration n).step p) ∧
      (∀ n : ℤ, L.complexStep b n = ⊤) ∧
      (∀ n : ℤ, L.complexStep (n + 1) n = ⊥) := by
  classical
  let T := J.total (ComplexShape.up ℤ)
  let S := fun p n : ℤ ↦ (J.secondFiltration n).step p
  let f := fun p n ↦ (J.bounded_secondFiltration_subcomplex p n).choose
  have hf : ∀ p n, f p n ≫ (S p (n + 1)).arrow =
      (S p n).arrow ≫ T.d n (n + 1) :=
    fun p n ↦ (J.bounded_secondFiltration_subcomplex p n).choose_spec
  have hsq : ∀ p n, f p n ≫ f p (n + 1) = 0 := by
    intro p n
    apply (cancel_mono (S p ((n + 1) + 1)).arrow).1
    rw [Category.assoc, hf, ← Category.assoc, hf, Category.assoc,
      T.d_comp_d, comp_zero, zero_comp]
  let U := fun p ↦ CochainComplex.of (fun n ↦ (S p n : C)) (f p) (hsq p)
  let a : ∀ p, U p ⟶ T := fun p ↦ CochainComplex.ofHom
    (fun n ↦ (S p n).arrow) (by intro n; simpa [U] using (hf p n).symm)
  have ha : ∀ p n, (a p).f n = (S p n).arrow := fun _ _ ↦ rfl
  have hmono : ∀ p, Mono (a p) := fun p ↦
    HomologicalComplex.mono_of_mono_f _ (fun n ↦ by dsimp [a]; infer_instance)
  let : ∀ p, Mono (a p) := hmono
  have hanti : Antitone (fun p ↦ Subobject.mk (a p)) := by
    intro p q hpq
    let c : U q ⟶ U p := CochainComplex.ofHom
      (fun n ↦ Subobject.ofLE (S q n) (S p n)
        ((J.secondFiltration n).antitone_step hpq)) (by
          intro n
          apply (cancel_mono (S p (n + 1)).arrow).1
          simp only [U, CochainComplex.of_d, Category.assoc, hf,
            Subobject.ofLE_arrow]
          rw [← Category.assoc, Subobject.ofLE_arrow])
    apply Subobject.mk_le_mk_of_comm c
    ext n
    exact Subobject.ofLE_arrow _
  let L : DecreasingFiltration T := ⟨fun p ↦ Subobject.mk (a p), fun p ↦ hanti (by omega)⟩
  have hL : ∀ p n, L.complexStep p n = S p n := by
    intro p n
    let e := Subobject.underlyingIso (a p)
    have he : (L.step p).arrow = e.hom ≫ a p :=
      (Subobject.underlyingIso_hom_comp_eq_mk (a p)).symm
    dsimp only [DecreasingFiltration.complexStep]
    simp only [he, HomologicalComplex.comp_f]
    have : IsIso (e.hom.f n) := inferInstance
    rw [imageSubobject_iso_comp]
    simp only [ha, imageSubobject_mono, Subobject.mk_arrow]
  refine ⟨L, hL, ?_, ?_⟩
  · intro n
    rw [hL]
    let Q := S b n
    have hQ : ∀ i j : ℤ, ∀ h : i + j = n,
        imageSubobject (J.ιTotal (ComplexShape.up ℤ) i j n h) ≤ Q := by
      intro i j hij
      by_cases hi : 0 ≤ i
      · by_cases hj : b ≤ j
        · have hm : j ∈ Finset.Icc b n := Finset.mem_Icc.mpr ⟨hj, by omega⟩
          have hsub : n - j = i := by omega
          have hι := J.ιTotalOrZero_eq (ComplexShape.up ℤ) i j n hij
          have hh := Finset.le_sup (f := fun k ↦ imageSubobject
            (J.ιTotalOrZero (ComplexShape.up ℤ) (n - k) k n)) hm
          rw [hsub, hι] at hh
          exact hh
        · rw [(hzero i j (Or.inr (by omega))).eq_zero_of_src
            (J.ιTotal (ComplexShape.up ℤ) i j n hij)]
          simp
      · rw [(hzero i j (Or.inl (by omega))).eq_zero_of_src
          (J.ιTotal (ComplexShape.up ℤ) i j n hij)]
        simp
    let r := J.totalDesc (fun i j h ↦
      factorThruImageSubobject (J.ιTotal (ComplexShape.up ℤ) i j n h) ≫
        Subobject.ofLE _ Q (hQ i j h))
    have hr : r ≫ Q.arrow = 𝟙 _ := by
      apply total.hom_ext
      intro i j h
      simp [r]
    have : IsSplitEpi Q.arrow := IsSplitEpi.mk' ⟨r, hr⟩
    have : IsIso Q.arrow := isIso_of_mono_of_isSplitEpi Q.arrow
    exact Subobject.eq_top_of_isIso_arrow Q
  · intro n
    rw [hL]
    simp [S, secondFiltration]

end HomologicalComplex₂
