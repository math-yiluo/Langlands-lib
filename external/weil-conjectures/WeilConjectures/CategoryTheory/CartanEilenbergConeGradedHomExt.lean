/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # Retained summands detect morphisms from the column-tail quotient

Source: Stacks Project, Homology, Tag 012X; column filtration and its graded pieces
(blueprint: lem-sp-cartan-eilenberg-cone-graded-hom-ext).
-/

@[expose] public section

universe uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

/-- Lift a generator through a monic map whose image contains it. -/
private theorem lift_of_image_le
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {X Y Z : A} (j : X ⟶ Y) [Mono j] (a : Z ⟶ Y)
    (ha : imageSubobject a ≤ imageSubobject j) :
    ∃ l : Z ⟶ X, l ≫ j = a := by
  have ha' : imageSubobject a ≤ Subobject.mk j := by
    simpa only [imageSubobject_mono] using ha
  refine ⟨factorThruImageSubobject a ≫ Subobject.ofLE _ _ ha' ≫
    (Subobject.underlyingIso j).hom, ?_⟩
  simp

/-- A lift belonging to the next step is killed by the graded projection. -/
private theorem lift_next_quotient_zero
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {C : CochainComplex A ℤ} (F : DecreasingFiltration C) (p m : ℤ)
    {Z : A} (a : Z ⟶ C.X m)
    (ha : imageSubobject a ≤ F.complexStep (p + 1) m)
    (l : Z ⟶ (F.step p : CochainComplex A ℤ).X m)
    (hl : l ≫ (F.step p).arrow.f m = a) :
    l ≫ (F.complexQuotientπ p (p + 1) (by omega)).f m = 0 := by
  obtain ⟨l', hl'⟩ := lift_of_image_le ((F.step (p + 1)).arrow.f m) a ha
  let f := Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega))
  have hf : f.f m ≫ (F.step p).arrow.f m = (F.step (p + 1)).arrow.f m := by
    exact congrArg (fun k => k.f m) (Subobject.ofLE_arrow (F.antitone_step (by omega : p ≤ p + 1)))
  have he : l = l' ≫ f.f m := by
    apply (cancel_mono ((F.step p).arrow.f m)).1
    simpa only [Category.assoc, hf] using hl.trans hl'.symm
  have hq : f.f m ≫ (F.complexQuotientπ p (p + 1) (by omega)).f m = 0 := by
    exact congrArg (fun k => k.f m) (cokernel.condition f)
  rw [he, Category.assoc, hq, comp_zero]

/-- Maps out of the graded piece agree if they agree on every retained summand lift.
Source: Stacks Project, Homology, Tag 012X; quotient of the column-tail sum.
(blueprint: lem-sp-cartan-eilenberg-cone-graded-hom-ext).

Proof: cancel the epic evaluated cokernel projection from step p. Its two
composites agree on the K generator and on every diagonal generator of the
finite image supremum describing that step. A diagonal index s>p factors
through step p+1 and is killed by the cokernel projection. Index s=p has
nonnegative resolution degree m-p, so the first hypothesis applies after
extendXIso. Columns s<p do not occur. If p<b the index-p term does not occur
in the generating interval.
For the K generator, when p<=m it belongs to step p+1 and is killed there;
when m+1=p use the second hypothesis after the index identification. These
are the only possibilities under p-1<=m. Equality on these generators
implies equality on their image supremum: take the equalizer of the two
composites, compose its monic inclusion with the step inclusion, and use
the image-supremum formula to show that this subobject contains step p.
The equalizer inclusion is consequently split epic and monic, forcing the
two composites to agree. Monicity of the step inclusion makes all lifts
unique, so the statement can test every lift. Empty intervals and zero
retained terms require no separate nonemptiness assumption. -/
theorem cartanEilenberg_cone_graded_hom_ext
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (b : ℤ)
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (F : DecreasingFiltration (CochainComplex.mappingCone aug))
    (hF : ∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl aug).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Icc (max b p) n).sup (fun s ↦ imageSubobject
          ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
            (ComplexShape.up ℤ) (n - s) s n ≫
              (CochainComplex.mappingCone.inr aug).f n)))
    (p m : ℤ) (hm : p - 1 ≤ m)
    (T : A) (g h : (F.gradedPiece p).X m ⟶ T)
    (hI : ∀ (r : ℕ) (hr : (r : ℤ) + p = m)
      (l : (I.X p).X r ⟶ (F.step p : CochainComplex A ℤ).X m),
      l ≫ (F.step p).arrow.f m =
        (HomologicalComplex.extendXIso
          (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p))
          ComplexShape.embeddingUpNat (i := r) (i' := m - p)
          (by change (r : ℤ) = m - p; omega)).inv ≫
        (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
          (ComplexShape.up ℤ) (m - p) p m (by change (m - p) + p = m; omega) ≫
        (CochainComplex.mappingCone.inr aug).f m →
        l ≫ (F.complexQuotientπ p (p + 1) (by omega)).f m ≫ g =
          l ≫ (F.complexQuotientπ p (p + 1) (by omega)).f m ≫ h)
    (hK : ∀ (hk : m + 1 = p)
      (l : K.X p ⟶ (F.step p : CochainComplex A ℤ).X m),
      l ≫ (F.step p).arrow.f m =
        (K.XIsoOfEq hk.symm).hom ≫
        (CochainComplex.mappingCone.inl aug).v (m + 1) m (by omega) →
        l ≫ (F.complexQuotientπ p (p + 1) (by omega)).f m ≫ g =
          l ≫ (F.complexQuotientπ p (p + 1) (by omega)).f m ≫ h) :
    g = h := by
  classical
  let j := (F.step p).arrow.f m
  let q := (F.complexQuotientπ p (p + 1) (by omega)).f m
  have : Epi q := by dsimp [q, DecreasingFiltration.complexQuotientπ]; infer_instance
  apply (cancel_epi q).1
  let e := equalizer.ι (q ≫ g) (q ≫ h) ≫ j
  have hj : imageSubobject j ≤ Subobject.mk e := by
    change F.complexStep p m ≤ Subobject.mk e
    rw [hF p m]
    apply sup_le
    · rw [ite_eq_left (by omega : p ≤ m + 1)]
      let a := (CochainComplex.mappingCone.inl aug).v (m + 1) m (by omega)
      have ha : imageSubobject a ≤ F.complexStep p m := by
        rw [hF p m, ite_eq_left (by omega : p ≤ m + 1)]
        exact le_sup_left
      obtain ⟨l, hl⟩ := lift_of_image_le j a ha
      have hw : l ≫ q ≫ g = l ≫ q ≫ h := by
        by_cases hp : p ≤ m
        · have han : imageSubobject a ≤ F.complexStep (p + 1) m := by
            rw [hF (p + 1) m, ite_eq_left (by omega : p + 1 ≤ m + 1)]
            exact le_sup_left
          have hz := lift_next_quotient_zero F p m a han l hl
          change l ≫ q = 0 at hz
          simp only [← Category.assoc, hz, zero_comp]
        · have hk : m + 1 = p := by omega
          let t := (K.XIsoOfEq hk.symm).hom
          have ht : (t ≫ l) ≫ j = t ≫ a := by rw [Category.assoc, hl]
          have w := hK hk (t ≫ l) ht
          apply (cancel_epi t).1
          simpa only [Category.assoc] using w
      exact imageSubobject_le_mk e a (equalizer.lift l (by
        simpa only [Category.assoc] using hw)) (by simp [e, hl])
    · apply Finset.sup_le
      intro s hs
      have hsm : s ≤ m := (Finset.mem_Icc.mp hs).2
      have hps : p ≤ s := le_trans (le_max_right b p) (Finset.mem_Icc.mp hs).1
      let a :=
        (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
          (ComplexShape.up ℤ) (m - s) s m ≫
          (CochainComplex.mappingCone.inr aug).f m
      have ha : imageSubobject a ≤ F.complexStep p m := by
        rw [hF p m]
        apply le_sup_of_le_right
        dsimp only [a]
        exact Finset.le_sup (f := fun t ↦ imageSubobject
          ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
            (ComplexShape.up ℤ) (m - t) t m ≫
              (CochainComplex.mappingCone.inr aug).f m)) hs
      obtain ⟨l, hl⟩ := lift_of_image_le j a ha
      have hw : l ≫ q ≫ g = l ≫ q ≫ h := by
        by_cases hsp : s = p
        · subst s
          let r := (m - p).toNat
          have hr : (r : ℤ) + p = m := by dsimp [r]; rw [Int.toNat_of_nonneg (by omega)]; omega
          let t := (HomologicalComplex.extendXIso
            (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p))
            ComplexShape.embeddingUpNat (i := r) (i' := m - p)
            (by change (r : ℤ) = m - p; omega)).inv
          have ht : (t ≫ l) ≫ j = t ≫
              (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
                (ComplexShape.up ℤ) (m - p) p m (by change (m - p) + p = m; omega) ≫
              (CochainComplex.mappingCone.inr aug).f m := by
            rw [Category.assoc, hl]
            dsimp [a]
            simp only [HomologicalComplex₂.ιTotalOrZero_eq
              (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip)
              (ComplexShape.up ℤ) (m - p) p m (by change (m - p) + p = m; omega)]
          apply (cancel_epi t).1
          simpa only [Category.assoc] using hI r hr (t ≫ l) ht
        · have hs' : s ∈ Finset.Icc (max b (p + 1)) m := by
            have := Finset.mem_Icc.mp hs
            simp only [Finset.mem_Icc, max_le_iff] at this ⊢
            omega
          have han : imageSubobject a ≤ F.complexStep (p + 1) m := by
            rw [hF (p + 1) m]
            apply le_sup_of_le_right
            dsimp only [a]
            exact Finset.le_sup (f := fun t ↦ imageSubobject
              ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
                (ComplexShape.up ℤ) (m - t) t m ≫
                  (CochainComplex.mappingCone.inr aug).f m)) hs'
          have hz := lift_next_quotient_zero F p m a han l hl
          change l ≫ q = 0 at hz
          simp only [← Category.assoc, hz, zero_comp]
      exact imageSubobject_le_mk e a (equalizer.lift l (by
        simpa only [Category.assoc] using hw)) (by simp [e, hl])
  have hj' : Subobject.mk j ≤ Subobject.mk e := by
    simpa only [imageSubobject_mono] using hj
  let r := (Subobject.underlyingIso j).inv ≫ Subobject.ofLE _ _ hj' ≫
    (Subobject.underlyingIso e).hom
  have hr : r ≫ equalizer.ι (q ≫ g) (q ≫ h) = 𝟙 _ := by
    apply (cancel_mono j).1
    rw [Category.assoc]
    change r ≫ e = 𝟙 _ ≫ j
    simp [r]
  have : IsSplitEpi (equalizer.ι (q ≫ g) (q ≫ h)) := IsSplitEpi.mk' ⟨r, hr⟩
  exact (cancel_epi (equalizer.ι (q ≫ g) (q ≫ h))).1 (equalizer.condition _ _)

end CategoryTheory.Functor
