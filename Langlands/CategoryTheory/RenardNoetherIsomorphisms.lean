import Langlands.CategoryTheory.RenardNoetherIsomorphismStatements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Proof of Renard's Noether isomorphisms and complementary-subobject sum

Proof of `Langlands.Renard.NoetherIsomorphismsStatement` (Renard 2026,
Appendix A.VI.2(9)) in an arbitrary abelian category, on actual subobjects, their
chosen inclusions and actual cokernels. The route uses exactness of short
complexes and the lattice structure of `Subobject X` instead of the 3-by-3 lemma.
-/

namespace Langlands.Renard

open CategoryTheory CategoryTheory.Limits

universe u v

section Helpers

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A morphism killed by the cokernel projection of a monomorphism factors
through that monomorphism. -/
theorem exists_lift_of_comp_cokernel_π {P Y W : C} (m : P ⟶ Y) [Mono m] (g : W ⟶ Y)
    (hg : g ≫ cokernel.π m = 0) : ∃ l : W ⟶ P, l ≫ m = g := by
  have hS := ShortComplex.exact_of_g_is_cokernel
    (S := ShortComplex.mk m (cokernel.π m) (cokernel.condition m)) (cokernelIsCokernel m)
  exact ⟨hS.lift g hg, hS.lift_f g hg⟩

/-- If the monomorphism `i` is a kernel of `f`, then the morphism
`cokernel i ⟶ Z` induced by `f` is a monomorphism. -/
theorem mono_cokernel_desc_of_factors {K Y Z : C} (i : K ⟶ Y) [Mono i] (f : Y ⟶ Z)
    (w : i ≫ f = 0)
    (hf : ∀ {W : C} (g : W ⟶ Y), g ≫ f = 0 → ∃ l : W ⟶ K, l ≫ i = g) :
    Mono (cokernel.desc i f w) := by
  have hi : IsLimit (KernelFork.ofι i w) :=
    KernelFork.IsLimit.ofι' i w (fun g hg => ⟨(hf g hg).choose, (hf g hg).choose_spec⟩)
  exact (ShortComplex.exact_of_f_is_kernel (S := ShortComplex.mk i f w) hi).mono_cokernelDesc

/-- A morphism out of `A ⊔ B` that vanishes on both `A` and `B` is zero. -/
theorem eq_zero_of_ofLE_sup_comp {X W : C} {A B : Subobject X}
    (k : ((A ⊔ B : Subobject X) : C) ⟶ W)
    (ha : Subobject.ofLE A (A ⊔ B) le_sup_left ≫ k = 0)
    (hb : Subobject.ofLE B (A ⊔ B) le_sup_right ≫ k = 0) : k = 0 := by
  let m := kernel.ι k ≫ (A ⊔ B).arrow
  have hA : A ≤ Subobject.mk m :=
    Subobject.le_mk_of_comm (kernel.lift k _ ha) (by simp [m])
  have hB : B ≤ Subobject.mk m :=
    Subobject.le_mk_of_comm (kernel.lift k _ hb) (by simp [m])
  have hle : A ⊔ B ≤ Subobject.mk m := sup_le hA hB
  have hs : Subobject.ofLEMk _ m hle ≫ kernel.ι k = 𝟙 _ := by
    rw [← cancel_mono (A ⊔ B).arrow]
    simp [m]
  calc k = (Subobject.ofLEMk _ m hle ≫ kernel.ι k) ≫ k := by rw [hs, Category.id_comp]
    _ = 0 := by simp

end Helpers

/-- Renard A.VI.2(9)(i). -/
theorem nestedQuotientIso (C : Type u) [Category.{v} C] [Abelian C] :
    NestedQuotientIsoStatement C := by
  intro X A B h j
  have w : Subobject.ofLE A B h ≫ B.arrow ≫ cokernel.π A.arrow = 0 := by simp
  have hj : j = cokernel.desc (Subobject.ofLE A B h) (B.arrow ≫ cokernel.π A.arrow) w := rfl
  have hπj : cokernel.π (Subobject.ofLE A B h) ≫ j = B.arrow ≫ cokernel.π A.arrow := by
    rw [hj, cokernel.π_desc]
  refine ⟨?_, ?_⟩
  · rw [hj]
    refine mono_cokernel_desc_of_factors _ _ w (fun {W} g hg => ?_)
    obtain ⟨l, hl⟩ := exists_lift_of_comp_cokernel_π A.arrow (g ≫ B.arrow)
      (by simpa using hg)
    refine ⟨l, ?_⟩
    rw [← cancel_mono B.arrow]
    simpa using hl
  · have wq : A.arrow ≫ cokernel.π B.arrow = 0 := by
      rw [← Subobject.ofLE_arrow h, Category.assoc, cokernel.condition, comp_zero]
    let q := cokernel.desc A.arrow (cokernel.π B.arrow) wq
    have hq : cokernel.π A.arrow ≫ q = cokernel.π B.arrow := cokernel.π_desc _ _ _
    have hjq : j ≫ q = 0 := by
      rw [← cancel_epi (cokernel.π (Subobject.ofLE A B h)), reassoc_of% hπj, hq,
        cokernel.condition, comp_zero]
    have wr : B.arrow ≫ cokernel.π A.arrow ≫ cokernel.π j = 0 := by
      rw [← Category.assoc, ← hπj, Category.assoc, cokernel.condition, comp_zero]
    let r := cokernel.desc B.arrow (cokernel.π A.arrow ≫ cokernel.π j) wr
    have hr : cokernel.π B.arrow ≫ r = cokernel.π A.arrow ≫ cokernel.π j :=
      cokernel.π_desc _ _ _
    refine ⟨{ hom := cokernel.desc j q hjq, inv := r, hom_inv_id := ?_, inv_hom_id := ?_ }, ?_⟩
    · rw [← cancel_epi (cokernel.π j), ← cancel_epi (cokernel.π A.arrow)]
      simp only [cokernel.π_desc_assoc, Category.comp_id]
      rw [reassoc_of% hq, hr]
    · rw [← cancel_epi (cokernel.π B.arrow), reassoc_of% hr, Category.comp_id]
      simp only [cokernel.π_desc]
      exact hq
    · simp only [cokernel.π_desc]
      exact hq

/-- Renard A.VI.2(9)(ii). -/
theorem secondIso (C : Type u) [Category.{v} C] [Abelian C] : SecondIsoStatement C := by
  intro X A B
  have hib : Subobject.ofLE (A ⊓ B) B inf_le_right ≫ Subobject.ofLE B (A ⊔ B) le_sup_right =
      Subobject.ofLE (A ⊓ B) A inf_le_left ≫ Subobject.ofLE A (A ⊔ B) le_sup_left := by
    rw [← cancel_mono (A ⊔ B).arrow]
    simp
  have w : Subobject.ofLE (A ⊓ B) B inf_le_right ≫ Subobject.ofLE B (A ⊔ B) le_sup_right ≫
      cokernel.π (Subobject.ofLE A (A ⊔ B) le_sup_left) = 0 := by
    rw [reassoc_of% hib, cokernel.condition, comp_zero]
  let φ := cokernel.desc (Subobject.ofLE (A ⊓ B) B inf_le_right)
    (Subobject.ofLE B (A ⊔ B) le_sup_right ≫ cokernel.π (Subobject.ofLE A (A ⊔ B) le_sup_left)) w
  have hφ : cokernel.π (Subobject.ofLE (A ⊓ B) B inf_le_right) ≫ φ =
      Subobject.ofLE B (A ⊔ B) le_sup_right ≫
        cokernel.π (Subobject.ofLE A (A ⊔ B) le_sup_left) :=
    cokernel.π_desc _ _ _
  have hmono : Mono φ := by
    refine mono_cokernel_desc_of_factors _ _ w (fun {W} g hg => ?_)
    obtain ⟨l, hl⟩ := exists_lift_of_comp_cokernel_π (Subobject.ofLE A (A ⊔ B) le_sup_left)
      (g ≫ Subobject.ofLE B (A ⊔ B) le_sup_right) (by simpa using hg)
    have hlA : l ≫ A.arrow = g ≫ B.arrow := by
      have := congrArg (· ≫ (A ⊔ B).arrow) hl
      simpa using this
    have hfac : (A ⊓ B).Factors (g ≫ B.arrow) := by
      rw [Subobject.inf_factors]
      refine ⟨?_, Subobject.factors_comp_arrow g⟩
      rw [← hlA]
      exact Subobject.factors_comp_arrow l
    refine ⟨(A ⊓ B).factorThru _ hfac, ?_⟩
    rw [← cancel_mono B.arrow]
    simp
  have hepi : Epi φ := by
    have : Epi (Subobject.ofLE B (A ⊔ B) le_sup_right ≫
        cokernel.π (Subobject.ofLE A (A ⊔ B) le_sup_left)) := by
      refine Preadditive.epi_of_cancel_zero _ (fun {R} g hg => ?_)
      have hk : cokernel.π (Subobject.ofLE A (A ⊔ B) le_sup_left) ≫ g = 0 :=
        eq_zero_of_ofLE_sup_comp _ (by simp) (by simpa using hg)
      rw [← cancel_epi (cokernel.π (Subobject.ofLE A (A ⊔ B) le_sup_left)), hk, comp_zero]
    rw [← hφ] at this
    exact epi_of_epi (cokernel.π (Subobject.ofLE (A ⊓ B) B inf_le_right)) φ
  have := isIso_of_mono_of_epi φ
  exact ⟨asIso φ, by simpa using hφ⟩

/-- Renard A.VI.2(9), final assertion: complementary subobjects give a direct sum. -/
theorem complementarySubobjectsSum (C : Type u) [Category.{v} C] [Abelian C] :
    ComplementarySubobjectsSumStatement C := by
  intro X A B hinf hsup
  have hmono : Mono (biprod.desc A.arrow B.arrow) := by
    refine Preadditive.mono_of_cancel_zero _ (fun {W} g hg => ?_)
    have hsum : (g ≫ biprod.fst) ≫ A.arrow + (g ≫ biprod.snd) ≫ B.arrow = 0 := by
      simpa [biprod.desc_eq, Preadditive.comp_add] using hg
    have hab : (g ≫ biprod.fst) ≫ A.arrow = (-(g ≫ biprod.snd)) ≫ B.arrow := by
      rw [Preadditive.neg_comp]
      exact eq_neg_of_add_eq_zero_left hsum
    have hfac : (A ⊓ B).Factors ((g ≫ biprod.fst) ≫ A.arrow) := by
      rw [Subobject.inf_factors]
      refine ⟨Subobject.factors_comp_arrow _, ?_⟩
      rw [hab]
      exact Subobject.factors_comp_arrow _
    rw [hinf, Subobject.bot_factors_iff_zero] at hfac
    have h1 : g ≫ biprod.fst = 0 := by
      rw [← cancel_mono A.arrow, hfac, zero_comp]
    have h2 : g ≫ biprod.snd = 0 := by
      rw [← cancel_mono B.arrow, zero_comp]
      rw [hfac, zero_add] at hsum
      exact hsum
    exact biprod.hom_ext _ _ (by simpa using h1) (by simpa using h2)
  have hepi : Epi (biprod.desc A.arrow B.arrow) := by
    refine Preadditive.epi_of_cancel_zero _ (fun {R} g hg => ?_)
    have ha : A.arrow ≫ g = 0 := by
      simpa using congrArg (biprod.inl ≫ ·) hg
    have hb : B.arrow ≫ g = 0 := by
      simpa using congrArg (biprod.inr ≫ ·) hg
    have : IsIso (A ⊔ B).arrow := (Subobject.isIso_arrow_iff_eq_top _).mpr hsup
    have hk : (A ⊔ B).arrow ≫ g = 0 :=
      eq_zero_of_ofLE_sup_comp _ (by simpa using ha) (by simpa using hb)
    rw [← cancel_epi (A ⊔ B).arrow, hk, comp_zero]
  have := isIso_of_mono_of_epi (biprod.desc A.arrow B.arrow)
  have hc : coprod.desc A.arrow B.arrow =
      (biprod.isoCoprod (A : C) (B : C)).inv ≫ biprod.desc A.arrow B.arrow := by
    ext <;> simp
  rw [hc]
  infer_instance

/-- Renard A.VI.2(9): the aggregate of the two Noether isomorphisms and the
complementary-subobject direct sum, in every abelian category. -/
theorem noetherIsomorphisms (C : Type u) [Category.{v} C] [Abelian C] :
    NoetherIsomorphismsStatement C :=
  ⟨nestedQuotientIso C, secondIso C, complementarySubobjectsSum C⟩

end Langlands.Renard
