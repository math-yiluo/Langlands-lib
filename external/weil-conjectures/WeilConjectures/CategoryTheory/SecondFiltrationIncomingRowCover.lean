/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients

/-! # Incoming graded differential of an extended row

Source: Stacks Project, Homology, Tag 0130, clause 2.
(blueprint: lem-sp-second-filtration-incoming-row-cover).
-/

@[expose] public section

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

private theorem finite_image_hom_ext
    {C : Type*} [Category C] [Abelian C] {S V Y : C}
    {D : Type*} (t : Finset D) {X : D → C} (f : ∀ i, X i ⟶ V)
    (m : S ⟶ V) [Mono m]
    (hm : imageSubobject m = t.sup (fun i ↦ imageSubobject (f i)))
    (a : ∀ i, ∀ _ : i ∈ t, X i ⟶ S)
    (ha : ∀ i hi, a i hi ≫ m = f i)
    (g h : S ⟶ Y) (w : ∀ i hi, a i hi ≫ g = a i hi ≫ h) : g = h := by
  let e := equalizer.ι g h ≫ m
  have hs : Subobject.mk m ≤ Subobject.mk e := by
    rw [← imageSubobject_mono m, hm]
    apply Finset.sup_le
    intro i hi
    apply imageSubobject_le_mk e (f i) (equalizer.lift (a i hi) (w i hi))
    simp [e, ha]
  let r := (Subobject.underlyingIso m).inv ≫
    Subobject.ofLE (Subobject.mk m) (Subobject.mk e) hs ≫
    (Subobject.underlyingIso e).hom
  have hr : r ≫ equalizer.ι g h = 𝟙 _ := by
    apply (cancel_mono m).1
    rw [Category.assoc, Category.id_comp]
    change r ≫ e = m
    simp [r]
  have : IsSplitEpi (equalizer.ι g h) := IsSplitEpi.mk' ⟨r, hr⟩
  exact (cancel_epi (equalizer.ι g h)).1 (equalizer.condition g h)

private theorem diagonal_step_lift
    {C : Type*} [Category C] [Abelian C]
    (J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [J.HasTotal (ComplexShape.up ℤ)]
    (L : DecreasingFiltration (J.total (ComplexShape.up ℤ)))
    (hL : ∀ p n, L.complexStep p n = (J.secondFiltration n).step p)
    (p i j n : ℤ) (hij : i + j = n) (hp : p ≤ j) (hj : j ≤ n) :
    ∃ a : (J.X i).X j ⟶ (L.step p : CochainComplex C ℤ).X n,
      a ≫ (L.step p).arrow.f n =
        J.ιTotal (ComplexShape.up ℤ) i j n hij := by
  let m := (L.step p).arrow.f n
  have : Mono m := by
    change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map (L.step p).arrow)
    infer_instance
  have hi : imageSubobject (J.ιTotal (ComplexShape.up ℤ) i j n hij) ≤
      imageSubobject m := by
    change imageSubobject _ ≤ L.complexStep p n
    rw [hL]
    dsimp only [HomologicalComplex₂.secondFiltration]
    have hh := Finset.le_sup (f := fun k ↦ imageSubobject
      (J.ιTotalOrZero (ComplexShape.up ℤ) (n - k) k n))
      (Finset.mem_Icc.mpr ⟨hp, hj⟩)
    have hn : n - j = i := by omega
    rw [hn, J.ιTotalOrZero_eq (ComplexShape.up ℤ) i j n hij] at hh
    exact hh
  have hf : (Subobject.mk m).Factors (J.ιTotal (ComplexShape.up ℤ) i j n hij) := by
    rw [← imageSubobject_mono m]
    apply Subobject.factors_of_le _ hi
    simpa using imageSubobject_factors_comp_self
      (J.ιTotal (ComplexShape.up ℤ) i j n hij) (𝟙 _)
  exact (Subobject.mk_factors_iff m _).mp hf

private theorem diagonal_step_graded_epi
    {C : Type*} [Category C] [Abelian C]
    (J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [J.HasTotal (ComplexShape.up ℤ)]
    (L : DecreasingFiltration (J.total (ComplexShape.up ℤ)))
    (hL : ∀ p n, L.complexStep p n = (J.secondFiltration n).step p)
    (i s n : ℤ) (hij : i + s = n)
    (b : (J.X i).X s ⟶ (L.step s : CochainComplex C ℤ).X n)
    (hb : b ≫ (L.step s).arrow.f n =
      J.ιTotal (ComplexShape.up ℤ) i s n hij) :
    Epi (b ≫ (L.complexQuotientπ s (s + 1) (by omega)).f n) := by
  have hi : i = n - s := by omega
  subst i
  classical
  let m := (L.step s).arrow.f n
  let q := (L.complexQuotientπ s (s + 1) (by omega)).f n
  let inc := (Subobject.ofLE (L.step (s + 1)) (L.step s)
    (L.antitone_step (by omega))).f n
  have : Mono m := by
    change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map (L.step s).arrow)
    infer_instance
  have : Epi q := by
    change Epi ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map
      (cokernel.π (Subobject.ofLE (L.step (s + 1)) (L.step s)
        (L.antitone_step (by omega)))))
    infer_instance
  have hinc : inc ≫ m = (L.step (s + 1)).arrow.f n := by
    exact congrArg (fun f ↦ f.f n)
      (Subobject.ofLE_arrow (L.antitone_step (show s ≤ s + 1 by omega)))
  have hzero : inc ≫ q = 0 := by
    exact congrArg (fun f ↦ f.f n) (cokernel.condition
      (Subobject.ofLE (L.step (s + 1)) (L.step s) (L.antitone_step (by omega))))
  let f := fun i : ℤ ↦ J.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n
  have lifts : ∀ i, ∀ _ : i ∈ Finset.Icc s n,
      ∃ l : (J.X (n - i)).X i ⟶ (L.step s : CochainComplex C ℤ).X n,
        l ≫ m = f i := by
    intro i hi
    obtain ⟨l, hl⟩ := diagonal_step_lift J L hL s (n - i) i n (by omega)
      (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
    refine ⟨l, ?_⟩
    simpa only [f, J.ιTotalOrZero_eq (ComplexShape.up ℤ) (n - i) i n
      (by change (n - i) + i = n; omega)] using hl
  choose l hl using lifts
  constructor
  intro Y g h he
  apply (cancel_epi q).1
  apply finite_image_hom_ext (Finset.Icc s n) f m (hL s n) l hl
  intro i hi
  by_cases his : i = s
  · subst i
    have hls : l s hi = b := by
      apply (cancel_mono m).1
      rw [hl, hb]
      exact J.ιTotalOrZero_eq _ _ _ _ _
    simpa only [hls, Category.assoc] using he
  · have hit : s + 1 ≤ i := by have := (Finset.mem_Icc.mp hi).1; omega
    obtain ⟨t, ht⟩ := diagonal_step_lift J L hL (s + 1) (n - i) i n
      (by omega) hit (Finset.mem_Icc.mp hi).2
    have hlt : l i hi = t ≫ inc := by
      apply (cancel_mono m).1
      rw [hl, Category.assoc, hinc, ht]
      exact J.ιTotalOrZero_eq _ _ _ _ _
    simp only [hlt, Category.assoc, reassoc_of% hzero, zero_comp]

set_option backward.isDefEq.respectTransparency false in
/-- In positive resolution degree, the incoming graded differential is covered
by the incoming row term.
Source: Stacks Project, Tag 0130, clause 2, the second-filtration differential.
(blueprint: lem-sp-second-filtration-incoming-row-cover).

Proof. Put n = s+r and project the diagonal coproduct in degree n-1 onto
its summand with second coordinate s. This projection kills the next filtration
step. For r>0, lift the diagonal inclusion of the extended row term r-1
through the step s and then take its graded class. The projection descends to
the quotient and is inverse to this class: on the generating summand s the
composite is identity, and the other summands factor through step s+1 and
vanish. The interval is [s,n-1], so negative s is allowed. Composing with the
extension isomorphism identifies this source with row degree prev r = r-1.
The resulting e is an isomorphism, hence epic. Compute the total differential
on this inclusion. Its resolution component is the row differential and its
component raising s factors through step s+1. The latter vanishes after the
graded projection. Monicity of the step inclusion identifies the target lift
with the prescribed a, proving the displayed square.
A zero row is handled by the same projection/lift calculation, using the
unique morphisms between zero objects. No sign condition on s is used.
This statement concerns terms and differentials only, with no cycles,
filtered boundaries, or homology quotient.
-/
theorem secondFiltration_incoming_row_cover
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    (F : A ⥤ B) [F.Additive]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (L : DecreasingFiltration
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).total
        (ComplexShape.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n =
      ((((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).secondFiltration n).step
        p)
    (r : ℕ) (s : ℤ) (hr : 0 < r)
    (a : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).X r ⟶
      (L.step s : CochainComplex B ℤ).X (s + (r : ℤ)))
    (ha : a ≫ (L.step s).arrow.f (s + (r : ℤ)) =
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).extendXIso
        ComplexShape.embeddingUpNat (by rfl)).inv ≫
        (((CartanEilenbergPresentation.mappedFunctor F).obj I).flip).ιTotal
          (ComplexShape.up ℤ) (r : ℤ) s (s + (r : ℤ)) (by
            change (r : ℤ) + s = s + (r : ℤ)
            omega))) :
    ∃ e : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).X
        ((ComplexShape.up ℕ).prev r) ⟶ (L.gradedPiece s).X (s + (r : ℤ) - 1),
      Epi e ∧ e ≫ (L.gradedPiece s).d (s + (r : ℤ) - 1) (s + (r : ℤ)) =
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)).d
          ((ComplexShape.up ℕ).prev r) r ≫ a ≫
          (L.complexQuotientπ s (s + 1) (by omega)).f (s + (r : ℤ)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simp only [Nat.succ_eq_add_one]
  rw [CochainComplex.prev_nat_succ]
  let J := ((CartanEilenbergPresentation.mappedFunctor F).obj I).flip
  let R := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s)
  let n₀ := s + (k : ℤ)
  let n := s + ((k + 1 : ℕ) : ℤ)
  have hn : s + ((k + 1 : ℕ) : ℤ) - 1 = n₀ := by dsimp [n₀]; omega
  rw [hn]
  obtain ⟨b₀, hb₀⟩ := diagonal_step_lift J L hL s (k : ℤ) s n₀
    (by dsimp [n₀]; omega) le_rfl (by dsimp [n₀]; omega)
  let ε := R.extendXIso ComplexShape.embeddingUpNat (by rfl :
    ComplexShape.embeddingUpNat.f k = (k : ℤ))
  let b : R.X k ⟶ (L.step s : CochainComplex B ℤ).X n₀ := ε.inv ≫ b₀
  let q₀ := (L.complexQuotientπ s (s + 1) (by omega)).f n₀
  let q := (L.complexQuotientπ s (s + 1) (by omega)).f n
  refine ⟨b ≫ q₀, ?_, ?_⟩
  · have : Epi (b₀ ≫ q₀) := diagonal_step_graded_epi J L hL (k : ℤ) s n₀
      (by dsimp [n₀]; omega) b₀ hb₀
    dsimp only [b]
    rw [Category.assoc]
    infer_instance
  · change (b ≫ q₀) ≫ (L.complexQuotient s (s + 1) (by omega)).d n₀ n =
      R.d k (k + 1) ≫ a ≫ q
    dsimp only [q₀]
    rw [Category.assoc, (L.complexQuotientπ s (s + 1) (by omega)).comm]
    change b ≫ (L.step s : CochainComplex B ℤ).d n₀ n ≫ q = R.d k (k + 1) ≫ a ≫ q
    obtain ⟨t, ht⟩ := diagonal_step_lift J L hL (s + 1) (k : ℤ) (s + 1) n
      (by dsimp [n]; omega) le_rfl (by dsimp [n]; omega)
    let inc := (Subobject.ofLE (L.step (s + 1)) (L.step s)
      (L.antitone_step (by omega))).f n
    let m := (L.step s).arrow.f n
    have : Mono m := by
      change Mono ((HomologicalComplex.eval B (ComplexShape.up ℤ) n).map (L.step s).arrow)
      infer_instance
    have hinc : inc ≫ m = (L.step (s + 1)).arrow.f n :=
      congrArg (fun f ↦ f.f n)
        (Subobject.ofLE_arrow (L.antitone_step (show s ≤ s + 1 by omega)))
    have hzero : inc ≫ q = 0 :=
      congrArg (fun f ↦ f.f n) (cokernel.condition
        (Subobject.ofLE (L.step (s + 1)) (L.step s) (L.antitone_step (by omega))))
    have htotal : ε.inv ≫ J.ιTotal (ComplexShape.up ℤ) (k : ℤ) s n₀
        (by dsimp [n₀]; omega) ≫ (J.total (ComplexShape.up ℤ)).d n₀ n =
        R.d k (k + 1) ≫
          (R.extendXIso ComplexShape.embeddingUpNat (by rfl :
            ComplexShape.embeddingUpNat.f (k + 1) = ((k + 1 : ℕ) : ℤ))).inv ≫
          J.ιTotal (ComplexShape.up ℤ) ((k + 1 : ℕ) : ℤ) s n (by dsimp [n]; omega) +
        (k : ℤ).negOnePow • (ε.inv ≫ (J.X (k : ℤ)).d s (s + 1) ≫
          J.ιTotal (ComplexShape.up ℤ) (k : ℤ) (s + 1) n (by dsimp [n]; omega)) := by
      rw [J.total_d, Preadditive.comp_add, Preadditive.comp_add]
      rw [J.ι_D₁, J.ι_D₂]
      rw [J.d₁_eq (ComplexShape.up ℤ) (show
          (ComplexShape.up ℤ).Rel (k : ℤ) ((k + 1 : ℕ) : ℤ) by
            change (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ); omega) s n
          (by change ((k + 1 : ℕ) : ℤ) + s = n; dsimp [n]; omega),
        J.d₂_eq (ComplexShape.up ℤ) (k : ℤ) (show
          (ComplexShape.up ℤ).Rel s (s + 1) from rfl) n
          (by change (k : ℤ) + (s + 1) = n; dsimp [n]; omega)]
      simp only [Linear.comp_units_smul]
      change (1 : ℤˣ) • (ε.inv ≫
          (R.extend ComplexShape.embeddingUpNat).d (k : ℤ) ((k + 1 : ℕ) : ℤ) ≫
          J.ιTotal (ComplexShape.up ℤ) ((k + 1 : ℕ) : ℤ) s n _) + _ = _
      rw [one_smul, HomologicalComplex.extend_d_eq R ComplexShape.embeddingUpNat
        (by rfl) (by rfl)]
      simp only [ε, Category.assoc, Iso.inv_hom_id_assoc]
      rfl
    have hdiff : b ≫ (L.step s : CochainComplex B ℤ).d n₀ n =
        R.d k (k + 1) ≫ a +
        (k : ℤ).negOnePow • (ε.inv ≫ (J.X (k : ℤ)).d s (s + 1) ≫ t ≫ inc) := by
      apply (cancel_mono m).1
      simp only [Preadditive.add_comp, Linear.units_smul_comp, Category.assoc]
      rw [← (L.step s).arrow.comm n₀ n]
      dsimp only [b]
      rw [Category.assoc]
      rw [reassoc_of% hb₀, ha, hinc, ht]
      exact htotal
    rw [← Category.assoc, hdiff, Preadditive.add_comp, Category.assoc]
    simp only [Linear.units_smul_comp, Category.assoc, hzero, comp_zero, smul_zero, add_zero]

end CategoryTheory.Functor
