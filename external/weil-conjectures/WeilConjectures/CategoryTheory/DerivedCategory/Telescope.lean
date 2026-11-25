/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Telescopes of eventually constant sequences of complexes

Let `X₀ ⟶ X₁ ⟶ ⋯` be a sequence in a preadditive category with a cocone `Xₙ ⟶ L` whose legs
are isomorphisms from some index on. Then the *telescope* short complex

`0 ⟶ ∐ₙ Xₙ ⟶ ∐ₙ Xₙ ⟶ L ⟶ 0`,

whose first map is `𝟙 - shift`, is split (`CategoryTheory.Limits.Cofan.telescopeSplitting`).

Applied degreewise to a sequence of cochain complexes over an abelian category which is
degreewise eventually constant (for instance the canonical truncations `τ^{≤ n} L`), this gives
a short exact sequence of complexes, hence a distinguished triangle in the derived category.
Consequently, a natural transformation `τ : F ⟶ G`, compatible with the shifts, between
triangulated functors out of `D(C)` which commute with countable coproducts, is an isomorphism
at `L` as soon as it is an isomorphism at all the terms of the sequence
(`DerivedCategory.isIso_app_Q_obj_of_cocone`). In particular it suffices to check this on the
complexes which are bounded above (`DerivedCategory.isIso_app_of_isIso_app_Q_obj_isStrictlyLE`).

## Main statements

- `CategoryTheory.NatTrans.isIso_app_of_isColimit_cofan`: closure under coproducts.
- `CategoryTheory.Limits.Cofan.telescopeSplitting`: the telescope is split.
- `CochainComplex.telescopeShortComplex_shortExact`: the telescope of a degreewise eventually
  constant sequence of complexes is short exact.
- `DerivedCategory.isIso_app_Q_obj_of_cocone`: closure under such telescopes.
- `DerivedCategory.isIso_app_of_isIso_app_Q_obj_isStrictlyLE`: reduction to bounded above
  complexes.
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

namespace CategoryTheory.NatTrans

variable {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D} (τ : F ⟶ G)

/-- If `F` and `G` preserve a coproduct and a natural transformation `τ : F ⟶ G` is an
isomorphism at the summands, it is an isomorphism at the coproduct. -/
lemma isIso_app_of_isColimit_cofan {J : Type*} {X : J → C} {c : Cofan X} (hc : IsColimit c)
    [PreservesColimit (Discrete.functor X) F] [PreservesColimit (Discrete.functor X) G]
    (h : ∀ j, IsIso (τ.app (X j))) : IsIso (τ.app c.pt) := by
  let hF := isColimitOfPreserves F hc
  let hG := isColimitOfPreserves G hc
  have : τ.app c.pt = (IsColimit.coconePointsIsoOfNatIso hF hG
      (Discrete.natIso fun j ↦ asIso (τ.app (X j.as)))).hom := hF.hom_ext fun j ↦ by
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    simp
  rw [this]
  infer_instance

end CategoryTheory.NatTrans

namespace CategoryTheory.Limits.Cofan

variable {C : Type*} [Category* C] [Preadditive C] {X : ℕ ⥤ C} {s : Cofan X.obj}
  (hs : IsColimit s) (c : Cocone X)

/-- The shift endomorphism of the coproduct `∐ₙ Xₙ` of a sequence, mapping the summand `Xₙ` to
the summand `Xₙ₊₁` by the transition morphism. -/
noncomputable def telescopeShift : s.pt ⟶ s.pt :=
  Cofan.IsColimit.desc hs fun n ↦ X.map (homOfLE (Nat.le_add_right n 1)) ≫ s.inj (n + 1)

omit [Preadditive C] in
/-- The shift maps the summand `Xₙ` to the summand `Xₙ₊₁` by the transition morphism. -/
@[reassoc (attr := simp)]
lemma inj_telescopeShift (n : ℕ) :
    s.inj n ≫ telescopeShift hs = X.map (homOfLE (Nat.le_add_right n 1)) ≫ s.inj (n + 1) :=
  Cofan.IsColimit.fac hs _ n

/-- The morphism `∐ₙ Xₙ ⟶ L` induced by a cocone `Xₙ ⟶ L`. -/
noncomputable def telescopeDesc : s.pt ⟶ c.pt :=
  Cofan.IsColimit.desc hs c.ι.app

omit [Preadditive C] in
/-- The morphism `∐ₙ Xₙ ⟶ L` restricts to the legs of the cocone. -/
@[reassoc (attr := simp)]
lemma inj_telescopeDesc (n : ℕ) : s.inj n ≫ telescopeDesc hs c = c.ι.app n :=
  Cofan.IsColimit.fac hs _ n

/-- The telescope short complex `∐ₙ Xₙ ⟶ ∐ₙ Xₙ ⟶ L` of a sequence with a cocone, the first map
being `𝟙 - shift`. -/
@[simps]
noncomputable def telescopeShortComplex : ShortComplex C where
  X₁ := s.pt
  X₂ := s.pt
  X₃ := c.pt
  f := 𝟙 _ - telescopeShift hs
  g := telescopeDesc hs c
  zero := Cofan.IsColimit.hom_ext hs _ _ fun n ↦ by
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, id_comp, inj_telescopeDesc,
      inj_telescopeShift_assoc, Cocone.w, sub_self, comp_zero]

variable {hs c} (N : ℕ) (hN : ∀ n, N ≤ n → IsIso (c.ι.app n))

/-- The transition morphism `Xₙ ⟶ Xₖ` for `n ≤ k`, and `0` otherwise. -/
noncomputable def telescopeTransition (n k : ℕ) : X.obj n ⟶ X.obj k :=
  if h : n ≤ k then X.map (homOfLE h) else 0

/-- The transition morphism `Xₙ ⟶ Xₙ` is the identity. -/
lemma telescopeTransition_self (n : ℕ) : telescopeTransition (X := X) n n = 𝟙 _ := by
  simp [telescopeTransition]

/-- Composing the transition morphism `Xₙ ⟶ Xₖ` with `Xₖ ⟶ Xₖ₊₁` gives `Xₙ ⟶ Xₖ₊₁`. -/
@[reassoc]
lemma telescopeTransition_comp {n k : ℕ} (h : n ≤ k) :
    telescopeTransition (X := X) n k ≫ X.map (homOfLE (Nat.le_add_right k 1)) =
      telescopeTransition n (k + 1) := by
  simp only [telescopeTransition, dite_eq_left h, dite_eq_left (h.trans (Nat.le_add_right k 1)),
    ← X.map_comp]
  rfl

/-- Composing `Xₙ ⟶ Xₙ₊₁` with the transition morphism `Xₙ₊₁ ⟶ Xₖ` gives `Xₙ ⟶ Xₖ`. -/
@[reassoc]
lemma map_comp_telescopeTransition {n k : ℕ} (h : n + 1 ≤ k) :
    X.map (homOfLE (Nat.le_add_right n 1)) ≫ telescopeTransition (n + 1) k =
      telescopeTransition n k := by
  simp only [telescopeTransition, dite_eq_left h, dite_eq_left ((Nat.le_add_right n 1).trans h),
    ← X.map_comp]
  rfl

/-- The transition morphisms are compatible with the legs of the cocone. -/
lemma telescopeTransition_comp_ι {n k : ℕ} (h : n ≤ k) :
    telescopeTransition (X := X) n k ≫ c.ι.app k = c.ι.app n := by
  simp [telescopeTransition, dite_eq_left h]

include hN in
/-- The inverse of the leg `c.ι.app k` for `N ≤ k`, and `0` otherwise. -/
noncomputable def telescopeInv (k : ℕ) : c.pt ⟶ X.obj k :=
  if h : N ≤ k then haveI := hN k h; inv (c.ι.app k) else 0

/-- `telescopeInv` is a right inverse of the legs from the index `N` on. -/
@[reassoc]
lemma ι_telescopeInv {k : ℕ} (h : N ≤ k) : c.ι.app k ≫ telescopeInv N hN k = 𝟙 _ := by
  simp [telescopeInv, dite_eq_left h]

/-- `telescopeInv` is a left inverse of the legs from the index `N` on. -/
lemma telescopeInv_ι {k : ℕ} (h : N ≤ k) : telescopeInv N hN k ≫ c.ι.app k = 𝟙 _ := by
  simp [telescopeInv, dite_eq_left h]

/-- The inverses of the legs are compatible with the transition morphisms. -/
@[reassoc]
lemma telescopeInv_comp_map {k : ℕ} (h : N ≤ k) :
    telescopeInv N hN k ≫ X.map (homOfLE (Nat.le_add_right k 1)) = telescopeInv N hN (k + 1) := by
  have := hN (k + 1) (h.trans (Nat.le_add_right k 1))
  rw [← cancel_mono (c.ι.app (k + 1)), assoc, c.w, telescopeInv_ι N hN h,
    telescopeInv_ι N hN (h.trans (Nat.le_add_right k 1))]

/-- The component on the summand `Xₙ` of the retraction of `𝟙 - shift`:
`∑_{n ≤ k < N} (Xₙ ⟶ Xₖ) - ∑_{N ≤ k < n} (Xₙ ⟶ L ≅ Xₖ)`. -/
noncomputable def telescopeRetractionApp (n : ℕ) : X.obj n ⟶ s.pt :=
  ∑ k ∈ Finset.Ico n N, telescopeTransition n k ≫ s.inj k -
    ∑ k ∈ Finset.Ico N n, c.ι.app n ≫ telescopeInv N hN k ≫ s.inj k

/-- The component of the retraction on a summand `Xₙ` with `n ≤ N`. -/
lemma telescopeRetractionApp_of_le {n : ℕ} (h : n ≤ N) :
    telescopeRetractionApp (s := s) N hN n =
      ∑ k ∈ Finset.Ico n N, telescopeTransition n k ≫ s.inj k := by
  simp [telescopeRetractionApp, Finset.Ico_eq_empty_of_le h]

/-- The component of the retraction on a summand `Xₙ` with `N ≤ n`. -/
lemma telescopeRetractionApp_of_ge {n : ℕ} (h : N ≤ n) :
    telescopeRetractionApp (s := s) N hN n =
      -∑ k ∈ Finset.Ico N n, c.ι.app n ≫ telescopeInv N hN k ≫ s.inj k := by
  simp [telescopeRetractionApp, Finset.Ico_eq_empty_of_le h]

variable (hs) in
/-- The retraction of `𝟙 - shift` in the telescope. -/
noncomputable def telescopeRetraction : s.pt ⟶ s.pt :=
  Cofan.IsColimit.desc hs (telescopeRetractionApp N hN)

/-- The retraction restricted to the summand `Xₙ`. -/
@[reassoc (attr := simp)]
lemma inj_telescopeRetraction (n : ℕ) :
    s.inj n ≫ telescopeRetraction hs N hN = telescopeRetractionApp N hN n :=
  Cofan.IsColimit.fac hs _ n

/-- The retraction is a left inverse of `𝟙 - shift`. -/
lemma telescope_f_r : (𝟙 _ - telescopeShift hs) ≫ telescopeRetraction hs N hN = 𝟙 _ := by
  refine Cofan.IsColimit.hom_ext hs _ _ fun n ↦ ?_
  simp only [Preadditive.comp_sub, comp_id, Preadditive.sub_comp, id_comp,
    inj_telescopeRetraction, inj_telescopeShift_assoc]
  rcases lt_or_ge n N with h | h
  · rw [telescopeRetractionApp_of_le N hN h.le, telescopeRetractionApp_of_le N hN h,
      Finset.sum_eq_sum_Ico_succ_bot h, telescopeTransition_self, id_comp, Preadditive.comp_sum,
      add_sub_assoc, add_eq_left, sub_eq_zero]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [map_comp_telescopeTransition_assoc (Finset.mem_Ico.1 hk).1]
  · rw [telescopeRetractionApp_of_ge N hN h,
      telescopeRetractionApp_of_ge (n := n + 1) N hN (h.trans (Nat.le_add_right n 1))]
    simp only [Preadditive.comp_neg, Preadditive.comp_sum, Cocone.w_assoc]
    rw [Finset.sum_Ico_succ_top h, ι_telescopeInv_assoc N hN h]
    abel

/-- The retraction of `𝟙 - shift` and the section `L ≅ X_N ⟶ ∐ₙ Xₙ` of the projection split the
telescope. -/
lemma telescope_id :
    telescopeRetraction hs N hN ≫ (𝟙 _ - telescopeShift hs) +
      telescopeDesc hs c ≫ telescopeInv N hN N ≫ s.inj N = 𝟙 _ := by
  refine Cofan.IsColimit.hom_ext hs _ _ fun n ↦ ?_
  simp only [Preadditive.comp_add, inj_telescopeRetraction_assoc, inj_telescopeDesc_assoc,
    comp_id]
  rcases le_or_gt n N with h | h
  · have e : c.ι.app n ≫ telescopeInv N hN N = telescopeTransition n N := by
      rw [← telescopeTransition_comp_ι h, assoc, ι_telescopeInv N hN le_rfl, comp_id]
    rw [telescopeRetractionApp_of_le N hN h, reassoc_of% e, Preadditive.sum_comp]
    have : ∀ k ∈ Finset.Ico n N, (telescopeTransition n k ≫ s.inj k) ≫
        (𝟙 _ - telescopeShift hs) =
          -((fun k ↦ telescopeTransition n k ≫ s.inj k) (k + 1) -
            (fun k ↦ telescopeTransition n k ≫ s.inj k) k) := fun k hk ↦ by
      simp only [assoc, Preadditive.comp_sub, comp_id, inj_telescopeShift, neg_sub,
        telescopeTransition_comp_assoc (Finset.mem_Ico.1 hk).1]
    rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib,
      Finset.sum_Ico_sub (fun k ↦ telescopeTransition n k ≫ s.inj k) h,
      telescopeTransition_self, id_comp]
    abel
  · have e : ∀ k, N ≤ k → (c.ι.app n ≫ telescopeInv N hN k ≫ s.inj k) ≫
        (𝟙 _ - telescopeShift hs) =
          -((fun k ↦ c.ι.app n ≫ telescopeInv N hN k ≫ s.inj k) (k + 1) -
            (fun k ↦ c.ι.app n ≫ telescopeInv N hN k ≫ s.inj k) k) := fun k hk ↦ by
      simp only [assoc, Preadditive.comp_sub, comp_id, inj_telescopeShift, neg_sub,
        telescopeInv_comp_map_assoc N hN hk]
    rw [telescopeRetractionApp_of_ge N hN h.le, Preadditive.neg_comp, Preadditive.sum_comp,
      Finset.sum_congr rfl fun k hk ↦ e k (Finset.mem_Ico.1 hk).1, Finset.sum_neg_distrib,
      Finset.sum_Ico_sub (fun k ↦ c.ι.app n ≫ telescopeInv N hN k ≫ s.inj k) h.le,
      ι_telescopeInv_assoc N hN h.le]
    abel

variable (hs c) in
/-- The telescope `0 ⟶ ∐ₙ Xₙ ⟶ ∐ₙ Xₙ ⟶ L ⟶ 0` of a sequence with a cocone whose legs are
isomorphisms from the index `N` on is split. -/
noncomputable def telescopeSplitting : (telescopeShortComplex hs c).Splitting where
  r := telescopeRetraction hs N hN
  s := telescopeInv N hN N ≫ s.inj N
  f_r := telescope_f_r N hN
  s_g := by simp [telescopeInv_ι N hN le_rfl]; rfl
  id := telescope_id N hN

end CategoryTheory.Limits.Cofan

namespace CochainComplex

open Cofan

variable {C : Type*} [Category* C] [Abelian C] [HasCoproductsOfShape ℕ C]
  (X : ℕ ⥤ CochainComplex C ℤ) (c : Cocone X)

/-- In degree `i`, the telescope of a sequence of complexes is the telescope of the sequence of
the terms in degree `i`. -/
noncomputable def mapEvalTelescopeShortComplexIso (i : ℤ) :
    (telescopeShortComplex (coproductIsCoproduct X.obj) c).map
        (HomologicalComplex.eval C (.up ℤ) i) ≅
      telescopeShortComplex (X := X ⋙ HomologicalComplex.eval C (.up ℤ) i)
        (isColimitCofanMkObjOfIsColimit (HomologicalComplex.eval C (.up ℤ) i) _ _
          (coproductIsCoproduct X.obj))
        ((HomologicalComplex.eval C (.up ℤ) i).mapCocone c) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit
      (HomologicalComplex.eval C (.up ℤ) i) _ _ (coproductIsCoproduct X.obj)) _ _ fun n ↦ by
        have h₁ := inj_telescopeShift (X := X ⋙ HomologicalComplex.eval C (.up ℤ) i)
          (isColimitCofanMkObjOfIsColimit (HomologicalComplex.eval C (.up ℤ) i) _ _
            (coproductIsCoproduct X.obj)) n
        have h₂ := congr_arg (fun φ ↦ HomologicalComplex.Hom.f φ i)
          (inj_telescopeShift (coproductIsCoproduct X.obj) n)
        simp only [Iso.refl_hom, id_comp, comp_id, ShortComplex.map_f, telescopeShortComplex_f,
          HomologicalComplex.eval_map, Preadditive.comp_sub, cofan_mk_inj, Functor.comp_map,
          HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply, HomologicalComplex.id_f]
          at h₁ h₂ ⊢
        rw [h₁, h₂]
        erw [comp_id])
    (Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit
      (HomologicalComplex.eval C (.up ℤ) i) _ _ (coproductIsCoproduct X.obj)) _ _ fun n ↦ by
        have h₁ := inj_telescopeDesc (X := X ⋙ HomologicalComplex.eval C (.up ℤ) i)
          (isColimitCofanMkObjOfIsColimit (HomologicalComplex.eval C (.up ℤ) i) _ _
            (coproductIsCoproduct X.obj)) ((HomologicalComplex.eval C (.up ℤ) i).mapCocone c) n
        have h₂ := congr_arg (fun φ ↦ HomologicalComplex.Hom.f φ i)
          (inj_telescopeDesc (coproductIsCoproduct X.obj) c n)
        simp only [Iso.refl_hom, id_comp, comp_id, ShortComplex.map_g, telescopeShortComplex_g,
          HomologicalComplex.eval_map, cofan_mk_inj, HomologicalComplex.comp_f,
          Functor.mapCocone_ι_app] at h₁ h₂ ⊢
        rw [h₁, h₂])

/-- The telescope `0 ⟶ ∐ₙ Xₙ ⟶ ∐ₙ Xₙ ⟶ L ⟶ 0` of a sequence of complexes with a cocone
`Xₙ ⟶ L` is short exact when, in each degree, the legs of the cocone are isomorphisms from some
index on. -/
lemma shortExact_telescopeShortComplex
    (hc : ∀ i, ∃ N, ∀ n, N ≤ n → IsIso ((c.ι.app n).f i)) :
    (telescopeShortComplex (coproductIsCoproduct X.obj) c).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦ by
    obtain ⟨N, hN⟩ := hc i
    exact ShortComplex.shortExact_of_iso (mapEvalTelescopeShortComplexIso X c i).symm
      (telescopeSplitting _ _ N hN).shortExact

end CochainComplex

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C] [HasCoproductsOfShape ℕ C]
  [Abelian.HasKInjectiveResolutions C]
  {T : Type*} [Category* T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor T n).Additive] [Pretriangulated T]
  {F G : DerivedCategory C ⥤ T} [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated]
  [G.IsTriangulated] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
  [PreservesColimitsOfShape (Discrete ℕ) F] [PreservesColimitsOfShape (Discrete ℕ) G]

/-- Let `Xₙ ⟶ L` be a cocone over a sequence of complexes whose legs are, in each degree,
isomorphisms from some index on. If `τ` is an isomorphism at all the `Xₙ`, it is an isomorphism
at `L`: this follows from the telescope distinguished triangle `∐ Xₙ ⟶ ∐ Xₙ ⟶ L ⟶ (∐ Xₙ)[1]`. -/
lemma isIso_app_Q_obj_of_cocone (X : ℕ ⥤ CochainComplex C ℤ) (c : Cocone X)
    (hc : ∀ i, ∃ N, ∀ n, N ≤ n → IsIso ((c.ι.app n).f i))
    (h : ∀ n, IsIso (τ.app (Q.obj (X.obj n)))) :
    IsIso (τ.app (Q.obj c.pt)) := by
  have h₁ : IsIso (τ.app (Q.obj (∐ X.obj))) :=
    NatTrans.isIso_app_of_isColimit_cofan τ (isColimitCofanMkQObj (coproductIsCoproduct _)) h
  exact NatTrans.isIso_app_obj₃_of_isIso_app_obj₁₂ τ
    (triangleOfSES_distinguished (CochainComplex.shortExact_telescopeShortComplex X c hc)) h₁ h₁

/-- If `τ` is an isomorphism at all the bounded above complexes, it is an isomorphism: every
complex `L` is the union of its canonical truncations `τ^{≤ n} L`. -/
lemma isIso_app_of_isIso_app_Q_obj_isStrictlyLE
    (h : ∀ (L : CochainComplex C ℤ) (b : ℤ), L.IsStrictlyLE b → IsIso (τ.app (Q.obj L)))
    (K : DerivedCategory C) : IsIso (τ.app K) := by
  let L := Q.objPreimage K
  rw [← NatTrans.isIso_app_iff_of_iso τ (Q.objObjPreimageIso K)]
  let ι : ℕ ⥤ ℤ := Monotone.functor (f := ((↑) : ℕ → ℤ)) Nat.mono_cast
  refine isIso_app_Q_obj_of_cocone τ (ι ⋙ L.filtrationLE) (L.filtrationLECocone.whisker ι)
    (fun i ↦ ⟨(i + 1).toNat, fun n hn ↦ L.isIso_ιTruncLE_f n i (by lia)⟩)
    (fun n ↦ h _ n (by dsimp [ι, CochainComplex.filtrationLE]; infer_instance))

end DerivedCategory
