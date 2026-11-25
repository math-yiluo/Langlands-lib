/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!

# Objects of a derived category with homology concentrated in an interval

For an abelian category `C`, this file records the property that an object of `D(C)` has
homology in degrees `[a, b]` only, expressed through the canonical t-structure
`DerivedCategory.TStructure.t` so that the whole t-structure API applies to it.

## Main definitions

- `DerivedCategory.homologyConcentratedIn`: homology concentrated in `[a, b]`.

## Main statements

- `DerivedCategory.exists_homologyConcentratedIn_iff_bounded`: an object is bounded exactly
  when its homology is concentrated in some interval.
- `DerivedCategory.prop_of_bounded`: *dévissage*, a triangulated subcategory of `D(C)`
  containing the objects of `C` satisfying `P`, placed in degree `0`, contains every bounded
  object all of whose homology objects satisfy `P`.
- `DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE`: for `X ≤ n ≤ Y`, the functor
  `H^n` is bijective on morphisms `X ⟶ Y`.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- An object of `D(C)` has *homology concentrated in `[a, b]`* if it is both `≥ a` and `≤ b`
for the canonical t-structure `DerivedCategory.TStructure.t`, that is, if its homology
objects vanish outside the interval `[a, b]`. -/
def homologyConcentratedIn (a b : ℤ) : ObjectProperty (DerivedCategory C) :=
  fun M ↦ TStructure.t.IsGE M a ∧ TStructure.t.IsLE M b

lemma homologyConcentratedIn_iff (a b : ℤ) (M : DerivedCategory C) :
    homologyConcentratedIn a b M ↔ TStructure.t.IsGE M a ∧ TStructure.t.IsLE M b :=
  Iff.rfl

/-- Widening the interval preserves homology concentration. -/
lemma homologyConcentratedIn.mono {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b')
    {M : DerivedCategory C} (hM : homologyConcentratedIn a b M) :
    homologyConcentratedIn a' b' M := by
  obtain ⟨h₁, h₂⟩ := hM
  exact ⟨TStructure.t.isGE_of_ge M a' a ha, TStructure.t.isLE_of_le M b b' hb⟩

/-- A retract of an object with homology concentrated in `[a, b]` has homology concentrated in
`[a, b]`: its homology objects are retracts of those of the bigger object. -/
instance (a b : ℤ) : (homologyConcentratedIn (C := C) a b).IsStableUnderRetracts where
  of_retract {_ N} e h := by
    obtain ⟨h₁, h₂⟩ := h
    have key (q : ℤ) (hq : IsZero ((homologyFunctor C q).obj N)) :
        IsZero ((homologyFunctor C q).obj _) := (IsZero.iff_id_eq_zero _).2 (by
      rw [← (e.map (homologyFunctor C q)).retract, hq.eq_of_tgt (e.map _).i 0, zero_comp])
    exact ⟨(isGE_iff _ a).2 fun q hq ↦ key q ((isGE_iff N a).1 h₁ q hq),
      (isLE_iff _ b).2 fun q hq ↦ key q ((isLE_iff N b).1 h₂ q hq)⟩

/-- An object of `D(C)` is bounded exactly when its homology is concentrated in some
interval. -/
lemma exists_homologyConcentratedIn_iff_bounded (M : DerivedCategory C) :
    (∃ a b : ℤ, homologyConcentratedIn a b M) ↔ TStructure.t.bounded M := by
  constructor
  · rintro ⟨a, b, ha, hb⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a, b, ha, hb⟩

/-- For a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` and `n : ℤ` such that the homology
objects of `X₃` in degrees `n - 1` and `n` vanish, the map `Hⁿ X₁ ⟶ Hⁿ X₂` is an isomorphism. -/
lemma isIso_homologyMap_mor₁ (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₀ : IsZero ((homologyFunctor C n₀).obj T.obj₃))
    (h₁ : IsZero ((homologyFunctor C n₁).obj T.obj₃)) :
    IsIso ((homologyFunctor C n₁).map T.mor₁) := by
  have := (HomologySequence.mono_homologyMap_mor₁_iff T hT n₀ n₁ h).2 (h₀.eq_of_src _ _)
  have := (HomologySequence.epi_homologyMap_mor₁_iff T hT n₁).2 (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- For a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧` and `n : ℤ` such that the homology
objects of `X₁` in degrees `n` and `n + 1` vanish, the map `Hⁿ X₂ ⟶ Hⁿ X₃` is an isomorphism. -/
lemma isIso_homologyMap_mor₂ (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (h₀ : IsZero ((homologyFunctor C n₀).obj T.obj₁))
    (h₁ : IsZero ((homologyFunctor C n₁).obj T.obj₁)) :
    IsIso ((homologyFunctor C n₀).map T.mor₂) := by
  have := (HomologySequence.mono_homologyMap_mor₂_iff T hT n₀).2 (h₀.eq_of_src _ _)
  have := (HomologySequence.epi_homologyMap_mor₂_iff T hT n₀ n₁ h).2 (h₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- **Dévissage of bounded complexes.** Let `Q` be a triangulated subcategory of `D(C)` and
`P` a property of objects of `C` such that `Q` contains the objects of `C`
satisfying `P`, placed in degree `0`. Then `Q` contains every object of `D(C)` whose homology
is concentrated in `[a, b]` and satisfies `P` there: by induction on `b - a`, using the
truncation triangle `τ_{< b} M ⟶ M ⟶ τ_{≥ b} M ⟶`, whose third term is `H^b M` placed in
degree `b`. -/
lemma prop_of_isGE_of_isLE (Q : ObjectProperty (DerivedCategory C)) [Q.IsTriangulated]
    [Q.IsClosedUnderIsomorphisms] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (hP : ∀ X, P X → Q ((singleFunctor C 0).obj X)) (n : ℕ) :
    ∀ (a : ℤ) (M : DerivedCategory C), M.IsGE a → M.IsLE (a + n - 1) →
      (∀ q, a ≤ q → q < a + n → P ((homologyFunctor C q).obj M)) → Q M := by
  induction n with
  | zero =>
    intro a M _ _ _
    have : M.IsLE (a - 1) := by simpa using ‹M.IsLE (a + ↑(0 : ℕ) - 1)›
    exact Q.prop_of_isZero (TStructure.t.isZero M (a - 1) a (by lia))
  | succ n ih =>
    intro a M _ _ hM
    set b : ℤ := a + n
    have hT := TStructure.t.triangleLTGE_distinguished b M
    -- the third term is `H^b M` placed in degree `b`
    have : ((TStructure.t.triangleLTGE b).obj M).obj₃.IsLE b := by
      have : M.IsLE b := TStructure.t.isLE_of_le M (a + ↑(n + 1) - 1) _ (by lia)
      exact inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj M) b)
    have : ((TStructure.t.triangleLTGE b).obj M).obj₃.IsGE b := by
      infer_instance
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
      ((TStructure.t.triangleLTGE b).obj M).obj₃ b
    have h₁ : IsZero ((homologyFunctor C (b + 1)).obj ((TStructure.t.triangleLTGE b).obj M).obj₁) :=
      isZero_of_isLE _ (b - 1) _ (by lia)
    have h₀ : IsZero ((homologyFunctor C b).obj ((TStructure.t.triangleLTGE b).obj M).obj₁) :=
      isZero_of_isLE _ (b - 1) _ (by lia)
    have := isIso_homologyMap_mor₂ _ hT b (b + 1) rfl h₀ h₁
    have hY : P Y := P.prop_of_iso
      (asIso ((homologyFunctor C b).map ((TStructure.t.triangleLTGE b).obj M).mor₂) ≪≫
        (homologyFunctor C b).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso C b).app Y)
      (hM b (by lia) (by lia))
    have h₃ : Q ((TStructure.t.triangleLTGE b).obj M).obj₃ := by
      refine Q.prop_of_iso
        (e ≪≫ (((singleFunctors C).shiftIso (-b) b 0 (by lia)).app Y).symm).symm ?_
      exact Q.le_shift (-b) _ (hP Y hY)
    -- the first term is handled by induction
    have h₁ : Q ((TStructure.t.triangleLTGE b).obj M).obj₁ := by
      refine ih a _ ?_ ?_ fun q hq hq' ↦ ?_
      · exact inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj M) a)
      · exact TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
      · have : IsIso ((homologyFunctor C q).map ((TStructure.t.triangleLTGE b).obj M).mor₁) :=
          isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
            (isZero_of_isGE _ b _ (by lia)) (isZero_of_isGE _ b _ (by lia))
        exact P.prop_of_iso
          (asIso ((homologyFunctor C q).map ((TStructure.t.triangleLTGE b).obj M).mor₁)).symm
          (hM q hq (by lia))
    obtain ⟨M', hM', ⟨e'⟩⟩ := Q.ext_of_isTriangulatedClosed₂' _ hT h₁ h₃
    exact Q.prop_of_iso e'.symm hM'

/-- **Dévissage of bounded complexes.** Let `Q` be a triangulated subcategory of `D(C)` and
`P` a property of objects of `C` such that `Q` contains the objects of `C` satisfying `P`,
placed in degree `0`. Then `Q` contains every bounded object of `D(C)` all of whose homology
objects satisfy `P`. -/
lemma prop_of_bounded (Q : ObjectProperty (DerivedCategory C)) [Q.IsTriangulated]
    [Q.IsClosedUnderIsomorphisms] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (hP : ∀ X, P X → Q ((singleFunctor C 0).obj X)) (M : DerivedCategory C)
    (hM : TStructure.t.bounded M) (hMP : ∀ n, P ((homologyFunctor C n).obj M)) : Q M := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hM
  have : M.IsLE (a + ↑(b - a + 1).toNat - 1) :=
    TStructure.t.isLE_of_le M b _ (by lia)
  exact prop_of_isGE_of_isLE Q P hP (b - a + 1).toNat a M ha this fun q _ _ ↦ hMP q

/-- **Dévissage of bounded complexes, degreewise version.** Let `Q` be a property of objects of
`D(C)` closed under isomorphisms and extensions (for a distinguished triangle
`X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁⟦1⟧`, `Q X₁` and `Q X₃` imply `Q X₂`) and satisfied by zero objects, and let
`P q` be a property of objects of `C` for every degree `q` such that `Q` contains the objects
satisfying `P q` placed in degree `q`. Then `Q` contains every object whose homology is
concentrated in `[a, a + n - 1]` with `P q` holding for the homology in degree `q`. Unlike
`DerivedCategory.prop_of_isGE_of_isLE`, `Q` need not be stable under shifts. -/
lemma prop_of_isGE_of_isLE_of_degreewise (Q : ObjectProperty (DerivedCategory C))
    [Q.IsClosedUnderIsomorphisms] (hQ₀ : ∀ M, IsZero M → Q M)
    (hQ : ∀ T ∈ distTriang (DerivedCategory C), Q T.obj₁ → Q T.obj₃ → Q T.obj₂)
    (P : ℤ → ObjectProperty C) [∀ q, (P q).IsClosedUnderIsomorphisms]
    (hP : ∀ q X, P q X → Q ((singleFunctor C q).obj X)) (n : ℕ) :
    ∀ (a : ℤ) (M : DerivedCategory C), M.IsGE a → M.IsLE (a + n - 1) →
      (∀ q, a ≤ q → q < a + n → P q ((homologyFunctor C q).obj M)) → Q M := by
  induction n with
  | zero =>
    intro a M _ _ _
    have : M.IsLE (a - 1) := by simpa using ‹M.IsLE (a + ↑(0 : ℕ) - 1)›
    exact hQ₀ M (TStructure.t.isZero M (a - 1) a (by lia))
  | succ n ih =>
    intro a M _ _ hM
    set b : ℤ := a + n
    have hT := TStructure.t.triangleLTGE_distinguished b M
    -- the third term is `H^b M` placed in degree `b`
    have : ((TStructure.t.triangleLTGE b).obj M).obj₃.IsLE b := by
      have : M.IsLE b := TStructure.t.isLE_of_le M (a + ↑(n + 1) - 1) _ (by lia)
      exact inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj M) b)
    have : ((TStructure.t.triangleLTGE b).obj M).obj₃.IsGE b := by
      infer_instance
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
      ((TStructure.t.triangleLTGE b).obj M).obj₃ b
    have h₁ : IsZero ((homologyFunctor C (b + 1)).obj ((TStructure.t.triangleLTGE b).obj M).obj₁) :=
      isZero_of_isLE _ (b - 1) _ (by lia)
    have h₀ : IsZero ((homologyFunctor C b).obj ((TStructure.t.triangleLTGE b).obj M).obj₁) :=
      isZero_of_isLE _ (b - 1) _ (by lia)
    have := isIso_homologyMap_mor₂ _ hT b (b + 1) rfl h₀ h₁
    have hY : P b Y := (P b).prop_of_iso
      (asIso ((homologyFunctor C b).map ((TStructure.t.triangleLTGE b).obj M).mor₂) ≪≫
        (homologyFunctor C b).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso C b).app Y)
      (hM b (by lia) (by lia))
    have h₃ : Q ((TStructure.t.triangleLTGE b).obj M).obj₃ := Q.prop_of_iso e.symm (hP b Y hY)
    -- the first term is handled by induction
    have h₁ : Q ((TStructure.t.triangleLTGE b).obj M).obj₁ := by
      refine ih a _ ?_ ?_ fun q hq hq' ↦ ?_
      · exact inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj M) a)
      · exact TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
      · have : IsIso ((homologyFunctor C q).map ((TStructure.t.triangleLTGE b).obj M).mor₁) :=
          isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
            (isZero_of_isGE _ b _ (by lia)) (isZero_of_isGE _ b _ (by lia))
        exact (P q).prop_of_iso
          (asIso ((homologyFunctor C q).map ((TStructure.t.triangleLTGE b).obj M).mor₁)).symm
          (hM q hq (by lia))
    exact hQ _ hT h₁ h₃

/-- **Dévissage of bounded complexes, degreewise version**, for bounded objects: see
`DerivedCategory.prop_of_isGE_of_isLE_of_degreewise`. -/
lemma prop_of_bounded_of_degreewise (Q : ObjectProperty (DerivedCategory C))
    [Q.IsClosedUnderIsomorphisms] (hQ₀ : ∀ M, IsZero M → Q M)
    (hQ : ∀ T ∈ distTriang (DerivedCategory C), Q T.obj₁ → Q T.obj₃ → Q T.obj₂)
    (P : ℤ → ObjectProperty C) [∀ q, (P q).IsClosedUnderIsomorphisms]
    (hP : ∀ q X, P q X → Q ((singleFunctor C q).obj X)) (M : DerivedCategory C)
    (hM : TStructure.t.bounded M) (hMP : ∀ q, P q ((homologyFunctor C q).obj M)) : Q M := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hM
  have : M.IsLE (a + ↑(b - a + 1).toNat - 1) :=
    TStructure.t.isLE_of_le M b _ (by lia)
  exact prop_of_isGE_of_isLE_of_degreewise Q hQ₀ hQ P hP (b - a + 1).toNat a M ha this
    fun q _ _ ↦ hMP q
section Amplitude

variable {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
  (Φ : DerivedCategory C ⥤ DerivedCategory D) [Φ.CommShift ℤ] [Φ.IsTriangulated] (d : ℤ)

omit [Φ.IsTriangulated] in
/-- If a triangulated functor `Φ : D(C) ⥤ D(D)` sends every object of `C` placed in degree `0`
into degrees `≤ d`, it sends every object of `C` placed in degree `n` into degrees `≤ n + d`. -/
lemma isLE_obj_singleFunctor_obj (hΦ : ∀ F : C, (Φ.obj ((singleFunctor C 0).obj F)).IsLE d)
    (F : C) (n : ℤ) : (Φ.obj ((singleFunctor C n).obj F)).IsLE (n + d) := by
  have := hΦ F
  have : TStructure.t.IsLE ((Φ.obj ((singleFunctor C 0).obj F))⟦-n⟧) (n + d) :=
    TStructure.t.isLE_shift _ d (-n) (n + d) (by lia)
  let e : (Φ.obj ((singleFunctor C 0).obj F))⟦-n⟧ ≅ Φ.obj ((singleFunctor C n).obj F) :=
    (Φ.commShiftIso (-n)).symm.app _ ≪≫
      Φ.mapIso (((singleFunctors C).shiftIso (-n) n 0 (by lia)).app F)
  exact TStructure.t.isLE_of_iso e (n + d)

/-- **Amplitude by dévissage.** If a triangulated functor `Φ : D(C) ⥤ D(D)` sends every object
of `C` placed in degree `0` into degrees `≤ d`, it sends every bounded object concentrated in
degrees `≤ n` into degrees `≤ n + d`: by induction on the length, using the truncation triangle
`τ_{< n} M ⟶ M ⟶ τ_{≥ n} M ⟶` whose third term is `Hⁿ M` placed in degree `n`. -/
lemma isLE_obj_of_isLE (hΦ : ∀ F : C, (Φ.obj ((singleFunctor C 0).obj F)).IsLE d)
    (M : DerivedCategory C) (hM : TStructure.t.bounded M) (n : ℤ) [M.IsLE n] :
    (Φ.obj M).IsLE (n + d) := by
  obtain ⟨⟨a, ha⟩, -⟩ := hM
  suffices h : ∀ (k : ℕ) (M : DerivedCategory C) (n : ℤ), M.IsGE (n - k) → M.IsLE n →
      (Φ.obj M).IsLE (n + d) by
    exact h (n - a).toNat M n (TStructure.t.isGE_of_ge M _ a (by lia)) inferInstance
  intro k
  induction k with
  | zero =>
    intro M n h₁ h₂
    have : M.IsGE n := by simpa using h₁
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE M n
    have := isLE_obj_singleFunctor_obj Φ d hΦ Y n
    exact TStructure.t.isLE_of_iso (Φ.mapIso e.symm) (n + d)
  | succ k ih =>
    intro M n h₁ h₂
    have hT := Φ.map_distinguished _ (TStructure.t.triangleLTGE_distinguished n M)
    refine TStructure.t.isLE₂ _ hT (n + d) ?_ ?_
    · have : ((TStructure.t.triangleLTGE n).obj M).obj₁.IsLE (n - 1) :=
        TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
      have : ((TStructure.t.triangleLTGE n).obj M).obj₁.IsGE (n - 1 - k) := by
        have : M.IsGE (n - 1 - k) := TStructure.t.isGE_of_ge M _ (n - ↑(k + 1)) (by lia)
        exact inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT n).obj M) _)
      have := ih _ (n - 1) this inferInstance
      exact TStructure.t.isLE_of_le (Φ.obj ((TStructure.t.triangleLTGE n).obj M).obj₁)
        (n - 1 + d) (n + d) (by lia)
    · have : ((TStructure.t.triangleLTGE n).obj M).obj₃.IsLE n :=
        inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE n).obj M) n)
      have : ((TStructure.t.triangleLTGE n).obj M).obj₃.IsGE n :=
        inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncGE n).obj M) n)
      obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
        ((TStructure.t.triangleLTGE n).obj M).obj₃ n
      have := isLE_obj_singleFunctor_obj Φ d hΦ Y n
      exact TStructure.t.isLE_of_iso (Φ.mapIso e.symm) (n + d)

omit [Φ.IsTriangulated] in
/-- If a triangulated functor `Φ : D(C) ⥤ D(D)` sends every object of `C` placed in degree `0`
into degrees `≥ d`, it sends every object of `C` placed in degree `n` into degrees `≥ n + d`. -/
lemma isGE_obj_singleFunctor_obj (hΦ : ∀ F : C, (Φ.obj ((singleFunctor C 0).obj F)).IsGE d)
    (F : C) (n : ℤ) : (Φ.obj ((singleFunctor C n).obj F)).IsGE (n + d) := by
  have := hΦ F
  have : TStructure.t.IsGE ((Φ.obj ((singleFunctor C 0).obj F))⟦-n⟧) (n + d) :=
    TStructure.t.isGE_shift _ d (-n) (n + d) (by lia)
  let e : (Φ.obj ((singleFunctor C 0).obj F))⟦-n⟧ ≅ Φ.obj ((singleFunctor C n).obj F) :=
    (Φ.commShiftIso (-n)).symm.app _ ≪≫
      Φ.mapIso (((singleFunctors C).shiftIso (-n) n 0 (by lia)).app F)
  exact TStructure.t.isGE_of_iso e (n + d)

/-- **Amplitude by dévissage, lower bound.** If a triangulated functor `Φ : D(C) ⥤ D(D)` sends
every object of `C` placed in degree `0` into degrees `≥ d`, it sends every bounded object
concentrated in degrees `≥ n` into degrees `≥ n + d`: by induction on the length, using the
truncation triangle `τ_{≤ n} M ⟶ M ⟶ τ_{> n} M ⟶` whose first term is `Hⁿ M` placed in
degree `n`. -/
lemma isGE_obj_of_isGE (hΦ : ∀ F : C, (Φ.obj ((singleFunctor C 0).obj F)).IsGE d)
    (M : DerivedCategory C) (hM : TStructure.t.bounded M) (n : ℤ) [M.IsGE n] :
    (Φ.obj M).IsGE (n + d) := by
  obtain ⟨-, ⟨b, hb⟩⟩ := hM
  suffices h : ∀ (k : ℕ) (M : DerivedCategory C) (n : ℤ), M.IsGE n → M.IsLE (n + k) →
      (Φ.obj M).IsGE (n + d) by
    exact h (b - n).toNat M n inferInstance (TStructure.t.isLE_of_le M b _ (by lia))
  intro k
  induction k with
  | zero =>
    intro M n h₁ h₂
    have : M.IsLE n := by simpa using h₂
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE M n
    have := isGE_obj_singleFunctor_obj Φ d hΦ Y n
    exact TStructure.t.isGE_of_iso (Φ.mapIso e.symm) (n + d)
  | succ k ih =>
    intro M n h₁ h₂
    have hT := Φ.map_distinguished _ (TStructure.t.triangleLTGE_distinguished (n + 1) M)
    refine TStructure.t.isGE₂ _ hT (n + d) ?_ ?_
    · have : ((TStructure.t.triangleLTGE (n + 1)).obj M).obj₁.IsLE n :=
        TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
      have : ((TStructure.t.triangleLTGE (n + 1)).obj M).obj₁.IsGE n :=
        inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT (n + 1)).obj M) _)
      obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
        ((TStructure.t.triangleLTGE (n + 1)).obj M).obj₁ n
      have := isGE_obj_singleFunctor_obj Φ d hΦ Y n
      exact TStructure.t.isGE_of_iso (Φ.mapIso e.symm) (n + d)
    · have : ((TStructure.t.triangleLTGE (n + 1)).obj M).obj₃.IsGE (n + 1) :=
        inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncGE (n + 1)).obj M) (n + 1))
      have : ((TStructure.t.triangleLTGE (n + 1)).obj M).obj₃.IsLE (n + 1 + k) := by
        have : M.IsLE (n + 1 + k) := TStructure.t.isLE_of_le M (n + ↑(k + 1)) _ (by lia)
        exact inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE (n + 1)).obj M) _)
      have := ih _ (n + 1) inferInstance this
      exact TStructure.t.isGE_of_ge (Φ.obj ((TStructure.t.triangleLTGE (n + 1)).obj M).obj₃)
        (n + d) (n + 1 + d) (by lia)

end Amplitude

section Heart

open Category
open TStructure (t)

/-- Let `T : A ⟶ B ⟶ C ⟶ A[1]` be a distinguished triangle with `A ≤ a - 1` and `C ≥ a`.
Then `H^n(A) ⟶ H^n(B)` is an isomorphism for `n < a`. -/
lemma isIso_homologyFunctor_map_mor₁_of_isLE_of_isGE (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (a n : ℤ) (h : n < a) [T.obj₁.IsLE (a - 1)] [T.obj₃.IsGE a] :
    IsIso ((homologyFunctor C n).map T.mor₁) := by
  have h₁ : Mono ((homologyFunctor C n).map T.mor₁) :=
    ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff _ hT (n - 1) n
      (by lia)).2 (IsZero.eq_of_src (isZero_of_isGE _ a _ (by lia)) _ _)
  have h₂ : Epi ((homologyFunctor C n).map T.mor₁) :=
    ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff _ hT n).2
      (IsZero.eq_of_tgt (isZero_of_isGE _ a _ h) _ _)
  exact isIso_of_mono_of_epi _

/-- Let `T : A ⟶ B ⟶ C ⟶ A[1]` be a distinguished triangle with `A ≤ a - 1` and `C ≥ a`.
Then `H^n(B) ⟶ H^n(C)` is an isomorphism for `a ≤ n`. -/
lemma isIso_homologyFunctor_map_mor₂_of_isLE_of_isGE (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (a n : ℤ) (h : a ≤ n) [T.obj₁.IsLE (a - 1)] [T.obj₃.IsGE a] :
    IsIso ((homologyFunctor C n).map T.mor₂) := by
  have h₁ : Mono ((homologyFunctor C n).map T.mor₂) :=
    ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₂_iff _ hT n).2
      (IsZero.eq_of_src (isZero_of_isLE _ (a - 1) _ (by lia)) _ _)
  have h₂ : Epi ((homologyFunctor C n).map T.mor₂) :=
    ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff _ hT n (n + 1) rfl).2
      (IsZero.eq_of_tgt (isZero_of_isLE _ (a - 1) _ (by lia)) _ _)
  exact isIso_of_mono_of_epi _

/-- `H^n(τ_{<a} X) ⟶ H^n(X)` is an isomorphism for `n < a`. -/
lemma isIso_homologyFunctor_map_truncLTι_app (X : DerivedCategory C) (a n : ℤ) (h : n < a) :
    IsIso ((homologyFunctor C n).map ((t.truncLTι a).app X)) :=
  isIso_homologyFunctor_map_mor₁_of_isLE_of_isGE _ (t.triangleLTGE_distinguished a X) a n h

/-- `H^n(X) ⟶ H^n(τ_{≥a} X)` is an isomorphism for `a ≤ n`. -/
lemma isIso_homologyFunctor_map_truncGEπ_app (X : DerivedCategory C) (a n : ℤ) (h : a ≤ n) :
    IsIso ((homologyFunctor C n).map ((t.truncGEπ a).app X)) :=
  isIso_homologyFunctor_map_mor₂_of_isLE_of_isGE _ (t.triangleLTGE_distinguished a X) a n h

/-- On objects of the shifted heart `[n, n]`, the functor `H^n` is bijective on morphisms. -/
lemma homologyFunctor_map_bijective_of_isGE_of_isLE {P Q : DerivedCategory C} (n : ℤ)
    [P.IsGE n] [P.IsLE n] [Q.IsGE n] [Q.IsLE n] :
    Function.Bijective (fun φ : P ⟶ Q ↦ (homologyFunctor C n).map φ) := by
  obtain ⟨A, ⟨eP⟩⟩ := P.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  obtain ⟨B, ⟨eQ⟩⟩ := Q.exists_iso_singleFunctor_obj_of_isGE_of_isLE n
  let ε := singleFunctorCompHomologyFunctorIso C n
  have key (a : A ⟶ B) : (homologyFunctor C n).map ((singleFunctor C n).map a) =
      ε.hom.app A ≫ a ≫ ε.inv.app B := by
    have := ε.hom.naturality a
    simp only [Functor.comp_map, Functor.id_map] at this
    calc (homologyFunctor C n).map ((singleFunctor C n).map a)
        = ((homologyFunctor C n).map ((singleFunctor C n).map a) ≫ ε.hom.app B) ≫
            ε.inv.app B := by rw [assoc, Iso.hom_inv_id_app]; exact (comp_id _).symm
      _ = _ := by rw [this, assoc]
  constructor
  · intro φ φ' h
    simp only at h
    suffices (singleFunctor C n).preimage (eP.inv ≫ φ ≫ eQ.hom) =
        (singleFunctor C n).preimage (eP.inv ≫ φ' ≫ eQ.hom) by
      have := congrArg (singleFunctor C n).map this
      simp only [Functor.map_preimage] at this
      simpa using this
    have h1 := key ((singleFunctor C n).preimage (eP.inv ≫ φ ≫ eQ.hom))
    have h2 := key ((singleFunctor C n).preimage (eP.inv ≫ φ' ≫ eQ.hom))
    simp only [Functor.map_preimage, Functor.map_comp, h] at h1 h2
    rw [h1] at h2
    exact (cancel_mono _).1 ((cancel_epi _).1 h2).symm |>.symm
  · intro g
    let a : A ⟶ B := ε.inv.app A ≫ (homologyFunctor C n).map eP.inv ≫ g ≫
      (homologyFunctor C n).map eQ.hom ≫ ε.hom.app B
    refine ⟨eP.hom ≫ (singleFunctor C n).map a ≫ eQ.inv, ?_⟩
    simp only
    rw [Functor.map_comp, Functor.map_comp, key]
    simp only [a, assoc, Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, id_comp,
      ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, comp_id]

/-- For `X ≤ n` and `Y ≥ n` in the derived category, `H^n` induces a bijection between
morphisms `X ⟶ Y` and morphisms `H^n X ⟶ H^n Y`: every morphism `X ⟶ Y` factors uniquely
through `τ_{≥ n} X ⟶ τ_{≤ n} Y`, a morphism between objects of the shifted heart:
```
X ──f──▶ Y
│π       ▲ι
▼        │
τ_{≥n}X ─▶ τ_{≤n}Y
```
-/
lemma homologyFunctor_map_bijective_of_isLE_of_isGE {X Y : DerivedCategory C} (n : ℤ)
    [X.IsLE n] [Y.IsGE n] :
    Function.Bijective (fun f : X ⟶ Y ↦ (homologyFunctor C n).map f) := by
  let π := (t.truncGEπ n).app X
  let ι := (t.truncLTι (n + 1)).app Y
  have : IsIso ((homologyFunctor C n).map π) := isIso_homologyFunctor_map_truncGEπ_app X n n le_rfl
  have : IsIso ((homologyFunctor C n).map ι) :=
    isIso_homologyFunctor_map_truncLTι_app Y (n + 1) n (by lia)
  have : ((t.truncGE n).obj X).IsLE n := inferInstance
  have : ((t.truncLT (n + 1)).obj Y).IsGE n := inferInstance
  have hPQ := homologyFunctor_map_bijective_of_isGE_of_isLE
    (P := (t.truncGE n).obj X) (Q := (t.truncLT (n + 1)).obj Y) n
  have fac (f : X ⟶ Y) : f = π ≫ t.liftTruncLT (t.descTruncGE f n) n (n + 1) rfl ≫ ι := by
    simp [π, ι]
  constructor
  · intro f f' h
    simp only at h
    rw [fac f, fac f']
    congr 2
    apply hPQ.1
    simp only
    rw [← cancel_epi ((homologyFunctor C n).map π), ← cancel_mono ((homologyFunctor C n).map ι)]
    simp only [assoc, ← Functor.map_comp]
    rw [← fac f, ← fac f', h]
  · intro g
    obtain ⟨φ, hφ⟩ := hPQ.2 (inv ((homologyFunctor C n).map π) ≫ g ≫
      inv ((homologyFunctor C n).map ι))
    refine ⟨π ≫ φ ≫ ι, ?_⟩
    simp only at hφ ⊢
    simp [hφ]

end Heart

end DerivedCategory
