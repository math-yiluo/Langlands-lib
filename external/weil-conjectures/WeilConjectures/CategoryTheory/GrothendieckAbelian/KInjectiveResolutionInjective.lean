/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Double
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-!
# The functorial K-injective resolutions have injective components

Let `C` be a Grothendieck abelian category. A cochain complex `I` such that `I ⟶ 0` has the right
lifting property with respect to all monomorphic quasi-isomorphisms has injective components:
for `X : C`, maps `double (𝟙 X) ⟶ I` out of the acyclic complex `X ⟶ X` placed in degrees
`n, n + 1` are the maps `X ⟶ I.X n`, and `double (𝟙 -)` sends monomorphisms to monomorphic
quasi-isomorphisms. In particular the functorial K-injective resolution
`CochainComplex.kInjectiveResolutionFunctor` is degreewise injective.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MorphismProperty HomologicalComplex ZeroObject

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The complex `X ⟶ X` (the identity) placed in degrees `n` and `n + 1`. -/
noncomputable abbrev doubleId (X : C) (n : ℤ) : CochainComplex C ℤ :=
  double (𝟙 X) (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)

lemma isZero_doubleId_X (X : C) (n k : ℤ) (h₀ : k ≠ n) (h₁ : k ≠ n + 1) :
    IsZero ((doubleId X n).X k) :=
  isZero_double_X _ _ k h₀ h₁

lemma doubleId_acyclic (X : C) (n : ℤ) : (doubleId X n).Acyclic := by
  have hn : n ≠ n + 1 := by lia
  intro i
  by_cases h₀ : i = n
  · subst h₀
    rw [exactAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
    refine (ShortComplex.exact_iff_mono _ ?_).2 ?_
    · exact (isZero_doubleId_X _ _ _ (by lia) (by lia)).eq_of_src _ _
    · change Mono ((doubleId X i).d i (i + 1))
      rw [double_d _ _ hn]
      infer_instance
  by_cases h₁ : i = n + 1
  · subst h₁
    rw [exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp)]
    refine (ShortComplex.exact_iff_epi _ ?_).2 ?_
    · exact (isZero_doubleId_X _ _ _ (by lia) (by lia)).eq_of_tgt _ _
    · change Epi ((doubleId X n).d n (n + 1))
      rw [double_d _ _ hn]
      infer_instance
  · rw [exactAt_iff]
    exact ShortComplex.exact_of_isZero_X₂ _ (isZero_doubleId_X _ _ _ h₀ h₁)

/-- The map of disks induced by a morphism `g : X ⟶ Y`. -/
noncomputable def doubleIdMap {X Y : C} (g : X ⟶ Y) (n : ℤ) : doubleId X n ⟶ doubleId Y n :=
  mkHomFromDouble _ (by lia) (g ≫ (doubleXIso₀ _ _).inv) (g ≫ (doubleXIso₁ _ _ (by lia)).inv)
    (by simp [double_d _ _ (show n ≠ n + 1 by lia)])
    (fun k hk ↦ by
      obtain rfl : k = n + 1 + 1 := by simpa using hk.symm
      exact (isZero_doubleId_X _ _ _ (by lia) (by lia)).eq_of_tgt _ _)

lemma mono_doubleIdMap {X Y : C} (g : X ⟶ Y) [Mono g] (n : ℤ) : Mono (doubleIdMap g n) := by
  refine mono_of_mono_f _ fun k ↦ ?_
  by_cases h₀ : k = n
  · subst h₀
    rw [doubleIdMap, mkHomFromDouble_f₀]
    infer_instance
  by_cases h₁ : k = n + 1
  · subst h₁
    rw [doubleIdMap, mkHomFromDouble_f₁]
    infer_instance
  · exact (isZero_doubleId_X _ _ _ h₀ h₁).mono _

lemma quasiIso_doubleIdMap {X Y : C} (g : X ⟶ Y) (n : ℤ) : QuasiIso (doubleIdMap g n) where
  quasiIsoAt k := by
    rw [quasiIsoAt_iff_exactAt _ _ (doubleId_acyclic X n k)]
    exact doubleId_acyclic Y n k

variable (C) in
/-- A cochain complex `I` such that `I ⟶ 0` has the right lifting property with respect to all
monomorphic quasi-isomorphisms has injective components. -/
lemma injective_X_of_rlp {I Z : CochainComplex C ℤ} (p : I ⟶ Z) (hZ : IsZero Z)
    (hp : (monoQuasiIso C (ComplexShape.up ℤ)).rlp p) (n : ℤ) : Injective (I.X n) where
  factors {X Y} f g _ := by
    let e := fun W : C ↦ evalCompCoyonedaCorepresentableByDoubleId
      (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl) (by lia) W
    have := hp (doubleIdMap g n) ⟨mono_doubleIdMap g n, quasiIso_doubleIdMap g n⟩
    have sq : CommSq ((e X).homEquiv.symm f) (doubleIdMap g n) p 0 := ⟨hZ.eq_of_tgt _ _⟩
    refine ⟨(e Y).homEquiv sq.lift, ?_⟩
    have h := congr_arg (fun φ ↦ (doubleXIso₀ _ _).inv ≫ HomologicalComplex.Hom.f φ n)
      sq.fac_left
    simp only [e, evalCompCoyonedaCorepresentableByDoubleId_homEquiv_apply,
      evalCompCoyonedaCorepresentableByDoubleId_homEquiv_symm_apply, comp_f, doubleIdMap,
      mkHomFromDouble_f₀, Category.assoc, Iso.inv_hom_id_assoc] at h ⊢
    exact h

/-- The functorial K-injective resolution of a complex in a Grothendieck abelian category has
injective components. -/
instance injective_kInjectiveResolutionFunctor_obj_X [IsGrothendieckAbelian.{w} C]
    (K : CochainComplex C ℤ) (n : ℤ) :
    Injective (((kInjectiveResolutionFunctor.{w} C).obj K).X n) :=
  injective_X_of_rlp C _ (isZero_zero _) ((functorialFactorizationData _ _).hp _) n

end CochainComplex
