/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.TruncationCouple
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! Canonical truncation-couple proof step. -/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Transport an exact pair along three object isomorphisms. -/
private theorem exact_transport
    {C : Type*} [Category C] [Abelian C]
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃)
    (w : a ≫ b = 0) (h : (ShortComplex.mk a b w).Exact)
    {a' : Y₁ ⟶ Y₂} {b' : Y₂ ⟶ Y₃}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃)
    (h₁ : e₁.hom ≫ a' = a ≫ e₂.hom)
    (h₂ : e₂.hom ≫ b' = b ≫ e₃.hom) :
    ∃ w' : a' ≫ b' = 0, (ShortComplex.mk _ _ w').Exact := by
  have w' : a' ≫ b' = 0 := by
    rw [← cancel_epi e₁.hom, ← Category.assoc, h₁, Category.assoc, h₂,
      ← Category.assoc, w, zero_comp, comp_zero]
  refine ⟨w', ShortComplex.exact_of_iso ?_ h⟩
  exact ShortComplex.isoMk e₁ e₂ e₃ h₁ h₂

/-- Naturality of an indexed morphism with respect to equality transports. -/
private theorem cast_naturality
    {C : Type*} [Category C] {I : Type*} (X Y : I → C)
    (f : ∀ i, X i ⟶ Y i) {i j : I} (h : i = j) :
    eqToHom (congrArg X h) ≫ f j = f i ≫ eqToHom (congrArg Y h) := by
  subst j
  simp

/-- Naturality with a common target, including its final equality transports. -/
private theorem cast_naturality_last
    {C : Type*} [Category C] {I : Type*} (X Y : I → C)
    (f : ∀ i, X i ⟶ Y i) {i j : I} (h : i = j) {Z : C}
    (hi : Y i = Z) (hj : Y j = Z) :
    eqToHom (congrArg X h) ≫ f j ≫ eqToHom hj = f i ≫ eqToHom hi := by
  subst j
  simp

/-- Reindex a family of morphisms along equalities of the two indices. -/
private theorem reindex_hom
    {C : Type*} [Category C] (X Y : ℤ → ℤ → C)
    (f : ∀ p q, X p q ⟶ Y p q) {p q p' q' : ℤ}
    (hp : p = p') (hq : q = q') :
    eqToHom (congrArg₂ X hp hq) ≫ f p' q' =
      f p q ≫ eqToHom (congrArg₂ Y hp hq) := by
  subst p'
  subst q'
  simp

/-- Adding the zero bidegree does not change an exact pair. -/
private theorem exact_zero_right
    {C : Type*} [Category C] [Abelian C] (D E : ℤ → ℤ → C)
    (g : ∀ p q, D p q ⟶ E p q)
    (f : ∀ p q, E p q ⟶ D (p + 2) (q - 1)) (p q : ℤ)
    (h : ∃ w : g p q ≫ f p q = 0, (ShortComplex.mk _ _ w).Exact) :
    ∃ w : (g p q ≫ eqToHom (by simp : E p q = E (p + (0 : ℕ)) (q - (0 : ℕ)))) ≫
        f (p + (0 : ℕ)) (q - (0 : ℕ)) = 0,
      (ShortComplex.mk _ _ w).Exact := by
  obtain ⟨w, h⟩ := h
  refine exact_transport _ _ w h (Iso.refl _) (eqToIso ?_) (eqToIso ?_) ?_ ?_
  · simp
  · simp
  · simp
  · exact reindex_hom E (fun p q ↦ D (p + 2) (q - 1)) f
      (by simp) (by simp)

/-- Postcomposing the last map with an equality isomorphism preserves exactness. -/
private theorem exact_cast_last
    {C : Type*} [Category C] [Abelian C] {X Y Z Z' : C}
    (a : X ⟶ Y) (b : Y ⟶ Z)
    (h : ∃ w : a ≫ b = 0, (ShortComplex.mk _ _ w).Exact) (hz : Z = Z') :
    ∃ w : a ≫ (b ≫ eqToHom hz) = 0, (ShortComplex.mk _ _ w).Exact := by
  obtain ⟨w, h⟩ := h
  exact exact_transport a b w h (Iso.refl _) (Iso.refl _) (eqToIso hz)
    (by simp) (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Exactness of the raw truncation maps for arbitrary derived-category instances.
Source: Stacks Tags 08J5, 05SE, 0148, 011Q; blueprint step 1 of
lemma-uniform-bound-proper-direct-image--1 (blueprint: lem-sp-truncation-raw-exact).

Proof: The triangle tau<=q-1 K -> tau<=q K -> H^q(K)[-q] with the boundary
chosen by `TruncationCouple.existsUnique_boundary` is distinguished. Apply the
triangulated right derived functor and its homology sequence. Transport exactness
across the three bridge isomorphisms. The g-f and f-alpha pairs use the triangle at q,
in total degrees p+q
and p+q+1 respectively; the alpha-g pair uses the triangle at q+1, in total
degree p+q.
The index identities preserve total degree, and transport of exact short complexes
preserves both their zero composites and their image-equals-kernel condition. -/
theorem truncation_raw_exact
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [IsGrothendieckAbelian.{v₁} A] [HasDerivedCategory.{w₁} A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [IsGrothendieckAbelian.{v₂} B] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) :
    let g : ∀ p q : ℤ, TruncationCouple.D F K p q ⟶
        TruncationCouple.E F K (p + (0 : ℕ)) (q - (0 : ℕ)) :=
      fun p q ↦ TruncationCouple.g F K p q ≫ eqToHom (by simp)
    (∀ p q : ℤ,
      ∃ w : TruncationCouple.f F K p q ≫
          TruncationCouple.alpha F K (p + 2) (q - 1) = 0,
        (ShortComplex.mk _ _ w).Exact) ∧
    (∀ p q : ℤ,
      ∃ w : g p q ≫ TruncationCouple.f F K (p + (0 : ℕ)) (q - (0 : ℕ)) = 0,
        (ShortComplex.mk _ _ w).Exact) ∧
    (∀ p q : ℤ,
      ∃ w : TruncationCouple.alpha F K p q ≫ g (p - 1) (q + 1) = 0,
        (ShortComplex.mk _ _ w).Exact) := by
  dsimp only
  have hT (q : ℤ) : TruncationCouple.derivedTriangle F K q ∈
      Pretriangulated.distinguishedTriangles := by
    apply F.rightDerivedFunctor.map_distinguished
    exact (Classical.choose_spec (TruncationCouple.existsUnique_boundary K q)).1
  refine ⟨?_, ?_, ?_⟩
  · intro p q
    have h := DerivedCategory.HomologySequence.exact₁
      (TruncationCouple.derivedTriangle F K q) (hT q) (p + q) (p + q + 1)
    refine exact_transport _ _ _ h
      (TruncationCouple.bridgeIso F (TruncationCouple.cohomologyComplex K q) (p + q))
      (TruncationCouple.bridgeIso F (TruncationCouple.truncation K (q - 1))
        (p + q + 1) ≪≫ eqToIso ?_)
      (TruncationCouple.bridgeIso F (TruncationCouple.truncation K q)
        (p + q + 1) ≪≫ eqToIso ?_) ?_ ?_
    · unfold TruncationCouple.D
      congr 1
      omega
    · unfold TruncationCouple.D
      rw [sub_add_cancel]
      congr 1
      omega
    · simp [TruncationCouple.f]
    · simp only [TruncationCouple.derivedTriangle, TruncationCouple.triangle,
        Functor.mapTriangle_obj, Pretriangulated.Triangle.mk_obj₁,
        Pretriangulated.Triangle.mk_obj₂, Pretriangulated.Triangle.mk_obj₃,
        Pretriangulated.Triangle.mk_mor₁, Pretriangulated.Triangle.mk_mor₂,
        Pretriangulated.Triangle.mk_mor₃, Iso.trans_hom,
        eqToIso.hom, TruncationCouple.alpha, Functor.map_comp, eqToHom_map, Category.assoc]
      rw [eqToHom_iso_hom_naturality_assoc
        (fun n ↦ TruncationCouple.bridgeIso F (TruncationCouple.truncation K (q - 1)) n)
        (by omega : p + q + 1 = p + 2 + (q - 1))]
      simp only [Iso.hom_inv_id_assoc, eqToHom_trans_assoc]
      simpa only [Category.assoc] using
        cast_naturality_last
        (fun rn : ℤ × ℤ ↦ (DerivedCategory.homologyFunctor B rn.2).obj
          (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj
            (TruncationCouple.truncation K (rn.1 - 1)).obj)))
        (fun rn : ℤ × ℤ ↦ F.rightDerivedCohomologyWithResolution
          (TruncationCouple.truncation K rn.1)
          (CochainComplex.grothendieckKInjectiveResolutionChoice.{v₁}
            (TruncationCouple.truncation K rn.1).obj) rn.2)
        (fun rn ↦ (DerivedCategory.homologyFunctor B rn.2).map
          (F.rightDerivedFunctor.map (DerivedCategory.Q.map
            (TruncationCouple.transition K rn.1))) ≫
          (TruncationCouple.bridgeIso F (TruncationCouple.truncation K rn.1) rn.2).hom)
        (by ext <;> omega : (q, p + q + 1) = (q - 1 + 1, p + 2 + (q - 1)))
        (Z := TruncationCouple.D F K (p + 2 - 1) (q - 1 + 1))
        (by
          dsimp only
          unfold TruncationCouple.D
          rw [sub_add_cancel]
          congr 1
          omega)
        (by
          dsimp only
          unfold TruncationCouple.D
          congr 1
          omega)
  · intro p q
    have h := DerivedCategory.HomologySequence.exact₃
      (TruncationCouple.derivedTriangle F K q) (hT q) (p + q) (p + q + 1)
    apply exact_zero_right (TruncationCouple.D F K) (TruncationCouple.E F K)
      (TruncationCouple.g F K) (TruncationCouple.f F K)
    refine exact_transport _ _ _ h
      (TruncationCouple.bridgeIso F (TruncationCouple.truncation K q) (p + q))
      (TruncationCouple.bridgeIso F (TruncationCouple.cohomologyComplex K q) (p + q))
      (TruncationCouple.bridgeIso F (TruncationCouple.truncation K (q - 1))
        (p + q + 1) ≪≫ eqToIso ?_) ?_ ?_
    · unfold TruncationCouple.D
      congr 1
      omega
    · simp [TruncationCouple.g]
    · simp [TruncationCouple.f]
  · intro p q
    apply exact_cast_last
    have h := DerivedCategory.HomologySequence.exact₂
      (TruncationCouple.derivedTriangle F K (q + 1)) (hT (q + 1)) (p + q)
    refine exact_transport _ _ _ h
      (eqToIso ?_ ≪≫
        TruncationCouple.bridgeIso F (TruncationCouple.truncation K q) (p + q))
      (TruncationCouple.bridgeIso F (TruncationCouple.truncation K (q + 1))
        (p + q) ≪≫ eqToIso ?_)
      (TruncationCouple.bridgeIso F (TruncationCouple.cohomologyComplex K (q + 1))
        (p + q) ≪≫ eqToIso ?_) ?_ ?_
    · exact congrArg (fun r ↦ (DerivedCategory.homologyFunctor B (p + q)).obj
        (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj
          (TruncationCouple.truncation K r).obj))) (by omega : (q + 1) - 1 = q)
    · unfold TruncationCouple.D
      congr 1
      omega
    · unfold TruncationCouple.E
      congr 1
      omega
    · dsimp only [TruncationCouple.alpha, Iso.trans_hom, eqToIso.hom,
        TruncationCouple.derivedTriangle, TruncationCouple.triangle, Functor.mapTriangle]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp,
        eqToHom_map, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        Pretriangulated.Triangle.mk_mor₁]
    · simp only [Iso.trans_hom, eqToIso.hom, sub_add_add_cancel,
        eqToHom_iso_hom_naturality, TruncationCouple.g, Category.assoc,
        Iso.hom_inv_id_assoc, Iso.cancel_iso_hom_right_assoc]
      exact cast_naturality
        (fun n ↦ (DerivedCategory.homologyFunctor B n).obj
          (TruncationCouple.derivedTriangle F K (q + 1)).obj₂)
        (fun n ↦ (DerivedCategory.homologyFunctor B n).obj
          (TruncationCouple.derivedTriangle F K (q + 1)).obj₃)
        (fun n ↦ (DerivedCategory.homologyFunctor B n).map
          (TruncationCouple.derivedTriangle F K (q + 1)).mor₂) (by omega)

end CategoryTheory
