/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
public import WeilConjectures.CategoryTheory.Triangulated.FullyFaithfulGenerator

/-!
# Functors out of a rationalization

Let `C` be an `R`-linear triangulated category, `M` a submonoid of `R` and `A` a localization of
`R` at `M`. A triangulated functor `Φ : C ⥤ D` to an `A`-linear pretriangulated category which
sends the multiplication by `r` to the multiplication by its image in `A` kills the `M`-torsion
objects, hence factors through the rationalization: `Rationalization.lift M A Φ`.

On morphisms between objects of `C`, the induced functor is bijective as soon as `Φ` is so up to
`M`, i.e. as soon as the map `Hom(X, Y) ⟶ Hom(Φ X, Φ Y)` is a localization at `M`
(`CategoryTheory.Rationalization.homBijective_lift_obj`). Its hypotheses are the predicate
`CategoryTheory.Rationalization.LocHomBijective`, which is stable under isomorphisms and
under precomposition with fully faithful linear functors.
-/

@[expose] public section

universe w w' v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Category Limits Pretriangulated

namespace CategoryTheory.Rationalization

variable {R : Type w} [CommRing R] (M : Submonoid R) (A : Type w') [CommRing A] [Algebra R A]

section LocHomBijective

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear A D] (Φ : C ⥤ D)

/-- The functor `Φ` induces a bijection on morphisms `X ⟶ Y` up to `M`: a morphism killed by
`Φ` is killed by an element of `M`, and every morphism `Φ X ⟶ Φ Y` becomes the image of a
morphism after multiplication by an element of `M`. -/
def LocHomBijective (X Y : C) : Prop :=
  (∀ f : X ⟶ Y, Φ.map f = 0 → ∃ m ∈ M, m • f = 0) ∧
    ∀ g : Φ.obj X ⟶ Φ.obj Y, ∃ m ∈ M, ∃ f : X ⟶ Y, Φ.map f = algebraMap R A m • g

variable {M A Φ}

lemma LocHomBijective.of_iso {X Y X' Y' : C} (h : LocHomBijective M A Φ X Y) (e : X ≅ X')
    (e' : Y ≅ Y') : LocHomBijective M A Φ X' Y' := by
  refine ⟨fun f hf ↦ ?_, fun g ↦ ?_⟩
  · obtain ⟨m, hm, h₁⟩ := h.1 (e.hom ≫ f ≫ e'.inv) (by simp [hf])
    refine ⟨m, hm, ?_⟩
    have := congr_arg (fun t ↦ e.inv ≫ t ≫ e'.hom) h₁
    simpa using this
  · obtain ⟨m, hm, f, hf⟩ := h.2 (Φ.map e.hom ≫ g ≫ Φ.map e'.inv)
    refine ⟨m, hm, e.inv ≫ f ≫ e'.hom, ?_⟩
    rw [Functor.map_comp, Functor.map_comp, hf, Linear.smul_comp, Linear.comp_smul]
    congr 1
    simp

/-- Precomposition with a fully faithful `R`-linear functor. -/
lemma LocHomBijective.of_comp {B : Type u₃} [Category.{v₃} B] [Preadditive B] [Linear R B]
    (J : B ⥤ C) [J.Full] [J.Faithful] [J.Linear R] {X Y : B}
    (h : LocHomBijective M A Φ (J.obj X) (J.obj Y)) : LocHomBijective M A (J ⋙ Φ) X Y := by
  refine ⟨fun f hf ↦ ?_, fun g ↦ ?_⟩
  · obtain ⟨m, hm, h₁⟩ := h.1 (J.map f) hf
    exact ⟨m, hm, J.map_injective (by rw [Functor.map_smul, h₁, Functor.map_zero])⟩
  · obtain ⟨m, hm, f, hf⟩ := h.2 g
    exact ⟨m, hm, J.preimage f, by simpa using hf⟩

end LocHomBijective

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [Pretriangulated C] [IsTriangulated C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear A D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsLocalization M A] (Φ : C ⥤ D) [Φ.CommShift ℤ] [Φ.IsTriangulated]
  (hΦ : ∀ (r : R) (X : C), Φ.map (r • 𝟙 X) = algebraMap R A r • 𝟙 (Φ.obj X))

omit [∀ n : ℤ, (shiftFunctor C n).Linear R] [IsTriangulated C] in
include hΦ in
/-- A functor sending the multiplication by `r` to the multiplication by its image in `A` kills
the `M`-torsion objects. -/
lemma isZero_obj_of_torsion {Z : C} (hZ : torsion M C Z) : IsZero (Φ.obj Z) := by
  obtain ⟨m, hm, hZ⟩ := hZ
  have h := hΦ m Z
  rw [hZ, Φ.map_zero] at h
  have hu := IsLocalization.map_units A (⟨m, hm⟩ : M)
  rw [IsZero.iff_id_eq_zero]
  calc 𝟙 (Φ.obj Z) = ((hu.unit⁻¹ : Aˣ) : A) • (algebraMap R A m • 𝟙 (Φ.obj Z)) := by
        rw [smul_smul, IsUnit.val_inv_mul, one_smul]
    _ = 0 := by rw [← h, smul_zero]

omit [∀ n : ℤ, (shiftFunctor C n).Linear R] [IsTriangulated C] in
include hΦ in
lemma isInvertedBy_W : (W M C).IsInvertedBy Φ := fun X Y f hf ↦ by
  obtain ⟨Z, g, h, hT, hZ⟩ := hf
  exact (Triangle.isZero₃_iff_isIso₁ _ (Φ.map_distinguished _ hT)).1
    (isZero_obj_of_torsion M A Φ hΦ hZ)

/-- The functor `Rationalization M C ⥤ D` induced by a triangulated functor `Φ : C ⥤ D` sending
the multiplication by `r` to the multiplication by its image in `A`. -/
noncomputable def lift : Rationalization M C ⥤ D :=
  Localization.lift Φ (isInvertedBy_W M A Φ hΦ) (Q M C)

/-- The functor induced on the rationalization is compatible with `Φ`. -/
noncomputable def liftFac : Q M C ⋙ lift M A Φ hΦ ≅ Φ :=
  Localization.fac _ _ _

noncomputable instance : Localization.Lifting (Q M C) (W M C) Φ (lift M A Φ hΦ) :=
  ⟨liftFac M A Φ hΦ⟩

noncomputable instance : (lift M A Φ hΦ).CommShift ℤ :=
  Functor.commShiftOfLocalization (Q M C) (W M C) ℤ Φ (lift M A Φ hΦ)

instance : NatTrans.CommShift (liftFac M A Φ hΦ).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization (Q M C) (W M C) ℤ Φ (lift M A Φ hΦ)

instance : (lift M A Φ hΦ).IsTriangulated := by
  have := Localization.essSurj_mapArrow (Q M C) (W M C)
  exact Functor.isTriangulated_of_precomp_iso (liftFac M A Φ hΦ)

omit [∀ n : ℤ, (shiftFunctor C n).Linear R] [IsTriangulated C] in
lemma lift_map_Q_map {X Y : C} (f : X ⟶ Y) :
    (lift M A Φ hΦ).map ((Q M C).map f) =
      (liftFac M A Φ hΦ).hom.app X ≫ Φ.map f ≫ (liftFac M A Φ hΦ).inv.app Y := by
  simp

/-- The multiplication by a scalar is invariant under conjugation by isomorphisms. -/
lemma smul_id_conj {𝕜 : Type*} [Semiring 𝕜] {E : Type*} [Category E] [Preadditive E]
    [Linear 𝕜 E] {X Y : E} (e : X ≅ Y) (c : 𝕜) : e.inv ≫ (c • 𝟙 X) ≫ e.hom = c • 𝟙 Y := by
  simp

lemma lift_map_smul_id (r : R) (X : Rationalization M C) :
    (lift M A Φ hΦ).map (r • 𝟙 X) = algebraMap R A r • 𝟙 _ := by
  let e := (Q M C).objObjPreimageIso X
  have key : (lift M A Φ hΦ).map ((Q M C).map (r • 𝟙 ((Q M C).objPreimage X))) =
      algebraMap R A r • 𝟙 _ := by
    rw [lift_map_Q_map, hΦ]
    simp
  rw [← smul_id_conj e r, Functor.map_comp, Functor.map_comp, ← (Q M C).map_id,
    ← Functor.map_smul, key]
  simp

/-- The induced functor is bijective on morphisms between objects of `C` on which `Φ` is
bijective up to `M`. -/
lemma homBijective_lift_obj {X Y : C} (h : LocHomBijective M A Φ X Y) :
    (lift M A Φ hΦ).HomBijective ((Q M C).obj X) ((Q M C).obj Y) := by
  let eX : (lift M A Φ hΦ).obj ((Q M C).obj X) ≅ Φ.obj X := (liftFac M A Φ hΦ).app X
  let eY : (lift M A Φ hΦ).obj ((Q M C).obj Y) ≅ Φ.obj Y := (liftFac M A Φ hΦ).app Y
  have hQ {f : X ⟶ Y} : (lift M A Φ hΦ).map ((Q M C).map f) = eX.hom ≫ Φ.map f ≫ eY.inv :=
    lift_map_Q_map M A Φ hΦ f
  refine ⟨fun φ ψ hφψ ↦ ?_, fun g ↦ ?_⟩
  · rw [← sub_eq_zero]
    have hz : (lift M A Φ hΦ).map (φ - ψ) = 0 := by simp [hφψ]
    obtain ⟨m, hm, f, hf⟩ := exists_smul_eq_map (φ - ψ)
    have h₀ : (lift M A Φ hΦ).map ((Q M C).map f) = 0 := by
      rw [← hf, ← id_comp (φ - ψ), ← Linear.smul_comp, Functor.map_comp, hz, comp_zero]
    have : Φ.map f = 0 := by
      have := congr_arg (fun t ↦ eX.inv ≫ t ≫ eY.hom) h₀
      simpa [hQ] using this
    obtain ⟨m', hm', hf'⟩ := h.1 f this
    refine smul_left_injective (M.mul_mem hm' hm) ?_
    change (m' * m) • (φ - ψ) = (m' * m) • 0
    rw [smul_zero, mul_smul, hf, ← Functor.map_smul, hf', Functor.map_zero]
  · obtain ⟨m, hm, f, hf⟩ := h.2 (eX.inv ≫ g ≫ eY.hom)
    have := isIso_smul_id hm ((Q M C).obj X)
    refine ⟨inv (m • 𝟙 ((Q M C).obj X)) ≫ (Q M C).map f, ?_⟩
    rw [Functor.map_comp, Functor.map_inv, IsIso.inv_comp_eq, lift_map_smul_id, hQ, hf]
    simp

end CategoryTheory.Rationalization
