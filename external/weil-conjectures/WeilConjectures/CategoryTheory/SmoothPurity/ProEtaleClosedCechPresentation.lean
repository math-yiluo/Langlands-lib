/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedCechDegreeCorepresenter

/-! # Ambient corepresenters for closed Čech cochains

Source: the free-module construction in the affine matching-relations step of
`lem-sp-proetale-closed-injective-affine-cech`.
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Three consecutive degrees of a cochain functor, corepresented naturally by a
short complex. The order of the objects reverses because Hom is contravariant
in its first argument. No exactness is part of this universal property. -/
structure CochainCorepresentingShortComplex
    {C : Type u} [Category.{v} C] [Preadditive C]
    {R : Type w} [Ring R] (H : C ⥤ CochainComplex (ModuleCat.{v} R) ℕ)
    (q : ℕ) where
  complex : ShortComplex C
  first : ∀ M : C, (complex.X₁ ⟶ M) ≃+ (H.obj M).X (q + 2)
  middle : ∀ M : C, (complex.X₂ ⟶ M) ≃+ (H.obj M).X (q + 1)
  last : ∀ M : C, (complex.X₃ ⟶ M) ≃+ (H.obj M).X q
  first_natural : ∀ {M N : C} (f : M ⟶ N) (g : complex.X₁ ⟶ M),
    first N (g ≫ f) = (H.map f).f (q + 2) (first M g)
  middle_natural : ∀ {M N : C} (f : M ⟶ N) (g : complex.X₂ ⟶ M),
    middle N (g ≫ f) = (H.map f).f (q + 1) (middle M g)
  last_natural : ∀ {M N : C} (f : M ⟶ N) (g : complex.X₃ ⟶ M),
    last N (g ≫ f) = (H.map f).f q (last M g)
  first_boundary : ∀ (M : C) (g : complex.X₂ ⟶ M),
    first M (complex.f ≫ g) = (H.obj M).d (q + 1) (q + 2) (middle M g)
  last_boundary : ∀ (M : C) (g : complex.X₃ ⟶ M),
    middle M (complex.g ≫ g) = (H.obj M).d q (q + 1) (last M g)

end CategoryTheory

namespace CategoryTheory
namespace CochainDegreeCorepresenter

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {R : Type w} [Ring R] {H : C ⥤ CochainComplex (ModuleCat.{v} R) ℕ}

private noncomputable def boundary {i j : ℕ}
    (E : CochainDegreeCorepresenter H i) (F : CochainDegreeCorepresenter H j) :
    F.object ⟶ E.object :=
  (F.equiv E.object).symm ((H.obj E.object).d i j (E.equiv E.object (𝟙 E.object)))

private theorem boundary_equiv {i j : ℕ}
    (E : CochainDegreeCorepresenter H i) (F : CochainDegreeCorepresenter H j)
    (M : C) (g : E.object ⟶ M) :
    F.equiv M (boundary E F ≫ g) = (H.obj M).d i j (E.equiv M g) := by
  rw [F.natural]
  dsimp only [boundary]
  rw [AddEquiv.apply_symm_apply]
  have h := (ConcreteCategory.congr_hom ((H.map g).comm i j)
    (E.equiv E.object (𝟙 E.object))).symm
  change (H.map g).f j ((H.obj E.object).d i j _) =
    (H.obj M).d i j ((H.map g).f i (E.equiv E.object (𝟙 E.object))) at h
  rw [h, ← E.natural, Category.id_comp]

/-- Yoneda transposes two consecutive differentials into an actual short complex.
All face compatibility is proved from naturality; no exactness is used. -/
private noncomputable def shortComplex {q : ℕ}
    (E₀ : CochainDegreeCorepresenter H q)
    (E₁ : CochainDegreeCorepresenter H (q + 1))
    (E₂ : CochainDegreeCorepresenter H (q + 2)) :
    CochainCorepresentingShortComplex H q where
  complex := ShortComplex.mk (boundary E₁ E₂) (boundary E₀ E₁) (by
    apply (E₂.equiv E₀.object).injective
    rw [map_zero, boundary_equiv]
    dsimp only [boundary]
    rw [AddEquiv.apply_symm_apply]
    exact ConcreteCategory.congr_hom ((H.obj E₀.object).d_comp_d q (q + 1) (q + 2))
      (E₀.equiv E₀.object (𝟙 _)))
  first := E₂.equiv
  middle := E₁.equiv
  last := E₀.equiv
  first_natural := E₂.natural
  middle_natural := E₁.natural
  last_natural := E₀.natural
  first_boundary := boundary_equiv E₁ E₂
  last_boundary := boundary_equiv E₀ E₁

end CochainDegreeCorepresenter
end CategoryTheory

namespace AlgebraicGeometry.Scheme
attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- The degreewise universal properties determine both adjacent boundary maps.

Source: the free-module construction in Step 3 of
`lem-sp-proetale-closed-injective-affine-cech`.
(blueprint: lem-sp-proetale-closed-cech-presentation).

Proof: choose the three degreewise corepresenters. Transpose each differential
by evaluating it at the identity of the preceding corepresenter. Naturality of
the universal properties proves compatibility with every coefficient sheaf.
Applying the degree-q+2 universal property to the composite boundary identifies
it with the composite of the two Čech differentials, which is zero. Thus the
transposed arrows form a short complex. This only uses universal properties and
asserts no exactness. The same argument includes zero corepresenters. -/
theorem exists_closedCech_corepresentingShortComplex
    (A : Type u) [CommRing A] {B O : Scheme.{u}}
    (b : O ⟶ B) [IsOpenImmersion b] [QuasiCompact b]
    (P : B.ProEt) (V : P.left.ProEt) {n : ℕ} (U : Fin n → Over V) (q : ℕ) :
    Nonempty (CochainCorepresentingShortComplex
      (closedCechCoefficientFunctor A b P V U) q) := by
  obtain ⟨E₀⟩ := exists_closedCech_degreeCorepresenter A b P V U q
  obtain ⟨E₁⟩ := exists_closedCech_degreeCorepresenter A b P V U (q + 1)
  obtain ⟨E₂⟩ := exists_closedCech_degreeCorepresenter A b P V U (q + 2)
  exact ⟨E₀.shortComplex E₁ E₂⟩

end AlgebraicGeometry.Scheme
