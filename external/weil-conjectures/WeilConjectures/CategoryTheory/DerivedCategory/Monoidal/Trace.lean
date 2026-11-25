/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.Monoidal.Supertrace
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.CategoryTheory.Monoidal.Rigid.Trace

/-!
# The trace of an endomorphism of a bounded complex of dualizable objects

Let `A` be a braided monoidal closed Grothendieck abelian category with functorial flat
resolutions, and let `P` be a bounded complex of dualizable objects of `A`. The object of `D(A)`
represented by `P` is dualizable (`DerivedCategory.isDualizable_Q_obj`). If the braiding of
`D(A)` is induced by the Koszul braiding of complexes, in the sense that the lax monoidal
structure of `Qh : K(A) ⥤ D(A)` is compatible with the braidings on K-flat complexes, then the
categorical trace in `D(A)` of the image of a chain endomorphism `v` of `P` is the image of the
categorical trace of `v` in the category of complexes, for the termwise dual of `P`
(`DerivedCategory.trace_Qh_map_quotient_map`). The latter is the supertrace
`∑ₚ (-1)ᵖ tr(vᵖ | Pᵖ)` (`CochainComplex.trace_f_zero`).

This is used for blueprint `proposition-properties-trace`, together with
`proposition-properties-trace--4`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]

local instance instHasColimitsOfSize_trace : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A

/-- For the braiding `DerivedCategory.braidedCategory'` of the derived tensor product, the lax
monoidal structure of `Qh : K(A) ⥤ D(A)` is compatible with the Koszul braiding of the homotopy
category and the braiding of `D(A)`. -/
lemma braiding_hom_μ_Qh (X Y : HomotopyCategory A (.up ℤ)) :
    letI := braidedCategory' A
    (β_ (Qh.obj X) (Qh.obj Y)).hom ≫ μ Qh Y X = μ Qh X Y ≫ Qh.map (β_ X Y).hom :=
  DerivedMonoidal.braiding_hom_μ _ _ X Y

/-- Blueprint `proposition-properties-trace` (via `proposition-properties-trace--4`): let `P` be a
bounded complex of dualizable objects and `v : P ⟶ P` a chain map. If the lax monoidal structure of
`Qh : K(A) ⥤ D(A)` is compatible with the Koszul braiding of complexes and the braiding of
`D(A)` on K-flat complexes, then the categorical trace in `D(A)` of the image of `v` is the image
of the categorical trace of `v` in the category of complexes, computed with the termwise dual of
`P` (`CochainComplex.hasRightDual`). The right dual of the image of `P` in `D(A)` is arbitrary. -/
theorem trace_Qh_map_quotient_map [BraidedCategory (DerivedCategory A)]
    (hβ : ∀ X Y : HomotopyCategory A (.up ℤ), (HomotopyCategory.quasiIso A (.up ℤ)).kFlat X →
      (HomotopyCategory.quasiIso A (.up ℤ)).kFlat Y →
        (β_ (Qh.obj X) (Qh.obj Y)).hom ≫ μ Qh Y X = μ Qh X Y ≫ Qh.map (β_ X Y).hom)
    (P : CochainComplex A ℤ) (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ n, HasRightDual (P.X n)]
    [HasRightDual (Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj P))] (v : P ⟶ P) :
    letI := CochainComplex.hasRightDual P a b
    trace (Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map v)) =
      ε Qh ≫ Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map (trace v)) ≫ inv (ε Qh) := by
  let := CochainComplex.hasRightDual P a b
  let := CochainComplex.exactPairingRightDual P a b
  let H := HomotopyCategory.quotient A (.up ℤ)
  have hP' : ∀ n, IsDualizable (P.rightDual.X n) := fun n ↦
    ⟨{ rightDual := P.X (-n)
       exact := (BraidedCategory.exactPairing_swap (P.X (-n)) (P.X (-n))ᘁ :) }⟩
  let X : (HomotopyCategory.quasiIso A (.up ℤ)).kFlat.FullSubcategory :=
    ⟨H.obj P, (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (CochainComplex.kFlat_of_bounded_of_flat P a b
        (fun n ↦ (isDualizable_of_hasRightDual _).flat))⟩
  let Y : (HomotopyCategory.quasiIso A (.up ℤ)).kFlat.FullSubcategory :=
    ⟨H.obj P.rightDual, (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (CochainComplex.kFlat_of_bounded_of_flat P.rightDual (-b) (-a) (fun n ↦ (hP' n).flat))⟩
  -- the trace in the homotopy category
  let e₁ : ExactPairing (H.obj P) (H.obj P.rightDual) := ExactPairing.map H P P.rightDual
  let d₁ : HasRightDual (H.obj P) := ⟨H.obj P.rightDual⟩
  have h₁ : trace (H.map v) = ε H ≫ H.map (trace v) ≫ η H :=
    trace_map H ((Category.id_comp _).trans (Category.comp_id _).symm) v
  -- the trace in the full subcategory of K-flat complexes
  let : ExactPairing ((ObjectProperty.ι _).obj X) ((ObjectProperty.ι _).obj Y) := e₁
  let : ExactPairing X Y := ExactPairing.ofFullyFaithful (ObjectProperty.ι _) X Y
  let : HasRightDual X := ⟨Y⟩
  let f : X ⟶ X := ObjectProperty.homMk (H.map v)
  let : HasRightDual ((ObjectProperty.ι _).obj X) := d₁
  have h₂ := trace_map (ObjectProperty.ι _) (Functor.Braided.braided X Y) f
  -- the trace in the derived category
  let := Functor.Monoidal.ofLaxMonoidal (kFlatQh A)
  let : HasRightDual ((kFlatQh A).obj X) :=
    ‹HasRightDual (Qh.obj ((HomotopyCategory.quotient A (.up ℤ)).obj P))›
  have hF : μ (kFlatQh A) X Y ≫ (kFlatQh A).map (β_ X Y).hom =
      (β_ ((kFlatQh A).obj X) ((kFlatQh A).obj Y)).hom ≫ μ (kFlatQh A) Y X := by
    rw [comp_μ, comp_μ, ObjectProperty.ι_μ, ObjectProperty.ι_μ, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id,
      Category.comp_id, Category.comp_id]
    exact (hβ X.obj Y.obj X.property Y.property).symm
  have h₃ := trace_map (kFlatQh A) (X := X) hF f
  have h₄ : (ObjectProperty.ι _).map (trace f) = H.map (trace v) := by
    have h := h₂.symm.trans h₁
    erw [Category.id_comp, Category.comp_id, Category.id_comp, Category.comp_id] at h
    exact h
  have hε : ε (kFlatQh A) = ε Qh := by
    rw [comp_ε, ObjectProperty.ι_ε, CategoryTheory.Functor.map_id, Category.comp_id]
  have hη : η (kFlatQh A) = inv (ε Qh) := by
    refine IsIso.eq_inv_of_hom_inv_id ?_
    rw [← hε]
    exact Functor.Monoidal.ε_η _
  refine h₃.trans ?_
  rw [hε, hη, Functor.comp_map, h₄]

end DerivedCategory
