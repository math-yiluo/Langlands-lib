/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport

/-! # Exchange transformations presented by their adjuncts
(blueprint: def-weil-pbc-adjunction-square-exchange). -/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Functor

namespace CategoryTheory.Adjunction

private lemma exchange_adjunct
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (G : C ⥤ C') (H : D ⥤ D')
    (θ : G ⋙ L' ≅ L ⋙ H) (N : D) :
    L'.map ((((Functor.rightUnitor (R ⋙ G)).inv ≫
      Functor.whiskerLeft (R ⋙ G) b.unit) ≫
      (Functor.squareTransport R R' θ).hom ≫
      (Functor.whiskerRight a.counit (H ⋙ R') ≫ (Functor.leftUnitor _).hom)).app N) ≫
      b.counit.app (H.obj N) = θ.hom.app (R.obj N) ≫ H.map (a.counit.app N) := by
  simp [Functor.squareTransport]

lemma squareExchange_naturality
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (G : C ⥤ C') (H : D ⥤ D')
    (θ : G ⋙ L' ≅ L ⋙ H) {N M : D} (h : N ⟶ M) :
    (R ⋙ G).map h ≫
      b.homEquiv _ _ (θ.hom.app (R.obj M) ≫ H.map (a.counit.app M)) =
    b.homEquiv _ _ (θ.hom.app (R.obj N) ≫ H.map (a.counit.app N)) ≫
      (H ⋙ R').map h := by
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj]
  apply (b.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm]
  simp only [Equiv.symm_apply_apply]
  have hn := θ.hom.naturality (R.map h)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [Category.assoc, reassoc_of% hn, ← H.map_comp, a.counit_naturality,
    H.map_comp]

variable {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
  {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
  (a : L ⊣ R) (b : L' ⊣ R') (G : C ⥤ C') (H : D ⥤ D')
  (θ : G ⋙ L' ≅ L ⋙ H)

/-- The exchange map is the adjoint of the square comparison followed by the counit.
Source: Bhatt--Scholze, Remark 6.8.15; Mathlib's adjunction hom equivalence.
(blueprint: def-weil-pbc-adjunction-square-exchange). -/
noncomputable def squareExchange : R ⋙ G ⟶ H ⋙ R' where
  app N := b.homEquiv _ _ (θ.hom.app (R.obj N) ≫ H.map (a.counit.app N))
  naturality _ _ h := squareExchange_naturality a b G H θ h

/-- Taking the adjunct recovers the defining square/counit composite. -/
lemma squareExchange_adjunct (N : D) :
    (b.homEquiv _ _).symm ((squareExchange a b G H θ).app N) =
      θ.hom.app (R.obj N) ≫ H.map (a.counit.app N) :=
  (b.homEquiv _ _).symm_apply_apply _

/-- The same adjunct formula in map--counit form, without hom-equivalence inference. -/
lemma squareExchange_map_counit (N : D) :
    L'.map ((squareExchange a b G H θ).app N) ≫ b.counit.app (H.obj N) =
      θ.hom.app (R.obj N) ≫ H.map (a.counit.app N) :=
  squareExchange_adjunct a b G H θ N

/-- The adjunct presentation is exactly the unit--square--counit construction. -/
lemma squareExchange_eq_unit_square_counit : squareExchange a b G H θ =
    ((Functor.rightUnitor (R ⋙ G)).inv ≫ Functor.whiskerLeft (R ⋙ G) b.unit) ≫
      (Functor.squareTransport R R' θ).hom ≫
        (Functor.whiskerRight a.counit (H ⋙ R') ≫ (Functor.leftUnitor _).hom) := by
  ext N
  apply (b.homEquiv _ _).symm.injective
  rw [squareExchange_adjunct, Adjunction.homEquiv_counit]
  exact (exchange_adjunct a b G H θ N).symm

end CategoryTheory.Adjunction
