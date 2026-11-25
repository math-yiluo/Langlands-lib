/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # The scalar square for open exchange from its unit transposes -/
@[expose] public section
set_option autoImplicit false
namespace CategoryTheory.Adjunction

/-- The coefficient square for open exchange follows from the pullback cube and
its specified unit transposes.
Source: Stacks 03S6 and 07A4 (blueprint: lem-pur-open-scalar-exchange-unit-mates).
Proof: apply the target open adjunction Hom bijection. Naturality of its unit
moves the scalar inverse-image comparison through the unit. The exchange unit
formula, square naturality and the open scalar unit formula compute the first
transpose. The corresponding formulas compute the second transpose. Naturality
of the inner scalar comparison leaves precisely the pullback cube evaluated at
the source open extension, precomposed with scalar pullback of its unit. -/
theorem openScalar_exchange_of_unit
    {C C' D D' E E' F F' : Type*}
    [Category C] [Category C'] [Category D] [Category D']
    [Category E] [Category E'] [Category F] [Category F']
    {L : C ⥤ D} {J : D ⥤ C} {L' : C' ⥤ D'} {J' : D' ⥤ C'}
    {N : E ⥤ F} {R : F ⥤ E} {N' : E' ⥤ F'} {R' : F' ⥤ E'}
    (a : L ⊣ J) (a' : L' ⊣ J') (b : N ⊣ R) (b' : N' ⊣ R')
    (H : C ⥤ C') (He : E ⥤ E') (G : D ⥤ D') (Ge : F ⥤ F')
    (S : C ⥤ E) (S' : C' ⥤ E') (Q : D ⥤ F) (Q' : D' ⥤ F')
    (eg : Q ⋙ Ge ≅ G ⋙ Q') (eh : S ⋙ He ≅ H ⋙ S')
    (ej : Q ⋙ R ≅ J ⋙ S) (ej' : Q' ⋙ R' ≅ J' ⋙ S')
    (c : J ⋙ H ≅ G ⋙ J') (ce : R ⋙ He ≅ Ge ⋙ R')
    (i : S ⋙ N ⟶ L ⋙ Q) (i' : S' ⋙ N' ⟶ L' ⋙ Q')
    (d : H ⋙ L' ⟶ L ⋙ G) (de : He ⋙ N' ⟶ N ⋙ Ge)
    (hi : ∀ M, b.unit.app (S.obj M) ≫ R.map (i.app M) =
      S.map (a.unit.app M) ≫ ej.inv.app (L.obj M))
    (hi' : ∀ M, b'.unit.app (S'.obj M) ≫ R'.map (i'.app M) =
      S'.map (a'.unit.app M) ≫ ej'.inv.app (L'.obj M))
    (hd : ∀ M, a'.unit.app (H.obj M) ≫ J'.map (d.app M) =
      H.map (a.unit.app M) ≫ c.hom.app (L.obj M))
    (hde : ∀ M, b'.unit.app (He.obj M) ≫ R'.map (de.app M) =
      He.map (b.unit.app M) ≫ ce.hom.app (N.obj M))
    (hcube : ∀ K, S'.map (c.hom.app K) ≫ ej'.inv.app (G.obj K) ≫
      R'.map (eg.inv.app K) =
      eh.inv.app (J.obj K) ≫ He.map (ej.inv.app K) ≫ ce.hom.app (Q.obj K))
    (M : C) :
    N'.map (eh.inv.app M) ≫ de.app (S.obj M) ≫ Ge.map (i.app M) =
      i'.app (H.obj M) ≫ Q'.map (d.app M) ≫ eg.inv.app (L.obj M) := by
  apply (b'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj]
  have hn := b'.unit.naturality_assoc (eh.inv.app M)
    (R'.map (de.app (S.obj M)) ≫ R'.map (Ge.map (i.app M)))
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
  rw [← hn]
  rw [reassoc_of% (hde (S.obj M))]
  have hnce := ce.hom.naturality (i.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnce
  rw [← hnce, ← He.map_comp_assoc, hi, He.map_comp]
  have hnh := eh.inv.naturality_assoc (a.unit.app M)
    (He.map (ej.inv.app (L.obj M)) ≫ ce.hom.app (Q.obj (L.obj M)))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hnh
  simp only [Category.assoc]
  rw [← hnh]
  rw [reassoc_of% (hi' (H.obj M))]
  have hnj := ej'.inv.naturality_assoc (d.app M) (R'.map (eg.inv.app (L.obj M)))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnj
  rw [← hnj, ← S'.map_comp_assoc, hd, S'.map_comp, Category.assoc]
  rw [hcube]

end CategoryTheory.Adjunction
