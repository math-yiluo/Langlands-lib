/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! Compatibility of exchange mates with a cube of inverse-image comparisons.
Source: Stacks Project, Tag 0E47; adjunction transposition.
(blueprint: lem-weil-pbc-exchange-mate-cube) -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace CategoryTheory

private theorem mate_app_eq_adjunct
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    (a : F ⊣ R) (b : K ⊣ S) (θ : G ⋙ K ⟶ F ⋙ H) (E : B) :
    (mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).app E =
      b.homEquiv _ _ (θ.app (R.obj E) ≫ H.map (a.counit.app E)) := by
  apply (b.homEquiv _ _).symm.injective
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [Equiv.symm_apply_apply]
  exact mateEquiv_counit a b (TwoSquare.mk _ _ _ _ θ) E

/-- A cube commuting on inverse-image functors commutes after taking the four mates.
Source: Stacks Project, Tag 0E47
(blueprint: lem-weil-pbc-exchange-mate-cube).
Proof: transpose both proposed maps under the final adjunction. Naturality of its
counit moves the horizontal comparison past that counit. The mate/counit equations
for the two vertical comparisons then replace their transposes by the original
inverse-image comparisons. Substitute the inverse-image cube and cancel the
comparison isomorphisms. Naturality of the second exchange comparison and the
mate/counit equation for the first vertical comparison identify the remaining
composites. Injectivity of adjunction transposition proves the equality. -/
theorem exchangeMate_cube
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      K'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ.app X) =
        θ'.app (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X))
    (E : B) :
    c.map ((mateEquiv adj adjK (TwoSquare.mk _ _ _ _ θ)).app E) ≫
        (mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv)).app (H.obj E) ≫
        S'.map (pH.hom.app E) =
      pG.hom.app (R.obj E) ≫
        G'.map ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.inv)).app E) ≫
        (mateEquiv adj' adjK' (TwoSquare.mk _ _ _ _ θ')).app (b.obj E) := by
  let e := (mateEquiv adj adjK (TwoSquare.mk _ _ _ _ θ))
  let e' := (mateEquiv adj' adjK' (TwoSquare.mk _ _ _ _ θ'))
  let mF := (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.inv))
  let mK := (mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv))
  have he := mateEquiv_counit adj adjK (TwoSquare.mk _ _ _ _ θ) E
  have he' := mateEquiv_counit adj' adjK' (TwoSquare.mk _ _ _ _ θ') (b.obj E)
  have hmF := mateEquiv_counit adj adj' (TwoSquare.mk _ _ _ _ pF.inv) E
  have hmK := mateEquiv_counit adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv) (H.obj E)
  change c.map (e.app E) ≫ mK.app (H.obj E) ≫ S'.map (pH.hom.app E) =
    pG.hom.app (R.obj E) ≫ G'.map (mF.app E) ≫ e'.app (b.obj E)
  apply (adjK'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  change K.map (e.app E) ≫ adjK.counit.app (H.obj E) =
    θ.app (R.obj E) ≫ H.map (adj.counit.app E) at he
  change K'.map (e'.app (b.obj E)) ≫ adjK'.counit.app (H'.obj (b.obj E)) =
    θ'.app (R'.obj (b.obj E)) ≫ H'.map (adj'.counit.app (b.obj E)) at he'
  change F'.map (mF.app E) ≫ adj'.counit.app (b.obj E) =
    pF.inv.app (R.obj E) ≫ b.map (adj.counit.app E) at hmF
  change K'.map (mK.app (H.obj E)) ≫ adjK'.counit.app (d.obj (H.obj E)) =
    pK.inv.app (S.obj (H.obj E)) ≫ d.map (adjK.counit.app (H.obj E)) at hmK
  have hnat := adjK'.counit.naturality (pH.hom.app E)
  dsimp only [Functor.comp_map, Functor.id_map] at hnat
  simp only [Functor.comp_obj] at *
  rw [hnat, ← Category.assoc (K'.map (mK.app (H.obj E))), hmK]
  have hn := pK.inv.naturality (e.app E)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← d.map_comp_assoc, he]
  simp only [Functor.map_comp, Category.assoc]
  have hh := congrArg (fun z ↦ K'.map (pG.hom.app (R.obj E)) ≫ z ≫
    d.map (H.map (adj.counit.app E)) ≫ pH.hom.app E) (hc (R.obj E))
  simp only [Category.assoc] at hh
  rw [← K'.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp] at hh
  have hp := pH.inv.naturality (adj.counit.app E)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hp
  rw [← Category.assoc (pH.inv.app _), ← hp] at hh
  simp only [Category.assoc, Iso.inv_hom_id_app] at hh
  rw [hh]
  dsimp only [Functor.comp_obj] at *
  simp only [Category.comp_id]
  rw [he']
  have ht := θ'.naturality (mF.app E)
  dsimp only [Functor.comp_map, Functor.comp_obj] at ht
  rw [← Category.assoc (K'.map (G'.map (mF.app E))), ht]
  simp only [Category.assoc, ← H'.map_comp, hmF]

private theorem exchangeMate_cube_normalized
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      K'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ.app X) =
        θ'.app (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X))
    (E : B)
    (mF : a.obj (R.obj E) ⟶ R'.obj (b.obj E))
    (mK : c.obj (S.obj (H.obj E)) ⟶ S'.obj (d.obj (H.obj E)))
    (hF : (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.inv)).app E = mF)
    (hK : (mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv)).app (H.obj E) = mK) :
    c.map ((mateEquiv adj adjK (TwoSquare.mk _ _ _ _ θ)).app E) ≫ mK ≫
        S'.map (pH.hom.app E) =
      pG.hom.app (R.obj E) ≫ G'.map mF ≫
        (mateEquiv adj' adjK' (TwoSquare.mk _ _ _ _ θ')).app (b.obj E) := by
  have h := exchangeMate_cube adj adjK adj' adjK' a b c d pF pG pH pK θ θ' hc E
  rw [hF, hK] at h
  exact h

private theorem exchangeMate_cube_all_normalized
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      K'.map (pG.inv.app X) ≫ pK.inv.app (G.obj X) ≫ d.map (θ.app X) =
        θ'.app (a.obj X) ≫ H'.map (pF.inv.app X) ≫ pH.inv.app (F.obj X))
    (E : B)
    (mF : a.obj (R.obj E) ⟶ R'.obj (b.obj E))
    (mK : c.obj (S.obj (H.obj E)) ⟶ S'.obj (d.obj (H.obj E)))
    (e : G.obj (R.obj E) ⟶ S.obj (H.obj E))
    (e' : G'.obj (R'.obj (b.obj E)) ⟶ S'.obj (H'.obj (b.obj E)))
    (he : (mateEquiv adj adjK (TwoSquare.mk _ _ _ _ θ)).app E = e)
    (he' : (mateEquiv adj' adjK' (TwoSquare.mk _ _ _ _ θ')).app (b.obj E) = e')
    (hF : (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.inv)).app E = mF)
    (hK : (mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv)).app (H.obj E) = mK) :
    c.map e ≫ mK ≫ S'.map (pH.hom.app E) =
      pG.hom.app (R.obj E) ≫ G'.map mF ≫ e' := by
  have h := exchangeMate_cube_normalized adj adjK adj' adjK' a b c d pF pG pH pK
    θ θ' hc E mF mK hF hK
  rw [he, he'] at h
  exact h

end CategoryTheory
