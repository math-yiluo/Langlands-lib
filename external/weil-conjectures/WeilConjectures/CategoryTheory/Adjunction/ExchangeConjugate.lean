/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate

/-! # Conjugacy of the two exchange morphisms of a square

Consider a square of categories with a natural isomorphism `θ : G ⋙ Lf' ≅ Lf ⋙ G'`, where
`Lf ⊣ Rf`, `Lf' ⊣ Rf'`, `Gl ⊣ G` and `Gl' ⊣ G'`. Then `θ` has two exchange morphisms: the
exchange morphism `exchangeRight af af' θ : Rf ⋙ G ⟶ G' ⋙ Rf'` along the adjunctions
`Lf ⊣ Rf` and `Lf' ⊣ Rf'`, and the exchange morphism `exchangeLeft ag ag' θ : Lf' ⋙ Gl' ⟶ Gl ⋙ Lf`
along the adjunctions `Gl ⊣ G` and `Gl' ⊣ G'`. These are conjugate for the composite
adjunctions `Gl ⋙ Lf ⊣ Rf ⋙ G` and `Lf' ⋙ Gl' ⊣ G' ⋙ Rf'`
(`CategoryTheory.Adjunction.conjugateEquiv_exchangeLeft`), so one is an isomorphism if and only
if the other is (`CategoryTheory.Adjunction.isIso_exchangeRight_iff_isIso_exchangeLeft`).

We also characterize `exchangeLeft` by its compatibility with the units
(`CategoryTheory.Adjunction.unit_app_comp_map_exchangeLeft_app` and
`CategoryTheory.Adjunction.exchangeLeft_eq_of_unit_app_comp`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

section Conjugate

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'} {G : B ⥤ B'} {G' : A ⥤ A'}
  {Gl : B' ⥤ B} {Gl' : A' ⥤ A}
  (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (ag : Gl ⊣ G) (ag' : Gl' ⊣ G') (θ : G ⋙ Lf' ≅ Lf ⋙ G')

/-- **The two exchange morphisms of a square are conjugate**: the exchange morphism
`Lf' ⋙ Gl' ⟶ Gl ⋙ Lf` of `θ` along `Gl ⊣ G` and `Gl' ⊣ G'` is conjugate to the exchange
morphism `Rf ⋙ G ⟶ G' ⋙ Rf'` of `θ` along `Lf ⊣ Rf` and `Lf' ⊣ Rf'`, for the composite
adjunctions `Gl ⋙ Lf ⊣ Rf ⋙ G` and `Lf' ⋙ Gl' ⊣ G' ⋙ Rf'`. -/
lemma conjugateEquiv_exchangeLeft :
    conjugateEquiv (ag.comp af) (af'.comp ag') (exchangeLeft ag ag' θ) =
      exchangeRight af af' θ := by
  ext K
  have key : ag'.unit.app (Lf'.obj (G.obj (Rf.obj K))) ≫
      G'.map (Gl'.map (Lf'.map (ag.unit.app (G.obj (Rf.obj K))))) ≫
      G'.map (Gl'.map (θ.hom.app (Gl.obj (G.obj (Rf.obj K))))) ≫
      G'.map (ag'.counit.app (Lf.obj (Gl.obj (G.obj (Rf.obj K))))) ≫
      G'.map (Lf.map (ag.counit.app (Rf.obj K))) = θ.hom.app (Rf.obj K) := by
    have h₁ := ag'.unit.naturality
      (Lf'.map (ag.unit.app (G.obj (Rf.obj K))) ≫ θ.hom.app (Gl.obj (G.obj (Rf.obj K))))
    have h₂ := θ.hom.naturality (ag.counit.app (Rf.obj K))
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
      Functor.map_comp, Category.assoc] at h₁ h₂
    rw [← reassoc_of% h₁, ag'.right_triangle_components_assoc, ← h₂, ← Lf'.map_comp_assoc,
      ag.right_triangle_components, Lf'.map_id, Category.id_comp]
  simp only [conjugateEquiv_apply_app, exchangeLeft_app, exchangeRight_app, comp_unit_app,
    comp_counit_app, Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc]
  simp only [← Rf'.map_comp, reassoc_of% key]

/-- **The two exchange morphisms of a square are isomorphisms simultaneously.** -/
lemma isIso_exchangeRight_iff_isIso_exchangeLeft :
    IsIso (exchangeRight af af' θ) ↔ IsIso (exchangeLeft ag ag' θ) := by
  rw [← conjugateEquiv_exchangeLeft af af' ag ag' θ]
  exact ⟨fun _ ↦ conjugateEquiv_of_iso (ag.comp af) (af'.comp ag') _,
    fun _ ↦ conjugateEquiv_iso (ag.comp af) (af'.comp ag') _⟩

end Conjugate

section ExchangeLeft

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {jS : A ⥤ B} {jU : B ⥤ A} {jS' : A' ⥤ B'} {jU' : B' ⥤ A'} {H : A ⥤ A'} {H' : B ⥤ B'}
  (aj : jS ⊣ jU) (aj' : jS' ⊣ jU') (θ : jU ⋙ H ≅ H' ⋙ jU')

/-- The exchange morphism `exchangeLeft aj aj' θ` is compatible with the units: the unit of
`aj'` followed by `jU'` of the exchange morphism is `H` of the unit of `aj` followed by `θ`. -/
@[reassoc]
lemma unit_app_comp_map_exchangeLeft_app (K : A) :
    aj'.unit.app (H.obj K) ≫ jU'.map ((exchangeLeft aj aj' θ).app K) =
      H.map (aj.unit.app K) ≫ θ.hom.app (jS.obj K) := by
  have h := (aj'.homEquiv _ _).apply_symm_apply (H.map (aj.unit.app K) ≫ θ.hom.app (jS.obj K))
  rw [homEquiv_counit, homEquiv_unit] at h
  rw [exchangeLeft_app, ← jS'.map_comp_assoc]
  exact h

/-- **The exchange morphism `exchangeLeft` is characterized by its compatibility with the
units**: a natural transformation `γ : H ⋙ jS' ⟶ jS ⋙ H'` such that
`η' (H K) ≫ jU' (γ K) = H (η K) ≫ θ (jS K)` for all `K` is the exchange morphism of `θ`. -/
lemma exchangeLeft_eq_of_unit_app_comp (γ : H ⋙ jS' ⟶ jS ⋙ H')
    (h : ∀ K, aj'.unit.app (H.obj K) ≫ jU'.map (γ.app K) =
      H.map (aj.unit.app K) ≫ θ.hom.app (jS.obj K)) :
    exchangeLeft aj aj' θ = γ := by
  ext K
  apply (aj'.homEquiv _ _).injective
  rw [homEquiv_unit, homEquiv_unit]
  exact (unit_app_comp_map_exchangeLeft_app aj aj' θ K).trans (h K).symm

end ExchangeLeft

end CategoryTheory.Adjunction
