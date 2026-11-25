/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate

/-!
# Transport of exchange morphisms along comparison functors

Let `adj : Lf ⊣ Rf` and `adj' : Lf' ⊣ Rf'` be adjunctions and `θ : G ⋙ Lf' ≅ Lf ⋙ G'` a
commutation isomorphism, with exchange morphism `exchangeRight adj adj' θ : Rf ⋙ G ⟶ G' ⋙ Rf'`.
Let `ad : lf ⊣ rf`, `ad' : lf' ⊣ rf'` and `t : g ⋙ lf' ≅ lf ⋙ g'` be a second such datum, and let
`H` be functors from the categories of the first datum to those of the second (for instance
homology functors, or inclusions of full subcategories), commuting with all the functors
through isomorphisms `ψ`. If the units and counits of the adjunctions and the isomorphisms `θ`
and `t` are compatible with the `ψ`, then so are the exchange morphisms
(`CategoryTheory.Adjunction.map_exchangeRight_app_of_comm`).

The exchange morphism is characterized by its compatibility with the units
(`CategoryTheory.Adjunction.exchangeRight_eq_of_map_unit_app_comp`).

-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {B A B' A' b a b' a' : Type*} [Category* B] [Category* A] [Category* B'] [Category* A']
  [Category* b] [Category* a] [Category* b'] [Category* a']

/-- **The exchange morphism is characterized by its compatibility with the units**: a natural
transformation `σ : Rf ⋙ G ⟶ G' ⋙ Rf'` such that `G (η M) ≫ σ (Lf M) = η' (G M) ≫ Rf' (θ M)` for
all `M` is the exchange morphism of `θ`. -/
lemma exchangeRight_eq_of_map_unit_app_comp {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'}
    {Rf' : A' ⥤ B'} {G : B ⥤ B'} {G' : A ⥤ A'} (adj : Lf ⊣ Rf) (adj' : Lf' ⊣ Rf')
    (θ : G ⋙ Lf' ≅ Lf ⋙ G') (σ : Rf ⋙ G ⟶ G' ⋙ Rf')
    (hσ : ∀ M, G.map (adj.unit.app M) ≫ σ.app (Lf.obj M) =
      adj'.unit.app (G.obj M) ≫ Rf'.map (θ.hom.app M)) :
    exchangeRight adj adj' θ = σ := by
  ext K
  have hn := σ.naturality (adj.counit.app K)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hn
  rw [exchangeRight_app, ← Category.assoc, ← hσ, Category.assoc, ← hn, ← Category.assoc,
    ← G.map_comp, right_triangle_components]
  simp

/-- **Transport of exchange morphisms.** Let `adj : Lf ⊣ Rf`, `adj' : Lf' ⊣ Rf'`,
`θ : G ⋙ Lf' ≅ Lf ⋙ G'` and `ad : lf ⊣ rf`, `ad' : lf' ⊣ rf'`, `t : g ⋙ lf' ≅ lf ⋙ g'` be two
data of exchange morphisms, and let `H_B`, `H_A`, `H_B'`, `H_A'` be functors from the
categories of the first datum to those of the second, with commutation isomorphisms `ψ` with
all the functors. If the unit of `adj'`, the counit of `adj` and `θ` are compatible with the
`ψ`, then the exchange morphisms of `θ` and of `t` correspond to each other. -/
lemma map_exchangeRight_app_of_comm {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'}
    {Rf' : A' ⥤ B'} {G : B ⥤ B'} {G' : A ⥤ A'} (adj : Lf ⊣ Rf) (adj' : Lf' ⊣ Rf')
    (θ : G ⋙ Lf' ≅ Lf ⋙ G')
    {lf : b ⥤ a} {rf : a ⥤ b} {lf' : b' ⥤ a'} {rf' : a' ⥤ b'} {g : b ⥤ b'} {g' : a ⥤ a'}
    (ad : lf ⊣ rf) (ad' : lf' ⊣ rf') (t : g ⋙ lf' ≅ lf ⋙ g')
    {HB : B ⥤ b} {HA : A ⥤ a} {HB' : B' ⥤ b'} {HA' : A' ⥤ a'}
    (ψL : HB ⋙ lf ≅ Lf ⋙ HA) (ψR : HA ⋙ rf ≅ Rf ⋙ HB)
    (ψL' : HB' ⋙ lf' ≅ Lf' ⋙ HA') (ψR' : HA' ⋙ rf' ≅ Rf' ⋙ HB')
    (ψG : HB ⋙ g ≅ G ⋙ HB') (ψG' : HA ⋙ g' ≅ G' ⋙ HA')
    (hunit : ∀ K, HB'.map (adj'.unit.app K) =
      ad'.unit.app (HB'.obj K) ≫ rf'.map (ψL'.hom.app K) ≫ ψR'.hom.app (Lf'.obj K))
    (hcounit : ∀ K, lf.map (ψR.hom.app K) ≫ ψL.hom.app (Rf.obj K) ≫ HA.map (adj.counit.app K) =
      ad.counit.app (HA.obj K))
    (hθ : ∀ K, lf'.map (ψG.hom.app K) ≫ ψL'.hom.app (G.obj K) ≫ HA'.map (θ.hom.app K) =
      t.hom.app (HB.obj K) ≫ g'.map (ψL.hom.app K) ≫ ψG'.hom.app (Lf.obj K))
    (K : A) :
    g.map (ψR.hom.app K) ≫ ψG.hom.app (Rf.obj K) ≫
        HB'.map ((exchangeRight adj adj' θ).app K) =
      (exchangeRight ad ad' t).app (HA.obj K) ≫ rf'.map (ψG'.hom.app K) ≫
        ψR'.hom.app (G'.obj K) := by
  rw [exchangeRight_app, exchangeRight_app, HB'.map_comp, HB'.map_comp, hunit]
  have h₁ := ψR'.hom.naturality (θ.hom.app (Rf.obj K))
  have h₂ := ψR'.hom.naturality (G'.map (adj.counit.app K))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at h₁ h₂
  simp only [Category.assoc]
  rw [← reassoc_of% h₁, ← h₂]
  have h₃ := ad'.unit.naturality (g.map (ψR.hom.app K) ≫ ψG.hom.app (Rf.obj K))
  rw [reassoc_of% h₃]
  have key : lf'.map (g.map (ψR.hom.app K) ≫ ψG.hom.app (Rf.obj K)) ≫
      ψL'.hom.app (G.obj (Rf.obj K)) ≫ HA'.map (θ.hom.app (Rf.obj K)) ≫
      HA'.map (G'.map (adj.counit.app K)) =
      t.hom.app (rf.obj (HA.obj K)) ≫ g'.map (ad.counit.app (HA.obj K)) ≫ ψG'.hom.app K := by
    have h₄ := t.hom.naturality (ψR.hom.app K)
    have h₅ := ψG'.hom.naturality (adj.counit.app K)
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at h₄ h₅
    rw [lf'.map_comp, Category.assoc, reassoc_of% (hθ (Rf.obj K)), ← h₅,
      reassoc_of% h₄, ← g'.map_comp_assoc, ← g'.map_comp_assoc, Category.assoc, hcounit]
  have key' := rf'.congr_map key
  simp only [Functor.map_comp, Category.assoc] at key' ⊢
  rw [reassoc_of% key']

/-- The exchange morphism `exchangeRight adj adj' θ` is compatible with the units: at `Lf M`,
precomposed with `G` of the unit of `adj`, it is the unit of `adj'` followed by `Rf' θ`. -/
@[reassoc]
lemma map_unit_comp_exchangeRight_app {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'}
    {Rf' : A' ⥤ B'} {G : B ⥤ B'} {G' : A ⥤ A'} (adj : Lf ⊣ Rf) (adj' : Lf' ⊣ Rf')
    (θ : G ⋙ Lf' ≅ Lf ⋙ G') (M : B) :
    G.map (adj.unit.app M) ≫ (exchangeRight adj adj' θ).app (Lf.obj M) =
      adj'.unit.app (G.obj M) ≫ Rf'.map (θ.hom.app M) := by
  have h₁ := adj'.unit.naturality (G.map (adj.unit.app M))
  have h₂ := θ.hom.naturality (adj.unit.app M)
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at h₁ h₂
  rw [exchangeRight_app, reassoc_of% h₁, ← Rf'.map_comp, ← Rf'.map_comp, reassoc_of% h₂,
    ← G'.map_comp, left_triangle_components, G'.map_id, Category.comp_id]

end CategoryTheory.Adjunction
