/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Coefficient transport of adjunction exchange maps

Source: the calculus of adjunction mates, expanded for the coefficient comparison in
Bhatt--Scholze, Lemma 6.5.9(3).
(blueprint: lem-weil-pbc-coefficient-exchange-mates)
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory.Adjunction

universe v w

variable {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type w}
  [Category.{v} C₁] [Category.{v} C₂] [Category.{v} C₃] [Category.{v} C₄]
  [Category.{v} D₁] [Category.{v} D₂] [Category.{v} D₃] [Category.{v} D₄]
  {U : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} {V : C₃ ⥤ C₄} {S : C₄ ⥤ C₃}
  {Ue : D₁ ⥤ D₂} {Re : D₂ ⥤ D₁} {Ve : D₃ ⥤ D₄} {Se : D₄ ⥤ D₃}
  (a : U ⊣ R) (b : V ⊣ S) (ae : Ue ⊣ Re) (be : Ve ⊣ Se)
  {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄} {Ge : D₁ ⥤ D₃} {He : D₂ ⥤ D₄}
  {T₁ : C₁ ⥤ D₁} {T₂ : C₂ ⥤ D₂} {T₃ : C₃ ⥤ D₃} {T₄ : C₄ ⥤ D₄}

/-- The coefficient pullback square, over fixed category and functor instances.
Keeping this equation as one predicate gives concrete derived applications the same
implicit instance arguments as the abstract mate theorem.
Source: adjunction mate calculus, Bhatt--Scholze Lemma 6.5.9(3).
(blueprint: lem-weil-pbc-coefficient-exchange-mates). -/
def coefficientPullbackSquare
    (θ : G ⋙ V ⟶ U ⋙ H) (θe : Ge ⋙ Ve ⟶ Ue ⋙ He)
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ⟶ T₁ ⋙ Ge) (αH : H ⋙ T₄ ⟶ T₂ ⋙ He)
    (M : C₁) : Prop :=
  T₄.map (θ.app M) ≫ αH.app (U.obj M) ≫ He.map (αU.hom.app M) =
    αV.hom.app (G.obj M) ≫ Ve.map (αG.app M) ≫ θe.app (T₁.obj M)

/-- Pointwise coefficient transport requires the pull-comparison cube only at `R.obj K`.
The exchange maps and push comparisons satisfy their two counit mate equations.

Source: Mathlib's adjunction mates and Bhatt--Scholze, Lemma 6.5.9(3).
(blueprint: lem-weil-pbc-coefficient-exchange-mates)

Proof. Apply injectivity of the second target adjunction's inverse Hom equivalence.
Replace both exchange maps by their adjuncts. Naturality of the target square moves
its first push comparison past the square map; its mate equation replaces the result.
Naturality of the target counit and the second mate equation rewrite the other side.
Move the mapped source exchange past the inverse pull comparison by naturality and
replace its adjunct. Naturality of the remaining horizontal comparison leaves the
pull-comparison cube precomposed and postcomposed with inverse vertical comparisons.
Cancel these isomorphisms. The resulting equality is the desired Hom-equivalence
image equality, hence the original coefficient/exchange equality. No map B or Be is
assumed invertible. -/
theorem coefficient_exchange_of_counit_at
    (θ : G ⋙ V ⟶ U ⋙ H) (θe : Ge ⋙ Ve ⟶ Ue ⋙ He)
    (K : C₂)
    (B : (R ⋙ G).obj K ⟶ (H ⋙ S).obj K)
    (Be : (Re ⋙ Ge).obj (T₂.obj K) ⟶ (He ⋙ Se).obj (T₂.obj K))
    (hB : V.map B ≫ b.counit.app (H.obj K) =
      θ.app (R.obj K) ≫ H.map (a.counit.app K))
    (hBe : Ve.map Be ≫ be.counit.app (He.obj (T₂.obj K)) =
      θe.app (Re.obj (T₂.obj K)) ≫ He.map (ae.counit.app (T₂.obj K)))
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ⟶ T₁ ⋙ Ge) (αH : H ⋙ T₄ ⟶ T₂ ⋙ He)
    (δ : T₁.obj (R.obj K) ⟶ Re.obj (T₂.obj K))
    (δ' : T₃.obj (S.obj (H.obj K)) ⟶ Se.obj (T₄.obj (H.obj K)))
    (hδ : Ue.map δ ≫ ae.counit.app (T₂.obj K) =
      αU.inv.app (R.obj K) ≫ T₂.map (a.counit.app K))
    (hδ' : Ve.map δ' ≫ be.counit.app (T₄.obj (H.obj K)) =
      αV.inv.app (S.obj (H.obj K)) ≫ T₄.map (b.counit.app (H.obj K)))
    (hcube : coefficientPullbackSquare θ θe αU αV αG αH (R.obj K)) :
    αG.app (R.obj K) ≫ Ge.map δ ≫ Be =
      T₃.map B ≫ δ' ≫ Se.map (αH.app K) := by
  unfold coefficientPullbackSquare at hcube
  apply (be.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
  rw [hBe]
  have hn := θe.naturality (δ)
  rw [reassoc_of% hn, ← Functor.map_comp, hδ]
  have hn' := be.counit.naturality (αH.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hn'
  rw [hn', reassoc_of% (hδ')]
  rw [reassoc_of% (αV.inv.naturality (B)), ← Functor.map_comp_assoc, hB]
  simp only [Functor.map_comp, Category.assoc]
  have hnH := αH.naturality (a.counit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at hnH
  rw [hnH]
  have hc := congrArg (fun z ↦ αV.inv.app (G.obj (R.obj K)) ≫ z ≫
    He.map (αU.inv.app (R.obj K))) hcube
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at hc
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hc
  simp only [Functor.comp_obj, Functor.map_id, Category.comp_id] at hc
  simpa only [Category.assoc, Functor.map_id, Category.id_comp] using congrArg
    (fun z ↦ z ≫ He.map (T₂.map (a.counit.app K))) hc.symm

/-- Coefficient transport of an exchange map follows from the pull-comparison cube and
its two counit mate equations.

Source: Mathlib's adjunction mates and Bhatt--Scholze, Lemma 6.5.9(3).
(blueprint: lem-weil-pbc-coefficient-exchange-mates)

Proof. Apply injectivity of the second target adjunction's inverse Hom equivalence.
Replace both exchange maps by their adjuncts. Naturality of the target square moves
its first push comparison past the square map; its mate equation replaces the result.
Naturality of the target counit and the second mate equation rewrite the other side.
Move the mapped source exchange past the inverse pull comparison by naturality and
replace its adjunct. Naturality of the remaining horizontal comparison leaves the
pull-comparison cube precomposed and postcomposed with inverse vertical comparisons.
Cancel these isomorphisms. The resulting equality is the desired Hom-equivalence
image equality, hence the original coefficient/exchange equality. No map B or Be is
assumed invertible. -/
theorem coefficient_exchange_of_counit
    (θ : G ⋙ V ⟶ U ⋙ H) (θe : Ge ⋙ Ve ⟶ Ue ⋙ He)
    (B : R ⋙ G ⟶ H ⋙ S) (Be : Re ⋙ Ge ⟶ He ⋙ Se)
    (hB : ∀ K, V.map (B.app K) ≫ b.counit.app (H.obj K) =
      θ.app (R.obj K) ≫ H.map (a.counit.app K))
    (hBe : ∀ K, Ve.map (Be.app K) ≫ be.counit.app (He.obj K) =
      θe.app (Re.obj K) ≫ He.map (ae.counit.app K))
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ⟶ T₁ ⋙ Ge) (αH : H ⋙ T₄ ⟶ T₂ ⋙ He)
    (δ : R ⋙ T₁ ⟶ T₂ ⋙ Re) (δ' : S ⋙ T₃ ⟶ T₄ ⋙ Se)
    (hδ : ∀ K, Ue.map (δ.app K) ≫ ae.counit.app (T₂.obj K) =
      αU.inv.app (R.obj K) ≫ T₂.map (a.counit.app K))
    (hδ' : ∀ K, Ve.map (δ'.app K) ≫ be.counit.app (T₄.obj K) =
      αV.inv.app (S.obj K) ≫ T₄.map (b.counit.app K))
    (hcube : ∀ K, T₄.map (θ.app K) ≫ αH.app (U.obj K) ≫
        He.map (αU.hom.app K) =
      αV.hom.app (G.obj K) ≫ Ve.map (αG.app K) ≫ θe.app (T₁.obj K))
    (K : C₂) :
    αG.app (R.obj K) ≫ Ge.map (δ.app K) ≫ Be.app (T₂.obj K) =
      T₃.map (B.app K) ≫ δ'.app (H.obj K) ≫ Se.map (αH.app K) := by
  exact coefficient_exchange_of_counit_at a b ae be θ θe K (B.app K) (Be.app (T₂.obj K))
    (hB K) (hBe (T₂.obj K)) αU αV αG αH (δ.app K) (δ'.app (H.obj K))
    (hδ K) (hδ' (H.obj K)) (hcube (R.obj K))

/-- Composition compatibility implies compatibility with a transported square.
Source: cancellation of composition isomorphisms in the calculus of mates.
(blueprint: lem-weil-pbc-composition-square-cancellation)
Proof. Cancel r₁, use the two composition equations and the transport equation,
and cancel s₁ with its inverse. -/
theorem composition_square_aux {D : Type*} [Category D]
    {A B C D₀ A' B' C' D' : D}
    (r₁ : A ≅ B) (r₂ : C ≅ D₀) (e : A ≅ C)
    (s₁ : A' ≅ B') (s₂ : C' ≅ D') (e' : A' ≅ C')
    (a₀ : A ⟶ A') (a₁ : C ⟶ C') (β₁ : B ⟶ B') (β₂ : D₀ ⟶ D')
    (h₁ : r₁.hom ≫ β₁ = a₀ ≫ s₁.hom)
    (h₂ : r₂.hom ≫ β₂ = a₁ ≫ s₂.hom)
    (he : e.hom ≫ a₁ = a₀ ≫ e'.hom) :
    (r₁.inv ≫ e.hom ≫ r₂.hom) ≫ β₂ =
      β₁ ≫ (s₁.inv ≫ e'.hom ≫ s₂.hom) := by
  apply (cancel_epi r₁.hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  simp only [Category.assoc]
  rw [h₂, ← Category.assoc, he]
  rw [← Category.assoc, ← Category.assoc, h₁]
  simp

end CategoryTheory.Adjunction
