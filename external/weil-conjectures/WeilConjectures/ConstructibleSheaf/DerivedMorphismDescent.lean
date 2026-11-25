/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.HeartGluing

/-!
# Descent of morphisms in the derived category along a surjective étale morphism

Let `u : U ⟶ T` be surjective and étale, and let `Z` with projections `r₁, r₂ : Z ⟶ U` be a
fibre product `U ×_T U`. Morphisms `K ⟶ M` in `D(T_ét, Λ)` between objects which are
isomorphic to sheaves placed in degree zero descend along `u`: a morphism
`δ : Lu^* K ⟶ Lu^* M` whose two pullbacks to `Z` agree is `Lu^* γ` for some `γ : K ⟶ M`.
Morphisms between sheaves placed in one degree are morphisms of sheaves, and those glue
(`AlgebraicGeometry.Etale.exists_hom_of_upperStar`).

## Main statements

- `AlgebraicGeometry.Etale.exists_leftDerivedUpperStar_map_eq_of_isPullback`: degree zero.

The version up to a common shift is in
`WeilConjectures.ConstructibleSheaf.DerivedMorphismDescentShift`.

## Implementation notes

This file only imports `WeilConjectures.SixFunctors.Etale.Derived.HeartGluing`, which does not
see the shortcut instance `ModuleCat.isGrothendieckAbelian_of_commRing`. The derived categories
in the statement therefore carry the same `IsGrothendieckAbelian (ModuleCat Λ)` instance as the
lemmas of `HeartGluing` used in the proof. With the shortcut in scope the kernel has to
reconcile the two instance paths, which took over 100 s and 9 GB of memory.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

/-- Transport through compatible squares of functors commutes with conjugation. -/
private theorem map_conjugate_of_commutative_square
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    {S₀ : C₀ ⥤ D₀} {S₁ : C₁ ⥤ D₁} {S₂ : C₂ ⥤ D₂}
    {p : C₀ ⥤ C₁} {q : C₁ ⥤ C₂} {r : C₀ ⥤ C₂}
    {P : D₀ ⥤ D₁} {Q : D₁ ⥤ D₂} {R : D₀ ⥤ D₂}
    (a : S₀ ⋙ P ≅ p ⋙ S₁) (b : S₁ ⋙ Q ≅ q ⋙ S₂) (d : S₀ ⋙ R ≅ r ⋙ S₂)
    (e : r ≅ p ⋙ q) (E : R ≅ P ⋙ Q)
    (hcomp : ∀ X, E.hom.app (S₀.obj X) ≫ Q.map (a.hom.app X) ≫
      b.hom.app (p.obj X) = d.hom.app X ≫ S₂.map (e.hom.app X))
    {K M : D₀} {F G : C₀} (eK : K ≅ S₀.obj F) (eM : M ≅ S₀.obj G)
    (δ : P.obj K ⟶ P.obj M) (φ : p.obj F ⟶ p.obj G)
    (hφ : S₁.map φ = a.inv.app F ≫ P.map eK.inv ≫ δ ≫
      P.map eM.hom ≫ a.hom.app G) :
    S₂.map (e.hom.app F ≫ q.map φ ≫ e.inv.app G) =
      d.inv.app F ≫ R.map eK.inv ≫
        (E.hom.app K ≫ Q.map δ ≫ E.inv.app M) ≫ R.map eM.hom ≫ d.hom.app G := by
  have hb : S₂.map (q.map φ) =
      b.inv.app _ ≫ Q.map (S₁.map φ) ≫ b.hom.app _ := by
    rw [← cancel_epi (b.hom.app _), Iso.hom_inv_id_app_assoc]
    exact (b.hom.naturality φ).symm
  have h₁ : ∀ X, S₂.map (e.hom.app X) =
      d.inv.app X ≫ E.hom.app _ ≫ Q.map (a.hom.app X) ≫ b.hom.app _ := by
    intro X
    rw [hcomp X]
    exact (Iso.inv_hom_id_app_assoc d X _).symm
  have h₂ : S₂.map (e.inv.app G) =
      b.inv.app _ ≫ Q.map (a.inv.app G) ≫ E.inv.app _ ≫ d.hom.app G := by
    rw [← cancel_epi (S₂.map (e.hom.app G)), ← Functor.map_comp,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, h₁ G]
    simp [← Functor.map_comp_assoc]
  have nK := E.hom.naturality eK.inv
  have nM := E.inv.naturality eM.hom
  simp only [Functor.comp_map] at nK nM
  have hφ' : a.hom.app F ≫ S₁.map φ ≫ a.inv.app G =
      P.map eK.inv ≫ δ ≫ P.map eM.hom := by
    rw [hφ]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  have hQ := congrArg Q.map hφ'
  simp only [Functor.map_comp] at hQ
  rw [Functor.map_comp, Functor.map_comp, h₁ F, hb, h₂]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% hQ, ← reassoc_of% nK, reassoc_of% nM]

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- **Descent of morphisms of sheaves placed in degree zero along a surjective étale
morphism.** Let `u : U ⟶ T` be surjective and étale, `Z` with `r₁, r₂ : Z ⟶ U` a fibre product
`U ×_T U`, and `K, M ∈ D(T_ét, Λ)` isomorphic to sheaves placed in degree zero. A morphism
`δ : Lu^* K ⟶ Lu^* M` whose two pullbacks to `Z` agree is `Lu^* γ` for a morphism `γ : K ⟶ M`. -/
theorem Etale.exists_leftDerivedUpperStar_map_eq_of_isPullback {T U Z : Scheme.{u}}
    {K M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (eK : K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj F)
    (eM : M ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj G)
    (u : U ⟶ T) [Etale u] [Surjective u] {r₁ r₂ : Z ⟶ U} (hZ : IsPullback r₁ r₂ u u)
    (δ : (L((u)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ (L((u)^*[ModuleCat.{u + 1} Λ])).obj M)
    (hδ : (leftDerivedUpperStarComp _ r₁ u).hom.app K ≫ (L((r₁)^*[_])).map δ ≫
          (leftDerivedUpperStarComp _ r₁ u).inv.app M =
        (leftDerivedUpperStarComp _ r₂ u (r₁ ≫ u) hZ.w).hom.app K ≫ (L((r₂)^*[_])).map δ ≫
          (leftDerivedUpperStarComp _ r₂ u (r₁ ≫ u) hZ.w).inv.app M) :
    ∃ γ : K ⟶ M, (L((u)^*[ModuleCat.{u + 1} Λ])).map γ = δ := by
  let s := fun {Y Z : Scheme.{u}} (g : Y ⟶ Z) ↦
    ((g)^*[ModuleCat.{u + 1} Λ]).singleFunctorCompLeftDerivedFunctorIso
  have hs : ∀ {Y Z : Scheme.{u}} (g : Y ⟶ Z)
      {A B : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
      (f : A ⟶ B),
      (L((g)^*[ModuleCat.{u + 1} Λ])).map ((_root_.DerivedCategory.singleFunctor _ 0).map f) =
        (s g).hom.app A ≫ (_root_.DerivedCategory.singleFunctor _ 0).map ((g)^*[_].map f) ≫
          (s g).inv.app B := fun {Y Z} g {A B} f ↦ by
    rw [← cancel_mono ((s g).hom.app B), Category.assoc, Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact (s g).hom.naturality f
  let φ₀ := (_root_.DerivedCategory.singleFunctor (Sheaf U.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0).preimage ((s u).inv.app F ≫ (L((u)^*[_])).map eK.inv ≫ δ ≫
      (L((u)^*[_])).map eM.hom ≫ (s u).hom.app G)
  have hφ₀ : (_root_.DerivedCategory.singleFunctor _ 0).map φ₀ = (s u).inv.app F ≫
      (L((u)^*[_])).map eK.inv ≫ δ ≫ (L((u)^*[_])).map eM.hom ≫ (s u).hom.app G :=
    Functor.map_preimage _ _
  let e : PUnit.{u + 1} → (U ⟶ T) := fun _ ↦ u
  have he : ∀ j, Etale (e j) := fun _ ↦ inferInstance
  have hcov : ⋃ j, Set.range (e j).base = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨⟨⟩, u.surjective x⟩
  obtain ⟨φ', hφ'⟩ := Etale.exists_hom_of_upperStar e he hcov F G (fun _ ↦ φ₀) (by
    intro j k W a b w ha hb _ _ _
    apply (_root_.DerivedCategory.singleFunctor _ 0).map_injective
    have key : ∀ (c : W ⟶ U) (hc : w = c ≫ u),
        (_root_.DerivedCategory.singleFunctor _ 0).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) c u w hc).hom.app F ≫
          (c)^*[ModuleCat.{u + 1} Λ].map φ₀ ≫
            (Etale.upperStarComp (ModuleCat.{u + 1} Λ) c u w hc).inv.app G) =
        (s w).inv.app F ≫ (L((w)^*[ModuleCat.{u + 1} Λ])).map eK.inv ≫
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) c u w hc).hom.app K ≫
            (L((c)^*[ModuleCat.{u + 1} Λ])).map δ ≫
            (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) c u w hc).inv.app M) ≫
          (L((w)^*[ModuleCat.{u + 1} Λ])).map eM.hom ≫ (s w).hom.app G := by
      intro c hc
      exact map_conjugate_of_commutative_square (s u) (s c) (s w)
        (Etale.upperStarComp _ c u w hc) (leftDerivedUpperStarComp _ c u w hc)
        (Etale.leftDerivedUpperStarComp_hom_app_singleFunctor_obj c u w hc)
        eK eM δ φ₀ hφ₀
    rw [key a ha, key b hb]
    have hab : a ≫ u = b ≫ u := ha.symm.trans hb
    let ℓ := hZ.lift a b hab
    have T₁ := Etale.leftDerivedUpperStarComp_conj_comp ℓ r₁ u a (r₁ ≫ u) w
      (hZ.lift_fst _ _ _).symm rfl ha δ
    have T₂ := Etale.leftDerivedUpperStarComp_conj_comp ℓ r₂ u b (r₁ ≫ u) w
      (hZ.lift_snd _ _ _).symm hZ.w hb δ
    have hτ : (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) a u w ha).hom.app K ≫
        (L((a)^*[ModuleCat.{u + 1} Λ])).map δ ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) a u w ha).inv.app M =
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) b u w hb).hom.app K ≫
        (L((b)^*[ModuleCat.{u + 1} Λ])).map δ ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) b u w hb).inv.app M := by
      rw [T₁, T₂, hδ]
    rw [hτ])
  refine ⟨eK.hom ≫ (_root_.DerivedCategory.singleFunctor _ 0).map φ' ≫ eM.inv, ?_⟩
  rw [Functor.map_comp, Functor.map_comp, hs, hφ' ⟨⟩, hφ₀]
  simp [← Functor.map_comp_assoc]

end AlgebraicGeometry
