/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleSumRightAdjointCoherence
public import WeilConjectures.AlgebraicGeometry.SfEtaleAmbientAdjointProjection
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactification
import WeilConjectures.AlgebraicGeometry.SfEtaleGraphProjectionArbitraryBase

/-! # Normalized etale exceptional duality over arbitrary bases

proof.md`, paragraphs 2-3
(auxiliary; not a blueprint node).

The normalization is the mate of the constructed graph comparison, with the exact
sum/evaluation adjunction. Tensor domains are transported explicitly from left-derived
pullback to termwise exact pullback. No quasi-compactness hypothesis is imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar lowerStar etaleLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  leftDerivedUpperStarIsoMapDerivedCategory

/-- The canonical right-adjoint comparison, defined as the mate of the graph comparison
under the selected compact-support adjunction and the exact sum/evaluation adjunction.
Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraphs 2-3; the graph construction
is `compactificationEtaleComparison` in upstream `EtaleLowerShriekCompactification`
(auxiliary; not a blueprint node). -/
noncomputable def sfEtaleRightAdjointComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V W : Scheme.{u}} (e : V ⟶ W) [Etale e] (c : Compactification e)
    (G : DerivedCategoryModule A W ⥤ DerivedCategoryModule A V)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G) :
    G ⟶ (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory :=
  conjugateEquiv adj (derivedEtaleLowerShriekMapAdjunction (ModuleCat.{u + 1} A) e)
    (compactificationEtaleComparison A e c)

/-- The coefficient-unit component eta of the canonical comparison rho, followed by the
specified pullback-unit identification. Its invertibility is asserted below.
Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraphs 2-3
(auxiliary; not a blueprint node). -/
noncomputable def sfEtaleRightAdjointUnit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V W : Scheme.{u}} (e : V ⟶ W) [Etale e] (c : Compactification e)
    (G : DerivedCategoryModule A W ⥤ DerivedCategoryModule A V)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G) :
    G.obj (constantComplex A W) ⟶ constantComplex A V :=
  (sfEtaleRightAdjointComparison A e c G adj).app (constantComplex A W) ≫
    (etaleSumPullbackUnitIso A e).hom

/-- The specified ambient tensor map, with its domain transported along the canonical
left-derived/exact inverse-image comparison. This is theta on the ordinary exact model.
Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraph 3
(auxiliary; not a blueprint node). -/
noncomputable def sfEtaleExactAmbientTensorMap
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V W : Scheme.{u}} (e : V ⟶ W) [Etale e] (c : Compactification e)
    (G : DerivedCategoryModule A W ⥤ DerivedCategoryModule A V)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (K : DerivedCategoryModule A W) :
    ((derivedTensor (ModuleCat.{u + 1} A) V).obj (G.obj (constantComplex A W))).obj
      ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ⟶ G.obj K :=
  ((derivedTensor (ModuleCat.{u + 1} A) V).obj (G.obj (constantComplex A W))).map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).inv.app K) ≫
    sfEtaleAmbientTensorMap A c G adj K

private theorem tensorUnitTransport
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F G : D ⥤ C} (i : F ≅ G)
    (a : ∀ X Y : D, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (u : F.obj (𝟙_ D) ≅ 𝟙_ C)
    (h : ∀ K : D, (a (𝟙_ D) K).hom ≫
      (u.hom ▷ F.obj K) ≫ (λ_ (F.obj K)).hom = F.map (λ_ K).hom)
    (K : D) :
    (i.inv.app (𝟙_ D) ⊗ₘ i.inv.app K) ≫ (a (𝟙_ D) K).inv ≫
        i.hom.app (𝟙_ D ⊗ K) ≫ G.map (λ_ K).hom =
      ((i.inv.app (𝟙_ D) ≫ u.hom) ▷ G.obj K) ≫ (λ_ (G.obj K)).hom := by
  rw [← i.hom.naturality, ← h K]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [MonoidalCategory.tensorHom_def, comp_whiskerRight, Category.assoc]
  rw [whisker_exchange_assoc, leftUnitor_naturality_assoc]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
private theorem tensorProjectionAdjunct
    {C D : Type*} [Category C] [Category D]
    {S : C ⥤ D} {E : D ⥤ C} (adj : S ⊣ E)
    (B : C ⥤ C ⥤ C) (B' : D ⥤ D ⥤ D)
    (δ : (((Functor.whiskeringLeft₂ C).obj E).obj E).obj B ⟶
      (Functor.postcompose₂.obj E).obj B')
    {M : C} {X : D} (f : S.obj M ⟶ X) (K : D) :
    adj.homEquiv _ _
        (((adj.projectionMap E B B' δ).app M).app K ≫ (B'.map f).app K) =
      (B.map (adj.homEquiv _ _ f)).app (E.obj K) ≫ (δ.app X).app K := by
  rw [adj.homEquiv_naturality_right, adj.projectionMap_app_app,
    Equiv.apply_symm_apply]
  change ((B.map (adj.unit.app M)).app (E.obj K) ≫
    (δ.app (S.obj M)).app K) ≫ E.map ((B'.map f).app K) = _
  have hn := NatTrans.congr_app (δ.naturality f) K
  change (B.map (E.map f)).app (E.obj K) ≫ (δ.app X).app K =
    (δ.app (S.obj M)).app K ≫ E.map ((B'.map f).app K) at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← NatTrans.comp_app, ← B.map_comp]
  rw [adj.homEquiv_unit]

private theorem conjugateHomEquiv
    {C D : Type*} [Category C] [Category D]
    {F S : C ⥤ D} {G E : D ⥤ C} (adj : F ⊣ G) (sa : S ⊣ E)
    (a : S ⟶ F) (M : C) (K : D) (b : F.obj M ⟶ K) :
    adj.homEquiv M K b ≫ (conjugateEquiv adj sa a).app K =
      sa.homEquiv M K (a.app M ≫ b) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  rw [Category.assoc, NatTrans.naturality, ← Category.assoc]
  rw [unit_conjugateEquiv, Category.assoc, ← E.map_comp]

private noncomputable def exactTensorIso
    (A : Type (u + 1)) [CommRing A] {V W : Scheme.{u}} (e : V ⟶ W) :
    (Functor.postcompose₂.obj (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory).obj
        (derivedTensor (ModuleCat.{u + 1} A) W) ≅
      (((Functor.whiskeringLeft₂ _).obj
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory).obj
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory).obj
          (derivedTensor (ModuleCat.{u + 1} A) V) :=
  let i := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e
  (Functor.postcompose₂.mapIso i.symm).app _ ≪≫
    leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) e ≪≫
    (((Functor.whiskeringLeft₂ _).mapIso i).app _).app _ ≪≫
    (((Functor.whiskeringLeft₂ _).obj _).mapIso i).app _

private theorem exactTensorUnit
    (A : Type (u + 1)) [CommRing A] {V W : Scheme.{u}} (e : V ⟶ W)
    (K : DerivedCategoryModule A W) :
    (sfEtaleExactPullbackTensorIso A e (constantComplex A W) K).inv ≫
      (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) W K).hom =
      ((derivedTensor (ModuleCat.{u + 1} A) V).map
        (etaleSumPullbackUnitIso A e).hom).app
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) V
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)).hom := by
  have h := tensorUnitTransport
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e)
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) e)
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) e)
    (leftDerivedUpperStarTensorComparison_leftUnitor_hom (ModuleCat.{u + 1} A) e) K
  simpa only [sfEtaleExactPullbackTensorIso, supportExactPullbackTensorIso,
    supportDerivedTensorIso, etaleSumPullbackUnitIso, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_inv, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_inv,
    derivedTensorLeftUnitor, derivedTensor_map_app, derivedTensor_obj_map,
    constantComplex, derivedTensor, curriedTensor_obj_obj, curriedTensor_obj_map,
    curriedTensor_map_app, tensorHom_def',
    Category.assoc] using h

/-- Canonical etale exceptional duality, including its evaluation-counit normalization
and the equality of the actual tensor mate with the unit action. The adjunction argument
selects any right adjoint furnished by `sfEtaleAmbientAdjointProjection`.
proof.md`, paragraphs 2-3
(auxiliary; not a blueprint node).

Proof plan:
1. Exact etale sum extension is left adjoint to exact inverse image. Apply the
   sum/evaluation adjunction termwise, then descend its unit, counit and triangles
   through homotopy localization to the entire unbounded derived categories
   (lemma-acyclicity-pulled-back-injectives,
   situation-conventions, lem-weil-pbc-termwise-adjunction-homotopy,
   situation-conventions,
   lem-weil-pbc-localization-universal-property). Transport the canonical strong
   monoidal structure of derived pullback to exact inverse image, retaining its unit
   comparison (lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
   def-pur-etale-exact-pullback-unit-composition-comparisons,
   lem-sfb-ringed-derived-monoidal-comparisons).
2. The specified graph comparison a from sum extension S to compact support F is
   invertible (lem-sf-etale-graph-projection-arbitrary-base). Its adjunction conjugate
   rho is therefore invertible. The mate formula says ev S(rho) = a_G followed by
   the compact-support counit. This fixes the normalization uniquely
   (def-weil-pbc-adjunction-conjugate). Its coefficient-unit component followed by
   the pullback-unit identification is eta, hence eta is invertible.
3. Transpose rho_K theta_K under S adjoint to E. Naturality of a and the defining
   transpose of theta give inverse projection followed by the compact-support
   counit at A_W and the unitor (lem-sf-etale-ambient-adjoint-projection).
   The graph/projection square replaces this by kappa followed by the evaluation
   counit at A_W and the unitor (lem-sf-etale-graph-projection-arbitrary-base).
4. Naturality and the counit equation for the unit-adjunct tensor action rewrite
   this as the evaluation adjunct of E(lambda) mu^{-1} (rho_A tensor 1)
   (lem-pur-unit-adjunct-tensor-action). The monoidal left-unit law identifies it
   with the adjunct of lambda (eta tensor 1). Injectivity of the adjunction
   bijection gives the stated equality.
5. The equality expresses theta as a composite of invertible maps; thus theta is
   invertible. The argument uses neither quasi-compactness nor boundedness.
   An arbitrary open immersion has the required factorization through id_W. -/
theorem sfEtaleUnitTensorArbitraryBase
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V W : Scheme.{u}} (e : V ⟶ W) [Etale e] [IsSeparated e] (c : Compactification e)
    (G : DerivedCategoryModule A W ⥤ DerivedCategoryModule A V)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G) :
    IsIso (sfEtaleRightAdjointComparison A e c G adj) ∧
      (∀ K : DerivedCategoryModule A W,
        (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
            ((sfEtaleRightAdjointComparison A e c G adj).app K) ≫
          (derivedEtaleLowerShriekMapAdjunction (ModuleCat.{u + 1} A) e).counit.app K =
        (compactificationEtaleComparison A e c).app (G.obj K) ≫ adj.counit.app K) ∧
      (∀ K : DerivedCategoryModule A W,
        sfEtaleExactAmbientTensorMap A e c G adj K ≫
            (sfEtaleRightAdjointComparison A e c G adj).app K =
          ((derivedTensor (ModuleCat.{u + 1} A) V).map
              (sfEtaleRightAdjointUnit A e c G adj)).app
                ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫
            (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) V
              ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)).hom) ∧
      IsIso (sfEtaleRightAdjointUnit A e c G adj) ∧
      ∀ K : DerivedCategoryModule A W, IsIso (sfEtaleAmbientTensorMap A c G adj K) := by
  let E := (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory
  let S := (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory
  let B := derivedTensor (ModuleCat.{u + 1} A) V
  let B' := derivedTensor (ModuleCat.{u + 1} A) W
  let sa := derivedEtaleLowerShriekMapAdjunction (ModuleCat.{u + 1} A) e
  let a := compactificationEtaleComparison A e c
  let r := sfEtaleRightAdjointComparison A e c G adj
  let ω := G.obj (constantComplex A W)
  have ha := sfEtaleGraphProjectionArbitraryBase A e c
  have : IsIso a := ha.1
  have hr : IsIso r := by
    dsimp only [r, sfEtaleRightAdjointComparison]
    infer_instance
  have hc (K : DerivedCategoryModule A W) :
      S.map (r.app K) ≫ sa.counit.app K = a.app (G.obj K) ≫ adj.counit.app K :=
    conjugateEquiv_counit adj sa a K
  have hu : IsIso (sfEtaleRightAdjointUnit A e c G adj) := by
    dsimp only [sfEtaleRightAdjointUnit]
    have : IsIso (sfEtaleRightAdjointComparison A e c G adj) := hr
    infer_instance
  have hnorm (K : DerivedCategoryModule A W) :
      sfEtaleExactAmbientTensorMap A e c G adj K ≫ r.app K =
        (B.map (sfEtaleRightAdjointUnit A e c G adj)).app (E.obj K) ≫
          (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) V (E.obj K)).hom := by
    have hθ : sfEtaleExactAmbientTensorMap A e c G adj K =
        adj.homEquiv _ K ((sfEtaleExactProjectionIso A c ω K).inv ≫
          (B'.map (adj.counit.app (constantComplex A W))).app K ≫
            (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) W K).hom) := by
      have := (sfEtaleAmbientAdjointProjection A c).2 ω K
      unfold sfEtaleExactAmbientTensorMap sfEtaleAmbientTensorMap
      rw [← adj.homEquiv_naturality_left]
      simp only [sfEtaleExactProjectionIso, Iso.trans_inv, Functor.mapIso_inv,
        asIso_inv, Iso.app_inv, Category.assoc]
      rfl
    rw [hθ]
    change _ ≫ (conjugateEquiv adj sa a).app K = _
    rw [conjugateHomEquiv adj sa a]
    rw [← Category.assoc, ← Category.assoc, ha.2 ω K]
    simp only [Category.assoc]
    rw [← NatTrans.comp_app_assoc, ← B'.map_comp]
    let f := a.app ω ≫ adj.counit.app (constantComplex A W)
    have hf : sa.homEquiv ω (constantComplex A W) f =
        r.app (constantComplex A W) := by
      change sa.homEquiv _ _ (a.app ω ≫ adj.counit.app _) = _
      rw [← conjugateHomEquiv adj sa a]
      dsimp only [ω]
      rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components, Category.id_comp]
      rfl
    have hp : sfEtaleSumExactTensorMap A e ω K =
        ((sa.projectionMap E B B' (exactTensorIso A e).inv).app ω).app K := by
      rw [Adjunction.projectionMap_app_app]
      rfl
    rw [hp, ← Category.assoc, sa.homEquiv_naturality_right]
    change sa.homEquiv _ _
      (((sa.projectionMap E B B' (exactTensorIso A e).inv).app ω).app K ≫
        (B'.map f).app K) ≫ E.map (derivedTensorLeftUnitor
          (ModuleCat.{u + 1} A) W K).hom = _
    rw [tensorProjectionAdjunct sa B B' (exactTensorIso A e).inv f K]
    change ((B.map (sa.homEquiv ω (constantComplex A W) f)).app (E.obj K) ≫
      (sfEtaleExactPullbackTensorIso A e (constantComplex A W) K).inv) ≫
        E.map (derivedTensorLeftUnitor (ModuleCat.{u + 1} A) W K).hom = _
    rw [hf]
    rw [Category.assoc, exactTensorUnit]
    dsimp only [sfEtaleRightAdjointUnit, r]
    rw [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  refine ⟨hr, hc, hnorm, hu, ?_⟩
  intro K
  have : IsIso (sfEtaleExactAmbientTensorMap A e c G adj K ≫ r.app K) := by
    rw [hnorm]
    infer_instance
  have : IsIso (sfEtaleExactAmbientTensorMap A e c G adj K) :=
    IsIso.of_isIso_comp_right _ (r.app K)
  unfold sfEtaleExactAmbientTensorMap at this
  exact IsIso.of_isIso_comp_left
    ((B.obj ω).map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).inv.app K))
    (sfEtaleAmbientTensorMap A c G adj K)

end AlgebraicGeometry.Etale
