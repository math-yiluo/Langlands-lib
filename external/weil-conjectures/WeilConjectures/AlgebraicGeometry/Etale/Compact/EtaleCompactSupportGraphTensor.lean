/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphTensorCore
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumExtensionTensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection

/-!
# Tensor evaluation of the compactification graph

Source: Stacks Project, Tags 0F4L, 0GKF and 0GL5.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] Sheaf.instHasColimitsOfShape
attribute [local irreducible] Functor.mapDerivedCategory Adjunction.mapDerivedCategoryAdjunction
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarIsoMapDerivedCategory
  etaleLowerShriek upperStar lowerStar openImmersionLowerShriek derivedTensor
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor

/-- Graph evaluation commutes with the sum-extension tensor mate.
Source: Stacks Project, Tags 0F4L, 0GKF and 0GL5
(blueprint: lem-pur-compact-support-graph-tensor-evaluation).

Proof:
1. Transpose the normalized comparison under proper direct image. On a complex this
is the descent of the ordinary inverse image of the graph-extension map followed by
its sheaf counit: on a K-injective resolution this follows from counit naturality.
2. On a local tensor generator indexed by a lift s, both composites evaluate the
section on the clopen graph of s and tensor it with the restriction of the coefficient
section. Both composites vanish on the complementary open. The sheaf axiom on this
clopen cover, linearity and the universal properties of inverse image and sheafification
prove equality on sheaves. The sum tensor mate is precisely the inverse of the map
sending (s,m) tensor k to (s,m tensor s^*k), by the sum adjunction.
3. For flat-term K-flat representatives, totalize this equality degreewise. The maps
preserve factor order and degree, so the signed differentials agree. Sum extension,
open extension and inverse image preserve these K-flat representatives. The canonical
pullback and open-extension tensor comparisons therefore identify the resulting maps
with the displayed derived maps.
4. Extend equality first through the localization presenting D(V) and then through the
localization presenting D(T). Their uniqueness clauses give the equality on all unbounded
objects, with the normalized inverse comparison fixed on every homotopy representative.
-/
private theorem projection_transpose
    {C D : Type*} [Category C] [Category D]
    {P : C ⥤ D} {R : D ⥤ C} (adj : P ⊣ R)
    (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    (δ : (Functor.postcompose₂.obj P).obj T ⟶
      (((Functor.whiskeringLeft₂ _).obj P).obj P).obj T')
    {A B K : C} {J J' : D}
    (q : A ⟶ (T.obj B).obj K) (t : B ⟶ R.obj J)
    (γ : (T'.obj J).obj (P.obj K) ⟶ J') :
    (adj.homEquiv _ _).symm
      (q ≫ (T.map t).app K ≫
        ((adj.rightAdjointProjectionMap δ).app J).app K ≫ R.map γ) =
      P.map q ≫ (δ.app B).app K ≫
        (T'.map ((adj.homEquiv _ _).symm t)).app (P.obj K) ≫ γ := by
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hγ := adj.counit.naturality γ
  simp only [Functor.comp_map, Functor.id_map] at hγ
  rw [hγ]
  have hπ := adj.map_rightAdjointProjectionMap_app_app_comp_counit δ J K
  change P.map (((adj.rightAdjointProjectionMap δ).app J).app K) ≫
    adj.counit.app ((T'.obj J).obj (P.obj K)) =
      (δ.app (R.obj J)).app K ≫ (T'.map (adj.counit.app J)).app (P.obj K) at hπ
  rw [reassoc_of% hπ]
  have hn := NatTrans.congr_app (δ.naturality t) K
  change P.map ((T.map t).app K) ≫ (δ.app (R.obj J)).app K =
    (δ.app B).app K ≫ (T'.map (P.map t)).app (P.obj K) at hn
  rw [reassoc_of% hn]
  simp only [NatTrans.comp_app, Category.assoc]

theorem compactSupportGraph_tensor_evaluation
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
    [IsLocallyNoetherian T] [CompactSpace T]
    (e : V ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e)
    (M : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let S : DerivedCategoryModule A V ⥤ DerivedCategoryModule A T :=
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory
    let E : DerivedCategoryModule A T ⥤ DerivedCategoryModule A V :=
      (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory
    let O : DerivedCategoryModule A V ⥤ DerivedCategoryModule A c.Z :=
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
    let P : DerivedCategoryModule A T ⥤ DerivedCategoryModule A c.Z :=
      (upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor
    let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g
    let d : ∀ X : DerivedCategoryModule A V, P.obj (S.obj X) ⟶ O.obj X := fun X ↦
      (adj.homEquiv (S.obj X) (O.obj X)).symm ((N.comparison e c).inv.app X)
    let sumAdj := (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
      inferInstance).mapDerivedCategoryAdjunction
    ∀ q : S.obj (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).obj (E.obj K)) ⟶
        ((derivedTensor (ModuleCat.{u + 1} A) T).obj (S.obj M)).obj K,
      sumAdj.unit.app _ ≫ E.map q =
        ((derivedTensor (ModuleCat.{u + 1} A) V).map (sumAdj.unit.app M)).app (E.obj K) ≫
          (etaleSumExtensionTensorPullbackIso A e (S.obj M) K).hom →
      P.map q ≫
        ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) c.g).app (S.obj M)).app K ≫
        ((derivedTensor (ModuleCat.{u + 1} A) c.Z).map (d M)).app (P.obj K) ≫
        ((derivedOpenImmersionLowerShriekProjectionIso
          (ModuleCat.{u + 1} A) c.i).inv.app M).app (P.obj K) ≫
        O.map (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).map
          ((leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).hom.app K)) ≫
        O.map (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).hom.app K)) =
      d (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).obj (E.obj K)) := by
  dsimp only
  intro q hq
  let O := (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
  let R := (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor
  let E := (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory
  let S := (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory
  let T₀ := derivedTensor (ModuleCat.{u + 1} A) T
  let V₀ := derivedTensor (ModuleCat.{u + 1} A) V
  let t := (N.comparison e c).inv
  let d : ∀ X : DerivedCategoryModule A V,
      (upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor.obj (S.obj X) ⟶ O.obj X :=
    fun X ↦ ((derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} A) c.g).homEquiv (S.obj X) (O.obj X)).symm (t.app X)
  let γ := ((derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} A) c.i).inv.app M).app
      ((upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor.obj K) ≫
    O.map ((V₀.obj M).map
      ((leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).hom.app K)) ≫
    O.map ((V₀.obj M).map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).hom.app K))
  change _ = d ((V₀.obj M).obj (E.obj K))
  have hc := compactSupportGraph_tensor_evaluation_core A N e c M K q hq
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g
  have ht := projection_transpose adj
    T₀ (derivedTensor (ModuleCat.{u + 1} A) c.Z)
    (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) c.g) q (t.app M) γ
  change (upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor.map q ≫
      ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) c.g).app
        (S.obj M)).app K ≫
      ((derivedTensor (ModuleCat.{u + 1} A) c.Z).map (d M)).app
        ((upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor.obj K) ≫ γ =
    d ((V₀.obj M).obj (E.obj K))
  rw [← ht]
  have hcore :
      q ≫ (T₀.map (t.app M)).app K ≫
          ((adj.rightAdjointProjectionMap
            (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) c.g)).app
              (O.obj M)).app K ≫ R.map γ =
        t.app ((V₀.obj M).obj (E.obj K)) := by
    convert hc using 1
    simp only [projectionMapOfCompactification_app_app, Functor.comp_map,
      Functor.map_comp, Category.assoc, γ]
    rfl
  rw [hcore]

end AlgebraicGeometry.Etale
