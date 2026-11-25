/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ExactPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.SfEtaleGraphTransferTensor

/-! # Proper exchange and the compactification tensor comparison

Source: step 6 of `lem-sf-etale-graph-unit-tensor`; Stacks Tag 0E48.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem projection_exchange_inv_tensor
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology B))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology B)) :
    L((g)^*[B]).map (((rightDerivedLowerStarProjectionMap B f).app K).app L) ≫
        (derivedBaseChangeMap B sq).app
          (((derivedTensor B X).obj K).obj (L((f)^*[B]).obj L)) =
      (leftDerivedUpperStarTensorIso B g (R((f)_*[B]).obj K) L).hom ≫
        ((derivedTensor B Y').map ((derivedBaseChangeMap B sq).app K)).app
          (L((g)^*[B]).obj L) ≫
        ((rightDerivedLowerStarProjectionMap B f').app (L((g')^*[B]).obj K)).app
          (L((g)^*[B]).obj L) ≫
        R((f')_*[B]).map (((derivedTensor B X').obj (L((g')^*[B]).obj K)).map
          ((derivedSquareUpperStarIso B sq).hom.app L)) ≫
        R((f')_*[B]).map
          (leftDerivedUpperStarTensorIso B g' K (L((f)^*[B]).obj L)).inv := by
  rw [← cancel_mono (R((f')_*[B]).map
    (leftDerivedUpperStarTensorIso B g' K (L((f)^*[B]).obj L)).hom)]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Category.comp_id]
  simpa only [leftDerivedUpperStarTensorIso_hom] using
    rightDerivedLowerStarProjectionMap_derivedBaseChangeMap B sq K L

private theorem exchange_tensor_transport
    {C D X Z Y : Type*} [cC : Category* C] [cD : Category* D] [cX : Category* X]
    [cZ : Category* Z] [cY : Category* Y]
    (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D) (Q : Z ⥤ Z ⥤ Z)
    {G : X ⥤ C} {U E : C ⥤ D} {V : X ⥤ Z} {R : Z ⥤ D}
    (H : Y ⥤ X) (F : D ⥤ Z) (τ : U ≅ E) (β : G ⋙ U ⟶ V ⋙ R)
    (N : Y) (X₀ : X) (N' : Y) (K : C) (J : Z)
    (δ : U.obj ((T.obj (G.obj (H.obj N))).obj K) ≅
      (S.obj (U.obj (G.obj (H.obj N)))).obj (U.obj K))
    (γ : V.obj X₀ ≅ (Q.obj (V.obj (H.obj N))).obj J)
    (πU : (S.obj (R.obj (V.obj (H.obj N)))).obj (U.obj K) ⟶
      R.obj ((Q.obj (V.obj (H.obj N))).obj (F.obj (U.obj K))))
    (πE : (S.obj (R.obj (V.obj (H.obj N)))).obj (E.obj K) ⟶
      R.obj ((Q.obj (V.obj (H.obj N))).obj (F.obj (E.obj K))))
    (d : F.obj (U.obj K) ⟶ J)
    (p : (T.obj (G.obj (H.obj N))).obj K ⟶ G.obj X₀) (a : X₀ ⟶ H.obj N')
    (P : (T.obj ((H ⋙ G).obj N)).obj K ⟶ (H ⋙ G).obj N')
    (μ : E.obj ((T.obj ((H ⋙ G).obj N)).obj K) ≅
      (S.obj (E.obj ((H ⋙ G).obj N))).obj (E.obj K))
    (b : (Q.obj (V.obj (H.obj N))).obj (F.obj (E.obj K)) ⟶ V.obj (H.obj N'))
    (hp : P = p ≫ G.map a)
    (hμ : μ = τ.symm.app _ ≪≫ δ ≪≫
      (S.mapIso (τ.app (G.obj (H.obj N)))).app (U.obj K) ≪≫
      (S.obj (E.obj (G.obj (H.obj N)))).mapIso (τ.app K))
    (hb : b = (Q.obj (V.obj (H.obj N))).map (F.map (τ.inv.app K) ≫ d) ≫
      γ.inv ≫ V.map a)
    (hπ : (S.obj (R.obj (V.obj (H.obj N)))).map (τ.inv.app K) ≫ πU =
      πE ≫ R.map ((Q.obj (V.obj (H.obj N))).map (F.map (τ.inv.app K))))
    (h : U.map p ≫ β.app X₀ =
      δ.hom ≫ (S.map (β.app (H.obj N))).app (U.obj K) ≫ πU ≫
        R.map ((Q.obj (V.obj (H.obj N))).map d) ≫ R.map γ.inv) :
    μ.inv ≫ E.map P ≫ τ.inv.app ((H ⋙ G).obj N') ≫ β.app (H.obj N') =
      (S.map (τ.inv.app (G.obj (H.obj N)) ≫ β.app (H.obj N))).app (E.obj K) ≫
        πE ≫ R.map b := by
  rw [hp, hμ, hb]
  dsimp only [Functor.comp_obj]
  simp only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, Iso.symm_inv,
    Category.assoc]
  rw [reassoc_of% (τ.inv.naturality (p ≫ G.map a))]
  simp only [Iso.hom_inv_id_app_assoc, Functor.map_comp, Category.assoc]
  have nb := β.naturality a
  dsimp only [Functor.comp_map] at nb
  rw [nb]
  rw [reassoc_of% h, Iso.inv_hom_id_assoc]
  rw [reassoc_of% ((S.map (τ.inv.app (G.obj (H.obj N)))).naturality (τ.inv.app K))]
  rw [reassoc_of% ((S.map (β.app (H.obj N))).naturality (τ.inv.app K))]
  rw [reassoc_of% hπ]
  simp only [NatTrans.comp_app, Category.assoc]

private abbrev square_component
    {C X Y Z : Type*} [Category* C] [Category* X] [Category* Y] [Category* Z]
    {G : C ⥤ X} {F : X ⥤ Z} {G' : C ⥤ Y} {F' : Y ⥤ Z}
    (β : G ⋙ F ⟶ G' ⋙ F') (K : C) : F.obj (G.obj K) ⟶ F'.obj (G'.obj K) :=
  β.app K

private abbrev projection_component
    {C X : Type*} [Category* C] [Category* X]
    (S : C ⥤ C ⥤ C) (T : X ⥤ X ⥤ X) (L : C ⥤ X) (R : X ⥤ C) (N : X)
    (π : (R ⋙ S).obj N ⟶
      ((Functor.postcompose₂.obj R).obj
        ((((Functor.whiskeringLeft₂ X).obj (𝟭 X)).obj L).obj T)).obj N)
    (K : C) : (S.obj (R.obj N)).obj K ⟶ R.obj ((T.obj N).obj (L.obj K)) :=
  π.app K

-- Normalize the projection and square components before specializing the calculation.
private theorem normalize_exchange_components
    {C D X Z : Type*} [Category* C] [Category* D] [Category* X] [Category* Z]
    (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D) (T₀ : X ⥤ X ⥤ X) (Q : Z ⥤ Z ⥤ Z)
    (G : X ⥤ C) (U : C ⥤ D) (V : X ⥤ Z) (R : Z ⥤ D)
    (L₀ : C ⥤ X) (F : D ⥤ Z) (β : G ⋙ U ⟶ V ⋙ R) (σ : U ⋙ F ≅ L₀ ⋙ V)
    (N : X) (K : C)
    (δ : U.obj ((T.obj (G.obj N)).obj K) ≅
      (S.obj (U.obj (G.obj N))).obj (U.obj K))
    (γ : V.obj ((T₀.obj N).obj (L₀.obj K)) ≅
      (Q.obj (V.obj N)).obj (V.obj (L₀.obj K)))
    (p : (G ⋙ T).obj N ⟶
      ((Functor.postcompose₂.obj G).obj
        ((((Functor.whiskeringLeft₂ X).obj (𝟭 X)).obj L₀).obj T₀)).obj N)
    (π : (R ⋙ S).obj (V.obj N) ⟶
      ((Functor.postcompose₂.obj R).obj
        ((((Functor.whiskeringLeft₂ Z).obj (𝟭 Z)).obj F).obj Q)).obj (V.obj N))
    (h : U.map (p.app K) ≫ β.app ((T₀.obj N).obj (L₀.obj K)) =
      δ.hom ≫ (S.map (β.app N)).app (U.obj K) ≫ π.app (U.obj K) ≫
        R.map ((Q.obj (V.obj N)).map (σ.hom.app K)) ≫ R.map γ.inv) :
    U.map (projection_component T T₀ L₀ G N p K) ≫
        β.app ((T₀.obj N).obj (L₀.obj K)) =
      δ.hom ≫ (S.map (β.app N)).app (U.obj K) ≫
        projection_component S Q F R (V.obj N) π (U.obj K) ≫
        R.map ((Q.obj (V.obj N)).map (square_component σ.hom K)) ≫ R.map γ.inv := by
  exact h

private theorem projection_component_naturality
    {C X : Type*} [Category* C] [Category* X]
    (S : C ⥤ C ⥤ C) (T : X ⥤ X ⥤ X) (L : C ⥤ X) (R : X ⥤ C) (N : X)
    (π : (R ⋙ S).obj N ⟶
      ((Functor.postcompose₂.obj R).obj
        ((((Functor.whiskeringLeft₂ X).obj (𝟭 X)).obj L).obj T)).obj N)
    {K₁ K₂ : C} (f : K₁ ⟶ K₂) :
    (S.obj (R.obj N)).map f ≫ projection_component S T L R N π K₂ =
      projection_component S T L R N π K₁ ≫ R.map ((T.obj N).map (L.map f)) := by
  simpa only [projection_component, Functor.comp_obj, Functor.postcompose₂, Functor.whiskeringLeft₂,
    Functor.whiskeringLeft, Functor.whiskeringRight, Functor.comp_map,
    Functor.id_obj, Functor.id_map] using π.naturality f

-- Keep the original functor-component types in the conclusion.
private theorem exchange_tensor_transport_components
    {C D X Z : Type*} [cC : Category* C] [cD : Category* D]
    [cX : Category* X] [cZ : Category* Z]
    (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D) (Q : Z ⥤ Z ⥤ Z)
    {G : X ⥤ C} {U E : C ⥤ D} {V : X ⥤ Z} {R : Z ⥤ D}
    (H : D ⥤ X) (F : D ⥤ Z) (τ : U ≅ E) (β : G ⋙ U ⟶ V ⋙ R)
    (N : D) (X₀ : X) (K : C) (J : Z)
    (δ : U.obj ((T.obj (G.obj (H.obj N))).obj K) ≅
      (S.obj (U.obj (G.obj (H.obj N)))).obj (U.obj K))
    (γ : V.obj X₀ ≅ (Q.obj (V.obj (H.obj N))).obj J)
    (π : (R ⋙ S).obj (V.obj (H.obj N)) ⟶
      ((Functor.postcompose₂.obj R).obj
        ((((Functor.whiskeringLeft₂ Z).obj (𝟭 Z)).obj F).obj Q)).obj (V.obj (H.obj N)))
    (d : F.obj (U.obj K) ⟶ J)
    (p : (T.obj (G.obj (H.obj N))).obj K ⟶ G.obj X₀)
    (a : X₀ ⟶ H.obj ((S.obj N).obj (E.obj K)))
    (P₀ : ((H ⋙ G) ⋙ T).obj N ⟶
      ((Functor.postcompose₂.obj (H ⋙ G)).obj
        ((((Functor.whiskeringLeft₂ D).obj (𝟭 D)).obj U).obj S)).obj N)
    (μ : E.obj ((T.obj ((H ⋙ G).obj N)).obj K) ≅
      (S.obj (E.obj ((H ⋙ G).obj N))).obj (E.obj K))
    (b : (Q.obj (V.obj (H.obj N))).obj (F.obj (E.obj K)) ⟶
      V.obj (H.obj ((S.obj N).obj (E.obj K))))
    (hp : projection_component T S U (H ⋙ G) N P₀ K ≫
        (H ⋙ G).map ((S.obj N).map (τ.hom.app K)) = p ≫ G.map a)
    (hμ : μ = τ.symm.app _ ≪≫ δ ≪≫
      (S.mapIso (τ.app (G.obj (H.obj N)))).app (U.obj K) ≪≫
      (S.obj (E.obj (G.obj (H.obj N)))).mapIso (τ.app K))
    (hb : b = (Q.obj (V.obj (H.obj N))).map (F.map (τ.inv.app K) ≫ d) ≫
      γ.inv ≫ V.map a)
    (hπ : (S.obj (R.obj (V.obj (H.obj N)))).map (τ.inv.app K) ≫
        projection_component S Q F R (V.obj (H.obj N)) π (U.obj K) =
      projection_component S Q F R (V.obj (H.obj N)) π (E.obj K) ≫
        R.map ((Q.obj (V.obj (H.obj N))).map (F.map (τ.inv.app K))))
    (h : U.map p ≫ β.app X₀ =
      δ.hom ≫ (S.map (β.app (H.obj N))).app (U.obj K) ≫
        projection_component S Q F R (V.obj (H.obj N)) π (U.obj K) ≫
        R.map ((Q.obj (V.obj (H.obj N))).map d) ≫ R.map γ.inv) :
    μ.inv ≫ E.map (P₀.app K ≫ (H ⋙ G).map ((S.obj N).map (τ.hom.app K))) ≫
        τ.inv.app ((H ⋙ G).obj ((S.obj N).obj (E.obj K))) ≫
        β.app (H.obj ((S.obj N).obj (E.obj K))) =
      (S.map (τ.inv.app (G.obj (H.obj N)) ≫ β.app (H.obj N))).app (E.obj K) ≫
        π.app (E.obj K) ≫ R.map b := by
  exact exchange_tensor_transport (cC := cC) (cD := cD) (cX := cX) (cZ := cZ)
    (cY := cD) T S Q H F τ β N X₀ ((S.obj N).obj (E.obj K)) K J δ γ
    (projection_component S Q F R (V.obj (H.obj N)) π (U.obj K))
    (projection_component S Q F R (V.obj (H.obj N)) π (E.obj K)) d p a
    (projection_component T S U (H ⋙ G) N P₀ K ≫
      (H ⋙ G).map ((S.obj N).map (τ.hom.app K))) μ b hp hμ hb hπ h

-- The graph tensor construction at general coefficients.
private noncomputable def graph_tensor_map
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {FC : B → B → Type*} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {V W : Scheme.{u}} (e : V ⟶ W) (c : Compactification e)
    (M : DerivedCategory (Sheaf V.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf W.smallEtaleTopology B)) :
    ((derivedTensor B (pullback c.g e)).obj
      (L((pullback.fst c.g e)^*[B]).obj
        (D((c.i)_!open[B]).obj M))).obj
      (L((pullback.snd c.g e)^*[B]).obj
        (D((e)^*[B]).obj K)) ⟶
    L((pullback.fst c.g e)^*[B]).obj
      (D((c.i)_!open[B]).obj
        (((derivedTensor B V).obj M).obj
          (D((e)^*[B]).obj K))) :=
  have : IsOpenImmersion c.i := c.isOpenImmersion
  ((derivedTensor B (pullback c.g e)).obj _).map
      (L((pullback.snd c.g e)^*[B]).map
          ((leftDerivedUpperStarIsoMapDerivedCategory B e).inv.app K) ≫
        (derivedSquareUpperStarIso B
          (IsPullback.of_hasPullback c.g e).toCommSq).hom.app K) ≫
    (leftDerivedUpperStarTensorIso B (pullback.fst c.g e)
      (D((c.i)_!open[B]).obj M)
      (L((c.g)^*[B]).obj K)).inv ≫
    L((pullback.fst c.g e)^*[B]).map
      (((derivedOpenImmersionLowerShriekProjectionIso
          B c.i).inv.app M).app
          (L((c.g)^*[B]).obj K) ≫
        D((c.i)_!open[B]).map
          (((derivedTensor B V).obj M).map
            ((leftDerivedUpperStarCompactificationIso B c).hom.app K ≫
              (leftDerivedUpperStarIsoMapDerivedCategory
                B e).hom.app K)))

private theorem exchange_tensor_geometric
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    [UpperStarPreservesFlat B]
    {FC : B → B → Type*} {CC : B → Type (u + 1)}
    [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
    [(CategoryTheory.forget B).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]
    {V W : Scheme.{u}} (e : V ⟶ W) (c : Compactification e)
    (M : DerivedCategory (Sheaf V.smallEtaleTopology B))
    (K : DerivedCategory (Sheaf W.smallEtaleTopology B))
    (b :
      ((derivedTensor B (pullback c.g e)).obj
        (L((pullback.fst c.g e)^*[B]).obj (D((c.i)_!open[B]).obj M))).obj
          (L((pullback.snd c.g e)^*[B]).obj (D((e)^*[B]).obj K)) ⟶
      L((pullback.fst c.g e)^*[B]).obj
        (D((c.i)_!open[B]).obj (((derivedTensor B V).obj M).obj (D((e)^*[B]).obj K))))
    (hb : b = graph_tensor_map B e c M K) :
    (supportExactPullbackTensorIso B e
      ((rightDerivedLowerShriekOfCompactification B c).obj M) K).inv ≫
      D((e)^*[B]).map
        (((projectionMapOfCompactification B c).app M).app K ≫
          (rightDerivedLowerShriekOfCompactification B c).map
            (((derivedTensor B V).obj M).map
              ((leftDerivedUpperStarIsoMapDerivedCategory
                B e).hom.app K))) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory B e).inv.app _ ≫
      (derivedBaseChangeMap B
        (IsPullback.of_hasPullback c.g e).toCommSq).app _ =
    ((derivedTensor B V).map
      ((leftDerivedUpperStarIsoMapDerivedCategory
          B e).inv.app _ ≫
        (derivedBaseChangeMap B
          (IsPullback.of_hasPullback c.g e).toCommSq).app
            (D((c.i)_!open[B]).obj M))).app
      (D((e)^*[B]).obj K) ≫
    ((rightDerivedLowerStarProjectionMap B
      (pullback.snd c.g e)).app
        (L((pullback.fst c.g e)^*[B]).obj
          (D((c.i)_!open[B]).obj M))).app
      (D((e)^*[B]).obj K) ≫
    R((pullback.snd c.g e)_*[B]).map
      b := by
  have : IsOpenImmersion c.i := c.isOpenImmersion
  -- Keep the component expressions explicit: nested data lets here force expensive
  -- kernel conversions through the derived tensor construction.
  have exraw := projection_exchange_inv_tensor B (IsPullback.of_hasPullback c.g e).toCommSq
      (D((c.i)_!open[B]).obj M) K
  have hπ := projection_component_naturality
    (derivedTensor B V) (derivedTensor B (pullback c.g e))
    L(((pullback.snd c.g e))^*[B]) R(((pullback.snd c.g e))_*[B]) (L(((pullback.fst c.g
        e))^*[B]).obj (D((c.i)_!open[B]).obj M)) ((rightDerivedLowerStarProjectionMap B
        (pullback.snd c.g e)).app (L(((pullback.fst c.g e))^*[B]).obj (D((c.i)_!open[B]).obj M)))
        ((leftDerivedUpperStarIsoMapDerivedCategory B e).inv.app K)
  have hp : (projection_component (derivedTensor B W) (derivedTensor B V) L((e)^*[B])
    (rightDerivedLowerShriekOfCompactification B c) M ((projectionMapOfCompactification B c).app
        M) K ≫
    (rightDerivedLowerShriekOfCompactification B c).map
      (((derivedTensor B V).obj M).map ((leftDerivedUpperStarIsoMapDerivedCategory B e).hom.app
          K))) = (projection_component (derivedTensor B W) (derivedTensor B c.Z)
    L((c.g)^*[B]) R((c.g)_*[B]) (D((c.i)_!open[B]).obj M)
    ((rightDerivedLowerStarProjectionMap B c.g).app (D((c.i)_!open[B]).obj M)) K) ≫
        R((c.g)_*[B]).map ((((derivedOpenImmersionLowerShriekProjectionIso B c.i).inv.app M).app
      (L((c.g)^*[B]).obj K)) ≫
      D((c.i)_!open[B]).map (((derivedTensor B V).obj M).map
        ((leftDerivedUpperStarCompactificationIso B c).hom.app K ≫
            (leftDerivedUpperStarIsoMapDerivedCategory B e).hom.app K))) := by
    dsimp only [projection_component]
    rw [projectionMapOfCompactification_app_app]
    simp only [Functor.map_comp, Functor.comp_map, Category.assoc]
  have hμ : (supportExactPullbackTensorIso B e
    ((rightDerivedLowerShriekOfCompactification B c).obj M) K) =
        (leftDerivedUpperStarIsoMapDerivedCategory B e).symm.app _ ≪≫
        (leftDerivedUpperStarTensorIso B e (R((c.g)_*[B]).obj (D((c.i)_!open[B]).obj M)) K) ≪≫
      ((derivedTensor B V).mapIso ((leftDerivedUpperStarIsoMapDerivedCategory B e).app
          (R((c.g)_*[B]).obj (D((c.i)_!open[B]).obj M)))).app
        (L((e)^*[B]).obj K) ≪≫
      ((derivedTensor B V).obj (D((e)^*[B]).obj
        (R((c.g)_*[B]).obj (D((c.i)_!open[B]).obj M)))).mapIso
            ((leftDerivedUpperStarIsoMapDerivedCategory B e).app K) := by
    dsimp only [supportExactPullbackTensorIso, supportDerivedTensorIso,
      rightDerivedLowerShriekOfCompactification, Functor.comp_obj]
  have hb' : b = ((derivedTensor B (pullback c.g e)).obj
      (L(((pullback.fst c.g e))^*[B]).obj (D((c.i)_!open[B]).obj M))).map (L(((pullback.snd c.g
          e))^*[B]).map ((leftDerivedUpperStarIsoMapDerivedCategory B e).inv.app K) ≫
          (square_component (derivedSquareUpperStarIso B (IsPullback.of_hasPullback c.g
          e).toCommSq).hom K)) ≫
      (leftDerivedUpperStarTensorIso B (pullback.fst c.g e) (D((c.i)_!open[B]).obj M)
          (L((c.g)^*[B]).obj K)).inv ≫ L(((pullback.fst c.g e))^*[B]).map
          ((((derivedOpenImmersionLowerShriekProjectionIso B c.i).inv.app M).app
      (L((c.g)^*[B]).obj K)) ≫
      D((c.i)_!open[B]).map (((derivedTensor B V).obj M).map
        ((leftDerivedUpperStarCompactificationIso B c).hom.app K ≫
            (leftDerivedUpperStarIsoMapDerivedCategory B e).hom.app K))) := by
    exact hb
  have ex' := normalize_exchange_components
    (derivedTensor B W) (derivedTensor B V) (derivedTensor B c.Z)
    (derivedTensor B (pullback c.g e)) R((c.g)_*[B]) L((e)^*[B])
    L(((pullback.fst c.g e))^*[B]) R(((pullback.snd c.g e))_*[B]) L((c.g)^*[B]) L(((pullback.snd
        c.g e))^*[B])
    (derivedBaseChangeMap B (IsPullback.of_hasPullback c.g e).toCommSq) (derivedSquareUpperStarIso
        B (IsPullback.of_hasPullback c.g e).toCommSq)
    (D((c.i)_!open[B]).obj M) K (leftDerivedUpperStarTensorIso B e (R((c.g)_*[B]).obj
        (D((c.i)_!open[B]).obj M)) K) (leftDerivedUpperStarTensorIso B (pullback.fst c.g e)
        (D((c.i)_!open[B]).obj M) (L((c.g)^*[B]).obj K)) ((rightDerivedLowerStarProjectionMap B
        c.g).app (D((c.i)_!open[B]).obj M)) ((rightDerivedLowerStarProjectionMap B (pullback.snd
        c.g e)).app (L(((pullback.fst c.g e))^*[B]).obj (D((c.i)_!open[B]).obj M))) exraw
  have ht := exchange_tensor_transport_components
      (C := DerivedCategory.{u + 1} (Sheaf W.smallEtaleTopology B))
      (D := DerivedCategory.{u + 1} (Sheaf V.smallEtaleTopology B))
      (X := DerivedCategory.{u + 1} (Sheaf c.Z.smallEtaleTopology B))
      (Z := DerivedCategory.{u + 1} (Sheaf (pullback c.g e).smallEtaleTopology B))
      (cC := (inferInstance : Category.{u + 1} _)) (cD := (inferInstance : Category.{u + 1} _))
      (cX := (inferInstance : Category.{u + 1} _)) (cZ := (inferInstance : Category.{u + 1} _))
      (T := derivedTensor B W) (S := derivedTensor B V)
      (Q := derivedTensor B (pullback c.g e))
      (G := R((c.g)_*[B])) (U := L((e)^*[B])) (E := D((e)^*[B]))
      (V := L(((pullback.fst c.g e))^*[B])) (R := R(((pullback.snd c.g e))_*[B]))
      (H := D((c.i)_!open[B])) (F := L(((pullback.snd c.g e))^*[B])) (τ :=
          (leftDerivedUpperStarIsoMapDerivedCategory B e)) (β := derivedBaseChangeMap B
          (IsPullback.of_hasPullback c.g e).toCommSq) M
      (((derivedTensor B c.Z).obj (D((c.i)_!open[B]).obj M)).obj (L((c.g)^*[B]).obj K)) K
      (L(((pullback.fst c.g e))^*[B]).obj (L((c.g)^*[B]).obj K))
      (leftDerivedUpperStarTensorIso B e (R((c.g)_*[B]).obj (D((c.i)_!open[B]).obj M)) K)
          (leftDerivedUpperStarTensorIso B (pullback.fst c.g e) (D((c.i)_!open[B]).obj M)
          (L((c.g)^*[B]).obj K)) ((rightDerivedLowerStarProjectionMap B (pullback.snd c.g e)).app
          (L(((pullback.fst c.g e))^*[B]).obj (D((c.i)_!open[B]).obj M))) (square_component
          (derivedSquareUpperStarIso B (IsPullback.of_hasPullback c.g e).toCommSq).hom K)
          (projection_component (derivedTensor B W) (derivedTensor B c.Z)
    L((c.g)^*[B]) R((c.g)_*[B]) (D((c.i)_!open[B]).obj M)
    ((rightDerivedLowerStarProjectionMap B c.g).app (D((c.i)_!open[B]).obj M)) K)
        ((((derivedOpenImmersionLowerShriekProjectionIso B c.i).inv.app M).app
      (L((c.g)^*[B]).obj K)) ≫
      D((c.i)_!open[B]).map (((derivedTensor B V).obj M).map
        ((leftDerivedUpperStarCompactificationIso B c).hom.app K ≫
            (leftDerivedUpperStarIsoMapDerivedCategory B e).hom.app K)))
            ((projectionMapOfCompactification B c).app M) (supportExactPullbackTensorIso B e
    ((rightDerivedLowerShriekOfCompactification B c).obj M) K) b hp hμ hb' hπ ex'
  exact ht

/-- Exchange/projection compatibility for the self-base-change square, including the
open projection comparison, but without a graph transfer or graph unit.
Source: `lem-sf-etale-graph-unit-tensor`, step 6; Stacks Tag 0E48
(auxiliary; not a blueprint node).

Proof in words. Expand projectionMapOfCompactification into the direct-image
projection for c.g, the inverse open projection for c.i, and the compactification
pullback composition isomorphism. Apply the already proved ordinary etale
exchange/projection identity to the square (c.g,e,q,q_Z), at Dj_! M and K. The
equality holds for the canonical
counit-defined direct-image projection and the mate-defined exchange. Naturality
of exchange moves the inverse open projection and the composition comparison
past exchange at their target. Pullback composition is monoidal, so the tensor
comparison and the square comparison combine into sfEtaleGraphTensorMap. Finally
transport the two inputs and the tensor output through Le* ≅ D(e*). By the
definition of supportExactPullbackTensorIso its transport factors cancel, leaving
exactly the displayed equation. No graph-transfer property or adjunction unit is
used. No invertibility of exchange is needed, so arbitrary coefficients and
arbitrary complexes are permitted, including the zero ring and empty schemes. -/
theorem sfEtaleGraphExchangeTensor
    (A : Type (u + 1)) [CommRing A]
    {V W : Scheme.{u}} (e : V ⟶ W) (c : Compactification e)
    (M : DerivedCategoryModule A V) (K : DerivedCategoryModule A W) :
    (supportExactPullbackTensorIso (ModuleCat.{u + 1} A) e
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) K).inv ≫
      D((e)^*[ModuleCat.{u + 1} A]).map
        (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K ≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
            (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).map
              ((leftDerivedUpperStarIsoMapDerivedCategory
                (ModuleCat.{u + 1} A) e).hom.app K))) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).inv.app _ ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback c.g e).toCommSq).app _ =
    ((derivedTensor (ModuleCat.{u + 1} A) V).map
      ((leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} A) e).inv.app _ ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback c.g e).toCommSq).app
            (D((c.i)_!open[ModuleCat.{u + 1} A]).obj M))).app
      (D((e)^*[ModuleCat.{u + 1} A]).obj K) ≫
    ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A)
      (pullback.snd c.g e)).app
        (L((pullback.fst c.g e)^*[ModuleCat.{u + 1} A]).obj
          (D((c.i)_!open[ModuleCat.{u + 1} A]).obj M))).app
      (D((e)^*[ModuleCat.{u + 1} A]).obj K) ≫
    R((pullback.snd c.g e)_*[ModuleCat.{u + 1} A]).map
      (sfEtaleGraphTensorMap A e c M K) := by
  exact exchange_tensor_geometric (ModuleCat.{u + 1} A) e c M K
    (sfEtaleGraphTensorMap A e c M K) (by rfl)

end AlgebraicGeometry.Etale
