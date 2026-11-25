/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Higher direct images as sheafified cohomology presheaves

Source: Stacks Project, Lemma Tag 072W (lemma-higher-direct-images), and Section 21.2
(equation-cohomology-object-site)
(blueprint: lem-weil-pbc-higher-direct-image-sheafified-presheaf).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For an arbitrary scheme morphism, `R^q p_* F` is the sheafification of
`V ↦ H^q(V ×_S X,F)`, with restriction induced by base change. Here `H^q(U,F)` is the
`q`-th right derived functor of the abelian-sheaf evaluation `G ↦ G(U)` (as in
lem-weil-pbc-injective-module-abelian-acyclic), and the restriction along `U' ⟶ U` is the
derived map `NatTrans.rightDerived` of evaluation restriction, i.e. the map induced on
`H^q` by the restriction maps `I^•(U) ⟶ I^•(U')` of an injective resolution of `F`.

Source: Stacks Project, Lemma Tag 072W and Section 21.2, equation-cohomology-object-site
(blueprint: lem-weil-pbc-higher-direct-image-sheafified-presheaf).

Proof:
1. Choose an injective resolution `R` of `F`, using the Grothendieck property of
abelian etale sheaves and enough injectives. Put `K = p_* R.cocomplex` and let `L`
be its underlying complex of presheaves. `InjectiveResolution.isoRightDerivedObj`
computes each classical right derived functor from `R`.
2. Evaluation of `L` at `V` is evaluation of `R.cocomplex` at `V ×_S X`, including
differentials and restriction maps, by the definition of direct image.
3. Exact evaluation commutes with homology. Compose its homology comparison with
`R.isoRightDerivedObj` to identify the specified derived-evaluation presheaf with
`L.homology q`. Naturality follows from `InjectiveResolution.rightDerived_app_eq`
and `ShortComplex.homologyMap_mapNatTrans`.
4. Exact sheafification commutes with homology, and the counit identifies the
sheafification of `L` with `K`. Thus the sheafification of the specified presheaf
is `K.homology q`, hence the classical `q`-th right derived direct image.
5. The proved source-library comparison
`Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso` identifies this with
homology of the total bounded-below derived pushforward of `F` in degree zero.
No separate arbitrary K-injective resolution comparison is needed. -/
noncomputable def higherDirectImageSheafifiedPresheaf {X S : Scheme.{u}} (p : X ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
      ((presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          ((MorphismProperty.Over.pullback @Etale ⊤ p).op ⋙
            { obj := fun U ↦
                ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
                  (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj U).rightDerived q).obj F
              map := fun f ↦
                (NatTrans.rightDerived
                  (Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
                    ((evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).map f)) q).app F
              map_id := fun U ↦ by
                simp only [CategoryTheory.Functor.map_id, Functor.whiskerLeft_id',
                  NatTrans.rightDerived_id, NatTrans.id_app]
              map_comp := fun f g ↦ by
                simp only [CategoryTheory.Functor.map_comp, Functor.whiskerLeft_comp,
                  NatTrans.rightDerived_comp, NatTrans.comp_app] }) ≅
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((Etale.rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} p).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) := by
  -- Compute both classical derived functors with the same injective resolution.
  let R := injectiveResolution F
  let f := Etale.lowerStar AddCommGrpCat.{u + 1} p
  let ι := sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}
  let a := presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}
  let K := (f.mapHomologicalComplex (.up ℕ)).obj R.cocomplex
  let L := (ι.mapHomologicalComplex (.up ℕ)).obj K
  let P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    { obj := fun U ↦
        ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj U).rightDerived q).obj F
      map := fun g ↦
        (NatTrans.rightDerived
          (Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
            ((evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).map g)) q).app F
      map_id := fun U ↦ by
        simp only [CategoryTheory.Functor.map_id, Functor.whiskerLeft_id',
          NatTrans.rightDerived_id, NatTrans.id_app]
      map_comp := fun g h ↦ by
        simp only [CategoryTheory.Functor.map_comp, Functor.whiskerLeft_comp,
          NatTrans.rightDerived_comp, NatTrans.comp_app] }
  -- Evaluation is exact; its homology comparison respects restriction maps.
  let eP : (MorphismProperty.Over.pullback @Etale ⊤ p).op ⋙ P ≅ L.homology q :=
    NatIso.ofComponents
      (fun V ↦ R.isoRightDerivedObj
          (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
            (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
              ((MorphismProperty.Over.pullback @Etale ⊤ p).op.obj V)) q ≪≫
        (L.sc q).mapHomologyIso ((evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj V))
      (by
        intro V W g
        dsimp [P]
        rw [R.rightDerived_app_eq]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        congr 1
        change ShortComplex.homologyMap
            ((L.sc q).mapNatTrans ((evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).map g)) ≫
            ((L.sc q).mapHomologyIso
              ((evaluation S.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj W)).hom = _
        rw [ShortComplex.homologyMap_mapNatTrans]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        rfl)
  -- Sheafification of the underlying complex recovers the complex of sheaves.
  let eK : (a.mapHomologicalComplex (.up ℕ)).obj L ≅ K :=
    (Functor.mapHomologicalComplexCompIso (sheafificationNatIso
      S.smallEtaleTopology AddCommGrpCat.{u + 1}).symm (.up ℕ)).app K ≪≫
      (Functor.mapHomologicalComplexIdIso _ (.up ℕ)).app K
  -- Exact sheafification commutes with homology, then PlusSingle gives the total derived value.
  exact a.mapIso eP ≪≫ ((L.sc q).mapHomologyIso a).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℕ) q).mapIso eK ≪≫
    (R.isoRightDerivedObj f q).symm ≪≫
    (f.homologyRightDerivedFunctorPlusObjSingleFunctorIso F q).symm

end AlgebraicGeometry
