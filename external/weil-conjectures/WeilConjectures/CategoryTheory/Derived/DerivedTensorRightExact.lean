/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
/-! # Tensor comparison for a right exact scalar functor

The two-variable left derived universal property applies to flat K-flat models and
requires no exactness of the ordinary scalar functor. The cochain equation retains
the fixed derived counit, including the quotient-to-homotopy comparison maps.
-/

@[expose] public section
set_option autoImplicit false
universe u u₁ u₂ u₃ u₄

open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory

open scoped CategoryTheory.Functor
open CategoryTheory.Functor

namespace CategoryTheory
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F G : C ⥤ D) (e : F ≅ G)

private def tensorConjugate
    (τ : (postcompose₂.obj G).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ _).obj G).obj G).obj (curriedTensor D)) :
    (postcompose₂.obj F).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ _).obj F).obj F).obj (curriedTensor D) :=
  (postcompose₂.mapIso e).app (curriedTensor C) ≪≫ τ ≪≫
    ((((Functor.whiskeringLeft₂ _).mapIso e).app F).app (curriedTensor D) ≪≫
      (((Functor.whiskeringLeft₂ _).obj G).mapIso e).app (curriedTensor D)).symm

private theorem tensorConjugate_hom
    (τ : (postcompose₂.obj G).obj (curriedTensor C) ≅
      (((Functor.whiskeringLeft₂ _).obj G).obj G).obj (curriedTensor D)) (K L : C) :
    (((tensorConjugate F G e τ).hom.app K).app L) =
      e.hom.app (K ⊗ L) ≫ ((τ.hom.app K).app L) ≫
        (e.inv.app K ⊗ₘ e.inv.app L) := by
  simp [tensorConjugate, tensorHom_def]

attribute [local irreducible] tensorConjugate

private theorem transfer_tensor_counit
    {P Q T : C} {EP EQ V : D} (t : P ⊗ Q ⟶ T) (t' : EP ⊗ EQ ⟶ V)
    (εP : G.obj P ⟶ EP) (εQ : G.obj Q ⟶ EQ) (εT : G.obj T ⟶ V)
    (τ : G.obj (P ⊗ Q) ⟶ G.obj P ⊗ G.obj Q)
    (h : G.map t ≫ εT = τ ≫ (εP ⊗ₘ εQ) ≫ t') :
    F.map t ≫ (e.hom.app T ≫ εT) =
      (e.hom.app (P ⊗ Q) ≫ τ ≫ (e.inv.app P ⊗ₘ e.inv.app Q)) ≫
        ((e.hom.app P ≫ εP) ⊗ₘ (e.hom.app Q ≫ εQ)) ≫ t' := by
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc,
    Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% e.hom.naturality, h]

private theorem binaryIso_ext_of_representatives
    {C D H : Type*} [Category C] [Category D] [Category H]
    (T : C ⥤ C ⥤ C) (S : D ⥤ D ⥤ D) (F : C ⥤ D) (q : H ⥤ C)
    (P : H → Prop)
    (hres : ∀ K : C, ∃ X : H, P X ∧ Nonempty (q.obj X ≅ K))
    (μ ν : ∀ K L, (S.obj (F.obj K)).obj (F.obj L) ≅ F.obj ((T.obj K).obj L))
    (hμ₁ : ∀ {K K'} (f : K ⟶ K') L,
      (S.map (F.map f)).app (F.obj L) ≫ (μ K' L).hom =
        (μ K L).hom ≫ F.map ((T.map f).app L))
    (hμ₂ : ∀ K {L L'} (f : L ⟶ L'),
      (S.obj (F.obj K)).map (F.map f) ≫ (μ K L').hom =
        (μ K L).hom ≫ F.map ((T.obj K).map f))
    (hν₁ : ∀ {K K'} (f : K ⟶ K') L,
      (S.map (F.map f)).app (F.obj L) ≫ (ν K' L).hom =
        (ν K L).hom ≫ F.map ((T.map f).app L))
    (hν₂ : ∀ K {L L'} (f : L ⟶ L'),
      (S.obj (F.obj K)).map (F.map f) ≫ (ν K L').hom =
        (ν K L).hom ≫ F.map ((T.obj K).map f))
    (hm : ∀ X Y, P X → P Y → μ (q.obj X) (q.obj Y) = ν (q.obj X) (q.obj Y)) :
    μ = ν := by
  funext K L
  obtain ⟨X, hX, ⟨e⟩⟩ := hres K
  obtain ⟨Y, hY, ⟨f⟩⟩ := hres L
  apply Iso.ext
  apply (cancel_epi ((S.map (F.map e.hom)).app (F.obj (q.obj Y)) ≫
    (S.obj (F.obj K)).map (F.map f.hom))).1
  simp only [Category.assoc, hμ₂, hν₂]
  rw [← Category.assoc, hμ₁, ← Category.assoc, hν₁, hm X Y hX hY]

private theorem transport_tensor_counit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) {P P' Q Q' T T' : C} {EP EP' EQ EQ' ET ET' V V' : D}
    (a : P ≅ P') (b : Q ≅ Q') (c : T ≅ T')
    (e : EP ≅ EP') (f : EQ ≅ EQ') (d : ET ≅ ET') (g : V ≅ V')
    (t : P ⊗ Q ⟶ T) (t' : EP ⊗ EQ ⟶ V)
    (εP : L.obj P ⟶ EP) (εQ : L.obj Q ⟶ EQ) (εT : L.obj T ⟶ ET)
    (δ : ET ⟶ V) (δ' : ET' ⟶ V')
    (τ : L.obj (P ⊗ Q) ⟶ L.obj P ⊗ L.obj Q)
    (τ' : L.obj (P' ⊗ Q') ⟶ L.obj P' ⊗ L.obj Q')
    (hn : L.map (a.inv ⊗ₘ b.inv) ≫ τ = τ' ≫ (L.map a.inv ⊗ₘ L.map b.inv))
    (hc : τ ≫ (εP ⊗ₘ εQ) ≫ t' = L.map t ≫ εT ≫ δ)
    (hδ : δ ≫ g.hom = d.hom ≫ δ') :
    L.map ((a.inv ⊗ₘ b.inv) ≫ t ≫ c.hom) ≫
        (L.map c.inv ≫ εT ≫ d.hom) ≫ δ' =
      τ' ≫ ((L.map a.inv ≫ εP ≫ e.hom) ⊗ₘ (L.map b.inv ≫ εQ ≫ f.hom)) ≫
        ((e.inv ⊗ₘ f.inv) ≫ t' ≫ g.hom) := by
  rw [← tensorHom_comp_tensorHom (L.map a.inv) (L.map b.inv)]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_map_assoc,
    tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← tensorHom_comp_tensorHom (L.map a.inv) (L.map b.inv)]
  rw [Category.assoc, ← reassoc_of% hn, reassoc_of% hc, hδ]

end CategoryTheory

namespace CategoryTheory.Functor

attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]

/-- The total left-derived counit on a cochain representative, transported through
both quotient-to-homotopy comparison isomorphisms.
Source: Stacks 06YY, localization construction of the total derived functor
(blueprint: lem-derived-right-exact-tensor-comparison). -/
noncomputable def rightExact_cochainCounit
    (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] (P : CochainComplex C ℤ) :
    F.leftDerivedFunctor.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
  F.leftDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).inv.app P) ≫
    F.leftDerivedFunctorCounit.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) ≫
    (DerivedCategory.quotientCompQhIso D).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj P)

attribute [local irreducible] rightExact_cochainCounit

section CachedMonoidalStructures

-- Cache the canonical structures. All public signatures are outside this section.
private noncomputable abbrev complexMonoidalC : MonoidalCategory (CochainComplex C ℤ) :=
  inferInstance
private noncomputable abbrev complexMonoidalD : MonoidalCategory (CochainComplex D ℤ) :=
  inferInstance
private noncomputable abbrev homotopyMonoidalC :
    MonoidalCategory (HomotopyCategory C (.up ℤ)) := inferInstance
private noncomputable abbrev homotopyMonoidalD :
    MonoidalCategory (HomotopyCategory D (.up ℤ)) := inferInstance
private noncomputable abbrev derivedMonoidalC : MonoidalCategory (DerivedCategory C) :=
  inferInstance
private noncomputable abbrev derivedMonoidalD : MonoidalCategory (DerivedCategory D) :=
  inferInstance

attribute [local instance 2000] complexMonoidalC complexMonoidalD
  homotopyMonoidalC homotopyMonoidalD derivedMonoidalC derivedMonoidalD

section GoodModels

variable (F : C ⥤ D) [F.Additive] [F.PreservesFlat] [F.IsLeftAdjoint]

private abbrev tensorGoodModels : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (HomotopyCategory.quasiIso C (.up ℤ)).kFlat ⊓ F.kFlatMap

private instance tensorGoodModels_isLeftDerivabilityStructure :
    (HomotopyCategory.quasiIsoLocalizerMorphism F.tensorGoodModels).IsLeftDerivabilityStructure :=
      by
  let Λ := (inferInstance : HasFunctorialFlatResolution C).some
  refine HomotopyCategory.isLeftDerivabilityStructure_quasiIsoLocalizerMorphism _
    Λ.reduced.resolutionNatTrans (fun _ ↦ inferInstance) ?_
  intro K
  exact ⟨(HomotopyCategory.kFlat_quotient_obj_iff _).2
      (Λ.reduced.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K),
    F.kFlatMap_quotient_obj_resolutionFunctor_obj Λ.reduced K⟩

end GoodModels

section Comparison

variable (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]

/-- The bifunctor `(K, M) ↦ LF K ⊗ᴸ LF M`, of type `D(C) ⥤ D(C) ⥤ D(D)`. -/
private noncomputable abbrev rightExact_derivedTensorLeftDerived :
    DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory D :=
  (((whiskeringLeft₂ _).obj F.leftDerivedFunctor).obj F.leftDerivedFunctor).obj
    (curriedTensor _)

/-- The bifunctor `(K, M) ↦ LF(K ⊗ᴸ M)`, of type `D(C) ⥤ D(C) ⥤ D(D)`. -/
private noncomputable abbrev rightExact_leftDerivedDerivedTensor :
    DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory D :=
  (postcompose₂.obj F.leftDerivedFunctor).obj (curriedTensor _)

/-- The counit exhibiting `(K, M) ↦ LF K ⊗ᴸ LF M` as the total left derived functor of
`(A, B) ↦ F A ⊗ F B`. On `K, M` in `K(C)` it is the composite
```
 LF(Qh K) ⊗ᴸ LF(Qh M) --(counit ⊗ᴸ 1)--> Qh(F K) ⊗ᴸ LF(Qh M)
   --(1 ⊗ᴸ counit)--> Qh(F K) ⊗ᴸ Qh(F M) --(μ Qh)--> Qh(F K ⊗ F M)
```
of the counits of `LF` on both factors and the lax monoidal structure of
`Qh : K(D) ⥤ D(D)`. -/
private noncomputable def rightExact_derivedTensorLeftDerivedCounit :
    (((whiskeringLeft₂ _).obj (Qh (C := C))).obj Qh).obj (rightExact_derivedTensorLeftDerived F) ⟶
      (((whiskeringLeft₂ _).obj (F.mapHomotopyCategory (.up ℤ))).obj
        (F.mapHomotopyCategory (.up ℤ))).obj
          ((postcompose₂.obj Qh).obj (curriedTensor _)) :=
  (((whiskeringLeft₂ _).map F.leftDerivedFunctorCounit).app
      (Qh ⋙ F.leftDerivedFunctor)).app (curriedTensor _) ≫
    (((whiskeringLeft₂ _).obj (F.mapHomotopyCategory (.up ℤ) ⋙ Qh)).map
      F.leftDerivedFunctorCounit).app (curriedTensor _) ≫
    (((whiskeringLeft₂ _).obj (F.mapHomotopyCategory (.up ℤ))).obj
        (F.mapHomotopyCategory (.up ℤ))).map (LaxMonoidal.μNatTrans Qh)

/-- The counit exhibiting `(K, M) ↦ LF(K ⊗ᴸ M)` as the total left derived functor of
`(A, B) ↦ F(A ⊗ B)`. On `K, M` in `K(C)` it is the composite
```
 LF(Qh K ⊗ᴸ Qh M) --(LF(μ Qh))--> LF(Qh (K ⊗ M)) --(counit)--> Qh(F(K ⊗ M))
```
-/
private noncomputable def rightExact_leftDerivedDerivedTensorCounit :
    (((whiskeringLeft₂ _).obj (Qh (C := C))).obj Qh).obj (rightExact_leftDerivedDerivedTensor F) ⟶
      (postcompose₂.obj (F.mapHomotopyCategory (.up ℤ) ⋙ Qh)).obj (curriedTensor _) :=
  (postcompose₂.obj F.leftDerivedFunctor).map (LaxMonoidal.μNatTrans Qh) ≫
    (postcompose₂.map F.leftDerivedFunctorCounit).app (curriedTensor _)

private lemma rightExact_derivedTensorLeftDerivedCounit_app_app
    (X₁ X₂ : HomotopyCategory C (.up ℤ)) :
    ((rightExact_derivedTensorLeftDerivedCounit F).app X₁).app X₂ =
      (F.leftDerivedFunctorCounit.app X₁ ⊗ₘ F.leftDerivedFunctorCounit.app X₂) ≫
        LaxMonoidal.μ Qh ((F.mapHomotopyCategory _).obj X₁)
          ((F.mapHomotopyCategory _).obj X₂) := by
  simp [rightExact_derivedTensorLeftDerivedCounit, tensorHom_def]

omit [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
    [BraidedCategory D] [HasFunctorialFlatResolution D] in
private lemma rightExact_leftDerivedDerivedTensorCounit_app_app
    (X₁ X₂ : HomotopyCategory C (.up ℤ)) :
    ((rightExact_leftDerivedDerivedTensorCounit F).app X₁).app X₂ =
      F.leftDerivedFunctor.map (LaxMonoidal.μ Qh X₁ X₂) ≫
        F.leftDerivedFunctorCounit.app (X₁ ⊗ X₂) := by
  simp [rightExact_leftDerivedDerivedTensorCounit]

variable [F.PreservesFlat] [F.IsLeftAdjoint]

/-- `(K, M) ↦ LF K ⊗ᴸ LF M` is the total left derived functor of `(A, B) ↦ F A ⊗ F B`. It is
computed on pairs `(K, M)` with `K` K-flat and `F M` K-flat. -/
private instance isLeftDerivedFunctor₂_rightExact_derivedTensorLeftDerived :
    (rightExact_derivedTensorLeftDerived F).IsLeftDerivedFunctor₂
      (rightExact_derivedTensorLeftDerivedCounit F)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIsoLocalizerMorphism F.tensorGoodModels)
    (HomotopyCategory.quasiIsoLocalizerMorphism F.tensorGoodModels) _ (fun X₁ X₂ ↦ ?_)
  let hμ := isIso_μNatTrans_Qh_app_app_of_kFlat
    ((F.mapHomotopyCategory _).obj X₁.obj) _ X₂.property.2
  have h₁ : IsIso (F.leftDerivedFunctorCounit.app X₁.obj) :=
    F.derives_kFlat.isIso_of_isLeftDerivedFunctor F.leftDerivedFunctorCounit
      ⟨X₁.obj, X₁.property.1⟩
  have h₂ : IsIso (F.leftDerivedFunctorCounit.app X₂.obj) :=
    F.derives_kFlat.isIso_of_isLeftDerivedFunctor F.leftDerivedFunctorCounit
      ⟨X₂.obj, X₂.property.1⟩
  let := h₁
  let := h₂
  change IsIso ((F.leftDerivedFunctorCounit.app X₁.obj ▷ _) ≫
    (_ ◁ F.leftDerivedFunctorCounit.app X₂.obj) ≫
    (((LaxMonoidal.μNatTrans Qh).app
      ((F.mapHomotopyCategory _).obj X₁.obj)).app
      ((F.mapHomotopyCategory _).obj X₂.obj)))
  infer_instance

/-- `(K, M) ↦ LF(K ⊗ᴸ M)` is the total left derived functor of `(A, B) ↦ F(A ⊗ B)`. It is
computed on pairs of K-flat complexes. -/
private instance isLeftDerivedFunctor₂_rightExact_leftDerivedDerivedTensor :
    (rightExact_leftDerivedDerivedTensor F).IsLeftDerivedFunctor₂
      (rightExact_leftDerivedDerivedTensorCounit F)
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat _ (fun X₁ X₂ ↦ ?_)
  let hμ := isIso_μNatTrans_Qh_app_app_of_kFlat X₁.obj _ X₂.property
  have ht : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat (X₁.obj ⊗ X₂.obj) :=
    ObjectProperty.prop_tensor X₁.property X₂.property
  let hε : IsIso (F.leftDerivedFunctorCounit.app (X₁.obj ⊗ X₂.obj)) :=
    F.derives_kFlat.isIso_of_isLeftDerivedFunctor F.leftDerivedFunctorCounit ⟨_, ht⟩
  change IsIso (F.leftDerivedFunctor.map
    (((LaxMonoidal.μNatTrans Qh).app X₁.obj).app X₂.obj) ≫
    F.leftDerivedFunctorCounit.app (X₁.obj ⊗ X₂.obj))
  exact IsIso.comp_isIso'
    (Functor.map_isIso F.leftDerivedFunctor
      (((LaxMonoidal.μNatTrans Qh).app X₁.obj).app X₂.obj)) hε

variable [F.Monoidal]

/-- The comparison `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M` of bifunctors `D(C) ⥤ D(C) ⥤ D(D)`, obtained by
deriving the comonoidal structure `δ` of `F`. It is the unique natural transformation such
that, for `K, M` in `K(C)`, the square
```
  LF(Qh K ⊗ᴸ Qh M) ──comparison──▶ LF(Qh K) ⊗ᴸ LF(Qh M)
          │                                │
          ▼                                ▼
     Qh(F(K ⊗ M)) ──────Qh(δ F)─────▶ Qh(F K ⊗ F M)
```
commutes, the vertical arrows being `rightExact_leftDerivedDerivedTensorCounit` and
`rightExact_derivedTensorLeftDerivedCounit`. -/
private noncomputable def rightExact_leftDerivedTensorComparison :
    rightExact_leftDerivedDerivedTensor F ⟶ rightExact_derivedTensorLeftDerived F :=
  leftDerived₂NatTrans _ (rightExact_derivedTensorLeftDerivedCounit F)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (rightExact_leftDerivedDerivedTensorCounit F)
    (postcompose₂MapWhiskeringLeft₂ (OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F) Qh)

/-- The characterising property of `rightExact_leftDerivedTensorComparison`. -/
private lemma rightExact_leftDerivedTensorComparison_app_app_comp_counit (K M : HomotopyCategory C
  (.up ℤ)) :
    ((F.rightExact_leftDerivedTensorComparison.app (Qh.obj K)).app (Qh.obj M)) ≫
        ((rightExact_derivedTensorLeftDerivedCounit F).app K).app M =
      ((rightExact_leftDerivedDerivedTensorCounit F).app K).app M ≫
        Qh.map (((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app K).app M) :=
  leftDerived₂NatTrans_app_app _ _ _ _ _ _ _ K M

/-- The comparison `LF(K ⊗ᴸ M) ⟶ LF K ⊗ᴸ LF M` is an isomorphism, `F` being strong monoidal. -/
private instance isIso_rightExact_leftDerivedTensorComparison : IsIso
  F.rightExact_leftDerivedTensorComparison := by
  dsimp only [rightExact_leftDerivedTensorComparison]
  infer_instance

attribute [local irreducible] rightExact_leftDerivedTensorComparison

private lemma rightExact_leftDerivedTensorComparison_app_app_comp_tensorHom
    (X₁ X₂ : HomotopyCategory C (.up ℤ)) :
    ((F.rightExact_leftDerivedTensorComparison.app (Qh.obj X₁)).app (Qh.obj X₂)) ≫
        (F.leftDerivedFunctorCounit.app X₁ ⊗ₘ F.leftDerivedFunctorCounit.app X₂) ≫
        LaxMonoidal.μ Qh ((F.mapHomotopyCategory _).obj X₁)
          ((F.mapHomotopyCategory _).obj X₂) =
      F.leftDerivedFunctor.map (LaxMonoidal.μ Qh X₁ X₂) ≫
        F.leftDerivedFunctorCounit.app (X₁ ⊗ X₂) ≫
        Qh.map (((OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ) F).app X₁).app X₂) := by
  have h := F.rightExact_leftDerivedTensorComparison_app_app_comp_counit X₁ X₂
  rw [rightExact_derivedTensorLeftDerivedCounit_app_app,
    rightExact_leftDerivedDerivedTensorCounit_app_app] at h
  simpa using h

private lemma rightExact_comparison_naturality_tensorHom {K₁ K₂ M₁ M₂ : DerivedCategory C}
    (f : K₁ ⟶ K₂) (g : M₁ ⟶ M₂) :
    F.leftDerivedFunctor.map (f ⊗ₘ g) ≫
        (F.rightExact_leftDerivedTensorComparison.app K₂).app M₂ =
      (F.rightExact_leftDerivedTensorComparison.app K₁).app M₁ ≫
        (F.leftDerivedFunctor.map f ⊗ₘ F.leftDerivedFunctor.map g) := by
  have h₁ := congr_app (F.rightExact_leftDerivedTensorComparison.naturality f) M₁
  have h₂ := (F.rightExact_leftDerivedTensorComparison.app K₂).naturality g
  dsimp at h₁ h₂
  rw [tensorHom_def, Functor.map_comp, Category.assoc, h₂, reassoc_of% h₁, tensorHom_def]

private lemma tensorator_Q (P Q : CochainComplex C ℤ) :
    LaxMonoidal.μ DerivedCategory.Q P Q =
      ((DerivedCategory.quotientCompQhIso C).inv.app P ⊗ₘ
        (DerivedCategory.quotientCompQhIso C).inv.app Q) ≫
      LaxMonoidal.μ Qh ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj Q) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app
        (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q) := by
  change (_ ⊗ₘ _) ≫ (_ ≫ Qh.map (𝟙 _)) ≫ _ = _
  simp only [Qh.map_id, Category.comp_id]
  rfl

attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh

private lemma rightExact_comparison_cochain (P Q : CochainComplex C ℤ) :
    F.leftDerivedFunctor.map (LaxMonoidal.μ (DerivedCategory.Q (C := C)) P Q) ≫
        F.rightExact_cochainCounit (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q) ≫
        (DerivedCategory.Q (C := D)).map
          (((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q) =
      (F.rightExact_leftDerivedTensorComparison.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q) ≫
        (F.rightExact_cochainCounit P ⊗ₘ F.rightExact_cochainCounit Q) ≫
        LaxMonoidal.μ (DerivedCategory.Q (C := D))
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) := by
  rw [tensorator_Q, tensorator_Q]
  let p := HomotopyCategory.quotient C (.up ℤ)
  let q := HomotopyCategory.quotient D (.up ℤ)
  let e := DerivedCategory.quotientCompQhIso C
  let e' := DerivedCategory.quotientCompQhIso D
  let δ := ((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q
  have h := F.rightExact_leftDerivedTensorComparison_app_app_comp_tensorHom
    (p.obj P) (p.obj Q)
  have ht := transport_tensor_counit
    (C := DerivedCategory C) (D := DerivedCategory D) F.leftDerivedFunctor (e.app P) (e.app Q)
    (e.app (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q))
    (e'.app ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (e'.app ((F.mapHomologicalComplex (.up ℤ)).obj Q))
    (e'.app ((F.mapHomologicalComplex (.up ℤ)).obj
      (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q)))
    (e'.app (((curriedTensor (CochainComplex D ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj Q)))
    (LaxMonoidal.μ (Qh (C := C)) (p.obj P) (p.obj Q))
    (LaxMonoidal.μ (Qh (C := D)) (q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
      (q.obj ((F.mapHomologicalComplex (.up ℤ)).obj Q)))
    (F.leftDerivedFunctorCounit.app (p.obj P))
    (F.leftDerivedFunctorCounit.app (p.obj Q))
    (F.leftDerivedFunctorCounit.app (p.obj (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q)))
    ((Qh (C := D)).map (q.map δ)) ((DerivedCategory.Q (C := D)).map δ)
    ((F.rightExact_leftDerivedTensorComparison.app (Qh.obj (p.obj P))).app (Qh.obj (p.obj Q)))
    ((F.rightExact_leftDerivedTensorComparison.app (DerivedCategory.Q.obj P)).app
      (DerivedCategory.Q.obj Q))
    (F.rightExact_comparison_naturality_tensorHom (e.inv.app P) (e.inv.app Q)) h
    (DerivedCategory.quotientCompQhIso_hom_naturality δ)
  dsimp only [p, q, e, e', δ] at ht
  unfold rightExact_cochainCounit
  dsimp only [Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Iso.app_hom, Iso.app_inv, MonoidalCategory.curriedTensor_obj_obj] at ht ⊢
  simpa only [Category.assoc] using ht

end Comparison

omit [HasFunctorialFlatResolution D] in
private theorem good_representative
    (F : C ⥤ D) [F.Additive] [F.PreservesFlat] [F.IsLeftAdjoint]
    (N : DerivedCategory C) :
    ∃ P : CochainComplex C ℤ,
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P ∧
      (∀ i, ObjectProperty.flat (P.X i)) ∧
      (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
        ((F.mapHomologicalComplex (.up ℤ)).obj P) ∧ Nonempty (Q.obj P ≅ N) := by
  let Λ : LeftResolution (ObjectProperty.flat.ι : _ ⥤ C) := Classical.arbitrary _
  let K := Q.objPreimage N
  refine ⟨Λ.reduced.resolutionFunctor.obj K,
    Λ.reduced.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K, ?_,
    F.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ.reduced
      ObjectProperty.flat.essImage_ι_le K,
    ⟨asIso (Q.map (Λ.reduced.resolutionNatTrans.app K)) ≪≫ Q.objObjPreimageIso N⟩⟩
  intro n
  have := CochainComplex.closedUnderColimitsOfShape_flat C ℤ
  let c := Λ.reduced.colimitOfShapeResolutionFunctorObj K
  exact ObjectProperty.prop_of_isColimit _
    (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) n) c.isColimit)
    (fun i ↦ ObjectProperty.flat.essImage_ι_le _ ((c.prop_diag_obj i).1 n))

omit [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
    [BraidedCategory D] [HasFunctorialFlatResolution D] in
private lemma rightExact_cochainCounit_isIso
    (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]
    (P : CochainComplex C ℤ) (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P) :
    IsIso (F.rightExact_cochainCounit P) := by
  have h : IsIso (F.leftDerivedFunctorCounit.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)) :=
    F.derives_kFlat.isIso_of_isLeftDerivedFunctor F.leftDerivedFunctorCounit
      ⟨_, (HomotopyCategory.kFlat_quotient_obj_iff P).2 hP⟩
  unfold rightExact_cochainCounit
  infer_instance

private lemma tensorator_Q_isIso (P Q : CochainComplex C ℤ)
    (hQ : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q) :
    IsIso (LaxMonoidal.μ (DerivedCategory.Q (C := C)) P Q) := by
  have h := isIso_μNatTrans_Qh_app_app_of_kFlat
    ((HomotopyCategory.quotient C (.up ℤ)).obj P)
    ((HomotopyCategory.quotient C (.up ℤ)).obj Q)
    ((HomotopyCategory.kFlat_quotient_obj_iff Q).2 hQ)
  rw [tensorator_Q]
  change IsIso ((_ ⊗ₘ _) ≫
    ((LaxMonoidal.μNatTrans (Qh (C := C))).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj Q) ≫ _)
  infer_instance

section TransportedComparison

variable (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
  (G : DerivedCategory C ⥤ DerivedCategory D) (e : G ≅ F.leftDerivedFunctor)

private noncomputable def normalizedTensorIso :
    ∀ K L : DerivedCategory C, G.obj K ⊗ G.obj L ≅ G.obj (K ⊗ L) :=
  fun K L ↦ ((tensorConjugate G F.leftDerivedFunctor e
    (asIso F.rightExact_leftDerivedTensorComparison)).symm.app K).app L

attribute [local irreducible] normalizedTensorIso

private lemma normalizedTensorIso_natural₁ {K K' : DerivedCategory C} (f : K ⟶ K')
    (L : DerivedCategory C) :
    (G.map f ▷ G.obj L) ≫ (normalizedTensorIso F G e K' L).hom =
      (normalizedTensorIso F G e K L).hom ≫ G.map (f ▷ L) := by
  unfold normalizedTensorIso
  exact congr_app ((tensorConjugate G F.leftDerivedFunctor e
    (asIso F.rightExact_leftDerivedTensorComparison)).inv.naturality f) L

private lemma normalizedTensorIso_natural₂ (K : DerivedCategory C)
    {L L' : DerivedCategory C} (f : L ⟶ L') :
    (G.obj K ◁ G.map f) ≫ (normalizedTensorIso F G e K L').hom =
      (normalizedTensorIso F G e K L).hom ≫ G.map (K ◁ f) := by
  unfold normalizedTensorIso
  exact ((tensorConjugate G F.leftDerivedFunctor e
    (asIso F.rightExact_leftDerivedTensorComparison)).inv.app K).naturality f

private lemma normalizedTensorIso_inv (K L : DerivedCategory C) :
    (normalizedTensorIso F G e K L).inv =
      e.hom.app (K ⊗ L) ≫
        (F.rightExact_leftDerivedTensorComparison.app K).app L ≫
          (e.inv.app K ⊗ₘ e.inv.app L) := by
  unfold normalizedTensorIso
  exact tensorConjugate_hom G F.leftDerivedFunctor e
    (asIso F.rightExact_leftDerivedTensorComparison) K L

end TransportedComparison

end CachedMonoidalStructures

/-- The ordinary oplax tensorator equation on flat-term K-flat models.
Source: Stacks 06YY and 07A4. This predicate keeps the cochain equation behind
one interface when the coefficient category is specialized to sheaves.
(blueprint: lem-derived-right-exact-tensor-comparison). -/
def rightExactTensorModelNormalization
    (F : C ⥤ D) [F.Additive] [F.IsLeftAdjoint] [F.OplaxMonoidal]
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (r : ∀ P : CochainComplex C ℤ,
      G.obj ((DerivedCategory.Q (C := C)).obj P) ⟶
        (DerivedCategory.Q (C := D)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (μ : ∀ K L : DerivedCategory C,
      ((curriedTensor (DerivedCategory D)).obj (G.obj K)).obj (G.obj L) ≅
        G.obj (((curriedTensor (DerivedCategory C)).obj K).obj L)) : Prop :=
  ∀ P Q : CochainComplex C ℤ,
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P →
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q →
    (∀ i, ObjectProperty.flat (P.X i)) → (∀ i, ObjectProperty.flat (Q.X i)) →
    G.map (LaxMonoidal.μ (DerivedCategory.Q (C := C)) P Q) ≫
      r (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q) ≫
        (DerivedCategory.Q (C := D)).map
          (((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q) =
      (μ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).inv ≫
        (r P ⊗ₘ r Q) ≫ LaxMonoidal.μ (DerivedCategory.Q (C := D))
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q)

/-- A strong monoidal left adjoint preserving flat objects has a uniquely normalized
binary comparison on its total left derived functor, and on any isomorphic functor.
Source: the universal property of total left derived bifunctors, computed on flat
K-flat resolutions; Stacks 06YY and 07A4.
Proof: derive the ordinary oplax tensorator on pairs of K-flat models whose images
are K-flat. Flat resolutions supply those models. Both derived counits are invertible
there, so the comparison is an isomorphism. Transport it along the given functor
isomorphism. The cochain counit equation follows from the homotopy counit equation.
Every object has a flat K-flat representative with K-flat image, and on two such
representatives the normalization determines the inverse comparison by cancellation.
Naturality transports this equality to every pair of derived objects.
(blueprint: lem-derived-right-exact-tensor-comparison). -/
theorem rightExact_tensorComparison_existsUnique
    (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
    (G : DerivedCategory C ⥤ DerivedCategory D) (e : G ≅ F.leftDerivedFunctor)
    (r : ∀ P : CochainComplex C ℤ,
      G.obj ((DerivedCategory.Q (C := C)).obj P) ⟶
        (DerivedCategory.Q (C := D)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (hr : ∀ P, r P = e.hom.app (DerivedCategory.Q.obj P) ≫ F.rightExact_cochainCounit P) :
    ∃! μ : ∀ K L : DerivedCategory C,
      ((curriedTensor (DerivedCategory D)).obj (G.obj K)).obj (G.obj L) ≅
        G.obj (((curriedTensor (DerivedCategory C)).obj K).obj L),
      (∀ {K K'} (f : K ⟶ K') L,
        ((curriedTensor (DerivedCategory D)).map (G.map f)).app (G.obj L) ≫ (μ K' L).hom =
          (μ K L).hom ≫ G.map (((curriedTensor (DerivedCategory C)).map f).app L)) ∧
      (∀ K {L L'} (f : L ⟶ L'),
        ((curriedTensor (DerivedCategory D)).obj (G.obj K)).map (G.map f) ≫ (μ K L').hom =
          (μ K L).hom ≫ G.map (((curriedTensor (DerivedCategory C)).obj K).map f)) ∧
      rightExactTensorModelNormalization F G r μ := by
  unfold rightExactTensorModelNormalization
  change ∃! μ : ∀ K L : DerivedCategory C, G.obj K ⊗ G.obj L ≅ G.obj (K ⊗ L),
      (∀ {K K'} (f : K ⟶ K') L,
        (G.map f ▷ G.obj L) ≫ (μ K' L).hom = (μ K L).hom ≫ G.map (f ▷ L)) ∧
      (∀ K {L L'} (f : L ⟶ L'),
        (G.obj K ◁ G.map f) ≫ (μ K L').hom = (μ K L).hom ≫ G.map (K ◁ f)) ∧
      (∀ P Q : CochainComplex C ℤ,
        (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P →
        (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q →
        (∀ i, ObjectProperty.flat (P.X i)) → (∀ i, ObjectProperty.flat (Q.X i)) →
        G.map (LaxMonoidal.μ (DerivedCategory.Q (C := C)) P Q) ≫
          r (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q) ≫
            (DerivedCategory.Q (C := D)).map
              (((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q) =
          (μ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).inv ≫
            (r P ⊗ₘ r Q) ≫ LaxMonoidal.μ (DerivedCategory.Q (C := D))
              ((F.mapHomologicalComplex (.up ℤ)).obj P)
              ((F.mapHomologicalComplex (.up ℤ)).obj Q))
  let μ := normalizedTensorIso F G e
  have hn₁ : ∀ {K K'} (f : K ⟶ K') L,
      (G.map f ▷ G.obj L) ≫ (μ K' L).hom = (μ K L).hom ≫ G.map (f ▷ L) :=
    fun {K K'} f L ↦ normalizedTensorIso_natural₁ F G e f L
  have hn₂ : ∀ K {L L'} (f : L ⟶ L'),
      (G.obj K ◁ G.map f) ≫ (μ K L').hom = (μ K L).hom ≫ G.map (K ◁ f) :=
    fun K {L L'} f ↦ normalizedTensorIso_natural₂ F G e K f
  have hm : ∀ P Q : CochainComplex C ℤ,
      G.map (LaxMonoidal.μ (DerivedCategory.Q (C := C)) P Q) ≫
        r (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q) ≫
          (DerivedCategory.Q (C := D)).map
            (((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q) =
        (μ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).inv ≫
          (r P ⊗ₘ r Q) ≫ LaxMonoidal.μ (DerivedCategory.Q (C := D))
            ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj Q) := by
    intro P Q
    simp only [hr]
    dsimp only [μ]
    rw [normalizedTensorIso_inv]
    simpa only [Category.assoc] using
      transfer_tensor_counit (C := DerivedCategory C) (D := DerivedCategory D)
        G F.leftDerivedFunctor e
        (T := DerivedCategory.Q.obj (((curriedTensor (CochainComplex C ℤ)).obj P).obj Q))
        _ _ _ _ _ _
        (F.rightExact_comparison_cochain P Q)
  refine ⟨μ, ⟨hn₁, hn₂, fun P Q _ _ _ _ ↦ hm P Q⟩, ?_⟩
  intro ν hν
  apply binaryIso_ext_of_representatives
    (C := DerivedCategory C) (D := DerivedCategory D) (H := CochainComplex C ℤ)
    (curriedTensor _) (curriedTensor _) G
    (DerivedCategory.Q (C := C))
    (fun P ↦ (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P ∧
      (∀ i, ObjectProperty.flat (P.X i)) ∧
      (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
        ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (fun K ↦ by
      obtain ⟨P, h₁, h₂, h₃, h₄⟩ := good_representative F K
      exact ⟨P, ⟨h₁, h₂, h₃⟩, h₄⟩) ν μ hν.1 hν.2.1 hn₁ hn₂
  intro P Q hP hQ
  have hrP : IsIso (r P) := by
    rw [hr]
    exact IsIso.comp_isIso' (NatIso.hom_app_isIso e _)
      (F.rightExact_cochainCounit_isIso P hP.1)
  have hrQ : IsIso (r Q) := by
    rw [hr]
    exact IsIso.comp_isIso' (NatIso.hom_app_isIso e _)
      (F.rightExact_cochainCounit_isIso Q hQ.1)
  have hμQ := tensorator_Q_isIso
    ((F.mapHomologicalComplex (.up ℤ)).obj P)
    ((F.mapHomologicalComplex (.up ℤ)).obj Q) hQ.2.2
  apply Iso.ext_inv
  apply (cancel_mono ((r P ⊗ₘ r Q) ≫ LaxMonoidal.μ (DerivedCategory.Q (C := D))
    ((F.mapHomologicalComplex (.up ℤ)).obj P)
    ((F.mapHomologicalComplex (.up ℤ)).obj Q))).1
  exact (hν.2.2 P Q hP.1 hQ.1 hP.2.1 hQ.2.1).symm.trans (hm P Q)

end CategoryTheory.Functor
