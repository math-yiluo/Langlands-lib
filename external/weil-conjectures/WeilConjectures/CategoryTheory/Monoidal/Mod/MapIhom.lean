/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular

/-!
# Compatibility of the internal hom of modules with monoidal equivalences

Let `G : Mod C A ⥤ Mod D B` be the equivalence of categories of modules induced by a monoidal
functor (`CategoryTheory.Mod.mapModComap`). It commutes with tensor products
(`CategoryTheory.Mod.tensorLeftCompMapModComapIso`), hence with internal homs
(`CategoryTheory.Mod.mapModComapCompIhomIso`). This file shows that the latter comparison is
natural in the first variable and compatible with `Hom_A(A, -) ≅ 𝟭`.

## Main statements

- `CategoryTheory.Mod.mapModComapCompIhomIso_inv_app_comp_ihomMap`: naturality of
  `G Hom_A(M, N) ≅ Hom_B(G M, G N)` in `M`.
- `CategoryTheory.Mod.map_ihomRegularIso_inv_app_comp_mapModComapCompIhomIso_inv_app`:
  compatibility with `Hom_A(A, -) ≅ 𝟭`.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Adjunction

variable {𝒜 : Type*} {ℬ : Type*} [Category 𝒜] [Category ℬ] (E : 𝒜 ≌ ℬ)
  {T I : 𝒜 ⥤ 𝒜} (adj : T ⊣ I) {T' I' : ℬ ⥤ ℬ} (adj' : T' ⊣ I')

/-- If `T' ≅ E⁻¹ ⋙ T ⋙ E` for adjunctions `T ⊣ I`, `T' ⊣ I'` and an equivalence `E`, then
`E ⋙ I' ≅ I ⋙ E`. -/
noncomputable def equivalenceCompRightAdjointIsoOfIso (t : E.inverse ⋙ T ⋙ E.functor ≅ T') :
    E.functor ⋙ I' ≅ I ⋙ E.functor :=
  Functor.isoWhiskerLeft E.functor (adj'.rightAdjointUniq
      ((((E.symm.toAdjunction.comp adj).comp E.toAdjunction).ofNatIsoLeft
        (Functor.associator _ _ _)).ofNatIsoLeft t)) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight E.unitIso.symm _ ≪≫
    Functor.leftUnitor _

lemma map_equivalenceCompRightAdjointIsoOfIso_inv_app_counit
    (t : E.inverse ⋙ T ⋙ E.functor ≅ T') (N : 𝒜) :
    T'.map ((equivalenceCompRightAdjointIsoOfIso E adj adj' t).inv.app N) ≫
        adj'.counit.app (E.functor.obj N) =
      t.inv.app (E.functor.obj (I.obj N)) ≫ E.functor.map (T.map (E.unitInv.app (I.obj N))) ≫
        E.functor.map (adj.counit.app N) := by
  simp only [Functor.comp_obj, Functor.id_obj, equivalenceCompRightAdjointIsoOfIso,
    Equivalence.symm_inverse, Equivalence.symm_functor, Iso.trans_inv, Functor.isoWhiskerRight_inv,
    Iso.symm_inv, Category.assoc, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.associator_hom_app, Functor.whiskerLeft_app, rightAdjointUniq_inv_app,
    Category.id_comp, Functor.map_comp, rightAdjointUniq_hom_app_counit, ofNatIsoLeft_counit,
    Functor.associator_inv_app, comp_counit_app, Equivalence.toAdjunction_counit,
    Equivalence.symm_counit, NatTrans.naturality_assoc, Equivalence.inv_fun_map, cancelIso,
    NatIso.cancel_natIso_inv_left]
  congr 1
  rw [← Functor.map_comp_assoc, adj.counit_naturality, Functor.map_comp, Category.assoc,
    E.functor_unitIso_comp, Category.comp_id]

/-- If the left adjoints `T ⊣ I` and `T' ⊣ I'` commute with an equivalence `E`, so do the right
adjoints: `E ⋙ I' ≅ I ⋙ E`. -/
noncomputable def equivalenceCompRightAdjointIso (t : T ⋙ E.functor ≅ E.functor ⋙ T') :
    E.functor ⋙ I' ≅ I ⋙ E.functor :=
  equivalenceCompRightAdjointIsoOfIso E adj adj'
    (Functor.isoWhiskerLeft E.inverse t ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.counitIso _ ≪≫ Functor.leftUnitor _)

/-- The adjoint transpose of `E (I N) ⟶ I' (E N)` is `T' (E (I N)) ≅ E (T (I N)) ⟶ E N`. -/
lemma map_equivalenceCompRightAdjointIso_inv_app_counit (t : T ⋙ E.functor ≅ E.functor ⋙ T')
    (N : 𝒜) :
    T'.map ((equivalenceCompRightAdjointIso E adj adj' t).inv.app N) ≫
        adj'.counit.app (E.functor.obj N) =
      t.inv.app (I.obj N) ≫ E.functor.map (adj.counit.app N) := by
  rw [equivalenceCompRightAdjointIso, map_equivalenceCompRightAdjointIsoOfIso_inv_app_counit]
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Iso.symm_inv,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Category.id_comp, Category.assoc]
  erw [Equivalence.counitInv_app_functor]
  erw [← Functor.comp_map E.functor T', t.inv.naturality_assoc, Functor.comp_map,
    ← Functor.map_comp_assoc, ← T.map_comp, E.unitIso.hom_inv_id_app, T.map_id,
    E.functor.map_id, Category.id_comp]
  rfl

end CategoryTheory.Adjunction

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]

section TensorLeft

variable [BraidedCategory C] [IsCommMonObj A] [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)]

/-- The quotient map `P ⊗ M ⟶ P ⊗_A M`. -/
noncomputable abbrev tensorLeftπ (M P : Mod C A) :
    (tensorRight A M.X).obj P ⟶ (tensorLeft M).obj P :=
  colimit.ι ((tensorLeftDiagram A M).flip.obj P) WalkingParallelPair.one

lemma tensorLeftπ_naturality (M : Mod C A) {P Q : Mod C A} (f : P ⟶ Q) :
    tensorLeftπ M P ≫ (tensorLeft M).map f = (tensorRight A M.X).map f ≫ tensorLeftπ M Q := by
  simp [tensorLeft]

lemma tensorLeftπ_tensorLeftMap_app {M M' : Mod C A} (f : M ⟶ M') (P : Mod C A) :
    tensorLeftπ M P ≫ (tensorLeftMap f).app P =
      (tensorRightMap A f.hom).app P ≫ tensorLeftπ M' P := by
  simp [tensorLeftMap, tensorLeftDiagramMap]

lemma tensorLeftπ_tensorLeftRegularHom_app (P : Mod C A) :
    tensorLeftπ (regular A) P ≫ tensorLeftRegularHom.app P = rightActHom P := by
  simp [tensorLeftRegularHom]

lemma tensorLeft_hom_ext (M P : Mod C A) {Z : Mod C A} {f g : (tensorLeft M).obj P ⟶ Z}
    (h : tensorLeftπ M P ≫ f = tensorLeftπ M P ≫ g) : f = g := by
  refine colimit.hom_ext fun j ↦ ?_
  cases j
  · rw [← colimit.w ((tensorLeftDiagram A M).flip.obj P) WalkingParallelPairHom.left,
      Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) h
  · exact h

end TensorLeft

section Hom

variable [BraidedCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

attribute [local instance] Mod.isGrothendieckAbelian

lemma tensorLeft_map_ihomMap_app_counit {M M' : Mod C A} (f : M ⟶ M') (N : Mod C A) :
    (tensorLeft M).map ((ihomMap f).app N) ≫ (ihomAdjunction M).counit.app N =
      (tensorLeftMap f).app ((ihom M').obj N) ≫ (ihomAdjunction M').counit.app N :=
  conjugateEquiv_counit _ _ _ _

lemma ihom_hom_ext {M P N : Mod C A} {f g : P ⟶ (ihom M).obj N}
    (h : (tensorLeft M).map f ≫ (ihomAdjunction M).counit.app N =
      (tensorLeft M).map g ≫ (ihomAdjunction M).counit.app N) : f = g := by
  apply ((ihomAdjunction M).homEquiv _ _).symm.injective
  simpa only [Adjunction.homEquiv_counit] using h

lemma tensorLeft_map_ihomRegularIso_inv_app_counit (N : Mod C A) :
    (tensorLeft (regular A)).map (ihomRegularIso.inv.app N) ≫
        (ihomAdjunction (regular A)).counit.app N = tensorLeftRegularHom.app N := by
  rw [ihomRegularIso, Adjunction.rightAdjointUniq_inv_app,
    Adjunction.rightAdjointUniq_hom_app_counit]
  simp [tensorLeftRegularIso]

end Hom

section TensorFunctor

open scoped Obj

variable [BraidedCategory C] [IsCommMonObj A] [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {B : D} [MonObj B]
  [BraidedCategory D] [IsCommMonObj B] [HasColimitsOfShape WalkingParallelPair D]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft B)]
  {G : C ⥤ D} [G.LaxMonoidal] [∀ X Y : C, IsIso (Functor.LaxMonoidal.μ G X Y)]
  (ρ : B ⟶ G.obj A) [IsMonHom ρ] [IsIso ρ]
  (hβ : ∀ X Y : C, Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
      (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X)
  [PreservesColimitsOfShape WalkingParallelPair (mapModComap ρ)]

omit [BraidedCategory D] [IsCommMonObj B] [HasColimitsOfShape WalkingParallelPair D]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft B)]
  [∀ X Y : C, IsIso (Functor.LaxMonoidal.μ G X Y)] [IsIso ρ] in
lemma mapModComap_tensorLeft_hom_ext (M P : Mod C A) {Z : Mod D B}
    {f g : (mapModComap ρ).obj ((tensorLeft M).obj P) ⟶ Z}
    (h : (mapModComap ρ).map (tensorLeftπ M P) ≫ f = (mapModComap ρ).map (tensorLeftπ M P) ≫ g) :
    f = g := by
  refine (isColimitOfPreserves (mapModComap ρ) (colimit.isColimit _)).hom_ext fun j ↦ ?_
  cases j
  · have hw := colimit.w ((tensorLeftDiagram A M).flip.obj P) WalkingParallelPairHom.left
    simp only [Functor.mapCocone_ι_app, colimit.cocone_ι]
    rw [← hw, Functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) h
  · exact h

lemma map_tensorLeftπ_tensorLeftCompMapModComapIso_hom_app (M P : Mod C A) :
    (mapModComap ρ).map (tensorLeftπ M P) ≫ (tensorLeftCompMapModComapIso ρ hβ M).hom.app P =
      ((tensorRightCompMapModComapIso ρ M.X).app P).hom ≫ tensorLeftπ ((mapModComap ρ).obj M)
        ((mapModComap ρ).obj P) := by
  simp only [tensorLeftCompMapModComapIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    preservesColimitNatIso_hom_app]
  erw [Category.id_comp, ι_preservesColimitIso_hom_assoc, Category.id_comp, Category.comp_id]
  erw [colim_map, ι_colimMap]
  rfl


/-- The comparison `G (P ⊗_A M) ≅ G P ⊗_B G M` is natural in `M`. -/
lemma map_tensorLeftMap_app_tensorLeftCompMapModComapIso_hom_app {M M' : Mod C A} (f : M ⟶ M')
    (P : Mod C A) :
    (mapModComap ρ).map ((tensorLeftMap f).app P) ≫
        (tensorLeftCompMapModComapIso ρ hβ M').hom.app P =
      (tensorLeftCompMapModComapIso ρ hβ M).hom.app P ≫
        (tensorLeftMap ((mapModComap ρ).map f)).app ((mapModComap ρ).obj P) := by
  refine mapModComap_tensorLeft_hom_ext ρ M P ?_
  rw [← Functor.map_comp_assoc, tensorLeftπ_tensorLeftMap_app, Functor.map_comp_assoc,
    map_tensorLeftπ_tensorLeftCompMapModComapIso_hom_app]
  erw [reassoc_of% map_tensorLeftπ_tensorLeftCompMapModComapIso_hom_app,
    tensorLeftπ_tensorLeftMap_app]
  rw [← Category.assoc, ← Category.assoc]
  refine congrArg (· ≫ _) (Mod.hom_ext _ _ ?_)
  change G.map (P.X ◁ f.hom) ≫ inv (Functor.LaxMonoidal.μ G P.X M'.X) =
    inv (Functor.LaxMonoidal.μ G P.X M.X) ≫ G.obj P.X ◁ G.map f.hom
  rw [IsIso.comp_inv_eq, Category.assoc, Functor.LaxMonoidal.μ_natural_right,
    IsIso.inv_hom_id_assoc]


/-- The comparison `G (P ⊗_A A) ≅ G P ⊗_B G A` is compatible with `P ⊗_A A ≅ P`, for an
identification `G A ≅ B` of `B`-modules inverse to `ρ`. -/
lemma tensorLeftCompMapModComapIso_hom_app_regular (ψ : (mapModComap ρ).obj (regular A) ≅ regular B)
    (hψ : ψ.hom.hom = inv ρ) (P : Mod C A) :
    (tensorLeftCompMapModComapIso ρ hβ (regular A)).hom.app P ≫
        (tensorLeftMap ψ.hom).app ((mapModComap ρ).obj P) ≫
          tensorLeftRegularHom.app ((mapModComap ρ).obj P) =
      (mapModComap ρ).map (tensorLeftRegularHom.app P) := by
  refine mapModComap_tensorLeft_hom_ext ρ (regular A) P ?_
  rw [← Functor.map_comp, tensorLeftπ_tensorLeftRegularHom_app]
  erw [reassoc_of% map_tensorLeftπ_tensorLeftCompMapModComapIso_hom_app,
    reassoc_of% tensorLeftπ_tensorLeftMap_app, tensorLeftπ_tensorLeftRegularHom_app]
  refine Mod.hom_ext _ _ ?_
  change inv (Functor.LaxMonoidal.μ G P.X A) ≫ G.obj P.X ◁ ψ.hom.hom ≫ (β_ (G.obj P.X) B).hom ≫
      ρ ▷ G.obj P.X ≫ Functor.LaxMonoidal.μ G A P.X ≫ G.map (act P.X) =
    G.map ((β_ P.X A).hom ≫ act P.X)
  rw [hψ]
  erw [BraidedCategory.braiding_naturality_right_assoc]
  rw [← comp_whiskerRight_assoc,
    IsIso.inv_hom_id, id_whiskerRight, Category.id_comp, ← reassoc_of% hβ,
    IsIso.inv_hom_id_assoc, Functor.map_comp]


end TensorFunctor

section HomFunctor

open scoped Obj

variable [BraidedCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {B : D} [MonObj B]
  [BraidedCategory D] [IsCommMonObj B] [Abelian D] [MonoidalPreadditive D]
  [IsGrothendieckAbelian.{v'} D]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorLeft X)]
  [∀ X : D, PreservesColimitsOfSize.{v', v'} (MonoidalCategory.tensorRight X)]
  {G : C ⥤ D} [G.LaxMonoidal] [∀ X Y : C, IsIso (Functor.LaxMonoidal.μ G X Y)]
  (ρ : B ⟶ G.obj A) [IsMonHom ρ] [IsIso ρ]
  (hβ : ∀ X Y : C, Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
      (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X)
  [(mapModComap ρ).IsEquivalence]

attribute [local instance] Mod.isGrothendieckAbelian

lemma mapModComapCompIhomIso_eq (M : Mod C A) :
    mapModComapCompIhomIso ρ hβ M = Adjunction.equivalenceCompRightAdjointIso
      (mapModComap ρ).asEquivalence (ihomAdjunction M) (ihomAdjunction ((mapModComap ρ).obj M))
      (tensorLeftCompMapModComapIso ρ hβ M) :=
  rfl

/-- The adjoint transpose of `G Hom_A(M, N) ⟶ Hom_B(G M, G N)` is
`G Hom_A(M, N) ⊗_B G M ≅ G (Hom_A(M, N) ⊗_A M) ⟶ G N`. -/
lemma tensorLeft_map_mapModComapCompIhomIso_inv_app_counit (M N : Mod C A) :
    (tensorLeft ((mapModComap ρ).obj M)).map ((mapModComapCompIhomIso ρ hβ M).inv.app N) ≫
        (ihomAdjunction ((mapModComap ρ).obj M)).counit.app ((mapModComap ρ).obj N) =
      (tensorLeftCompMapModComapIso ρ hβ M).inv.app ((ihom M).obj N) ≫
        (mapModComap ρ).map ((ihomAdjunction M).counit.app N) := by
  rw [mapModComapCompIhomIso_eq]
  exact Adjunction.map_equivalenceCompRightAdjointIso_inv_app_counit _ _ _ _ N


/-- **Naturality in `M`** of the comparison `G Hom_A(M, N) ≅ Hom_B(G M, G N)`. -/
lemma mapModComapCompIhomIso_inv_app_comp_ihomMap {M M' : Mod C A} (f : M ⟶ M')
    (N : Mod C A) :
    (mapModComapCompIhomIso ρ hβ M').inv.app N ≫
        (ihomMap ((mapModComap ρ).map f)).app ((mapModComap ρ).obj N) =
      (mapModComap ρ).map ((ihomMap f).app N) ≫ (mapModComapCompIhomIso ρ hβ M).inv.app N := by
  have hT := map_tensorLeftMap_app_tensorLeftCompMapModComapIso_hom_app ρ hβ f
    ((ihom M').obj N)
  have hT' : (tensorLeftCompMapModComapIso ρ hβ M).inv.app ((ihom M').obj N) ≫
      (mapModComap ρ).map ((tensorLeftMap f).app ((ihom M').obj N)) =
      (tensorLeftMap ((mapModComap ρ).map f)).app ((mapModComap ρ).obj ((ihom M').obj N)) ≫
        (tensorLeftCompMapModComapIso ρ hβ M').inv.app ((ihom M').obj N) := by
    rw [← cancel_epi ((tensorLeftCompMapModComapIso ρ hβ M).hom.app _),
      Iso.hom_inv_id_app_assoc]
    erw [← reassoc_of% hT, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  refine ihom_hom_ext ?_
  rw [Functor.map_comp, Category.assoc, tensorLeft_map_ihomMap_app_counit]
  erw [NatTrans.naturality_assoc]
  rw [tensorLeft_map_mapModComapCompIhomIso_inv_app_counit,
    Functor.map_comp, Category.assoc, tensorLeft_map_mapModComapCompIhomIso_inv_app_counit]
  erw [(tensorLeftCompMapModComapIso ρ hβ M).inv.naturality_assoc]
  erw [← (mapModComap ρ).map_comp]
  rw [tensorLeft_map_ihomMap_app_counit, Functor.map_comp]
  erw [reassoc_of% hT']
  rfl


/-- The comparison `G Hom_A(A, N) ≅ Hom_B(G A, G N)` is compatible with `Hom_A(A, -) ≅ 𝟭`, for an
identification `G A ≅ B` of `B`-modules inverse to `ρ`. -/
lemma map_ihomRegularIso_inv_app_comp_mapModComapCompIhomIso_inv_app
    (ψ : (mapModComap ρ).obj (regular A) ≅ regular B) (hψ : ψ.hom.hom = inv ρ) (N : Mod C A) :
    (mapModComap ρ).map (ihomRegularIso.inv.app N) ≫
        (mapModComapCompIhomIso ρ hβ (regular A)).inv.app N =
      ihomRegularIso.inv.app ((mapModComap ρ).obj N) ≫
        (ihomMap ψ.hom).app ((mapModComap ρ).obj N) := by
  have hT := tensorLeftCompMapModComapIso_hom_app_regular ρ hβ ψ hψ N
  have hT' : (tensorLeftCompMapModComapIso ρ hβ (regular A)).inv.app N ≫
      (mapModComap ρ).map (tensorLeftRegularHom.app N) =
      (tensorLeftMap ψ.hom).app ((mapModComap ρ).obj N) ≫
        tensorLeftRegularHom.app ((mapModComap ρ).obj N) := by
    rw [← hT, Iso.inv_hom_id_app_assoc]
  refine ihom_hom_ext ?_
  rw [Functor.map_comp, Category.assoc, tensorLeft_map_mapModComapCompIhomIso_inv_app_counit,
    Functor.map_comp, Category.assoc, tensorLeft_map_ihomMap_app_counit]
  erw [(tensorLeftCompMapModComapIso ρ hβ (regular A)).inv.naturality_assoc,
    NatTrans.naturality_assoc]
  erw [← (mapModComap ρ).map_comp]
  rw [tensorLeft_map_ihomRegularIso_inv_app_counit]
  erw [tensorLeft_map_ihomRegularIso_inv_app_counit]
  exact hT'

end HomFunctor

end CategoryTheory.Mod
