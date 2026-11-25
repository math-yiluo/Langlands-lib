/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Transfer between additive Čech resolution double complexes
Source: Stacks Project, Tag 01FD, the identity-morphism case of the augmentation diagram.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma canonical_transfer_identity {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I J : InjectiveResolution G) (φ : InjectiveResolution.Hom I J (𝟙 G))
    (cI : Etale.ResolutionSectionCanonicalComparison G I)
    (cJ : Etale.ResolutionSectionCanonicalComparison G J) (n : ℕ)
    (x : (((Etale.etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex).homology n) :
    cJ.globalEquiv n (HomologicalComplex.homologyMap
      (((Etale.etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex
        (.up ℕ)).map φ.hom) n x) = cI.globalEquiv n x := by
  let E := Etale.etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))
  let K := (E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let L := (E.mapHomologicalComplex (.up ℕ)).obj J.cocomplex
  let f := (E.mapHomologicalComplex (.up ℕ)).map φ.hom
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance x
  let e (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      (MorphismProperty.Over.mkIdTerminal @Etale X)).homAddEquiv _ F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  have he {F F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
      (a : F ⟶ F') (b : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶ F) : e F' (b ≫ a) = E.map a (e F b) := by
    dsimp only [e, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
    rw [Adjunction.homEquiv_naturality_right]
    rfl
  let a := (e (I.cocomplex.X n)).symm (K.iCycles n z)
  have ha : a ≫ I.cocomplex.d n (n + 1) = 0 := by
    apply (e (I.cocomplex.X (n + 1))).injective
    rw [he, AddEquiv.apply_symm_apply, map_zero]
    change (K.iCycles n ≫ K.d n (n + 1)) z = 0
    rw [K.iCycles_d]
    rfl
  have hz : K.iCycles n z = e _ a := by exact ((e _).apply_symm_apply _).symm
  have hz' : L.iCycles n (HomologicalComplex.cyclesMap f n z) =
      e _ (a ≫ φ.hom.f n) := by
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
      ConcreteCategory.comp_apply, hz, he]
    rfl
  have hn : HomologicalComplex.homologyMap f n (K.homologyπ n z) =
      L.homologyπ n (HomologicalComplex.cyclesMap f n z) := by
    change (K.homologyπ n ≫ HomologicalComplex.homologyMap f n) z =
      (HomologicalComplex.cyclesMap f n ≫ L.homologyπ n) z
    rw [HomologicalComplex.homologyπ_naturality]
  rw [hn, cJ.global_cocycle n (a ≫ φ.hom.f n)
    (by simp [reassoc_of% ha]) _ hz', cI.global_cocycle n a ha z hz]
  simpa using (I.extMk_comp_mk₀ a (n + 1) rfl ha φ).symm

private noncomputable def totalTransfer {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) {I J : InjectiveResolution X.etaleAdditiveSheaf}
    (φ : I.cocomplex ⟶ J.cocomplex) : additiveCechTotal U I ⟶ additiveCechTotal U J :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor _ _ _).map
      (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj
          (additiveCechOpenInclusion X).op ⋙ cechComplexFunctor U).mapHomologicalComplex
            (.up ℕ)).map φ)) (.up ℕ)

private lemma transfer_alpha {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) {I J : InjectiveResolution X.etaleAdditiveSheaf}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) :
    additiveCechAlpha U I n ≫ (totalTransfer U φ).f n =
      (φ.f n).hom.app (op (Scheme.Etale.mk (𝟙 X))) ≫ additiveCechAlpha U J n := by
  unfold additiveCechAlpha totalTransfer
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map]
  rw [← Category.assoc]
  dsimp only [Scheme.etaleOpenCechResolutionDoubleComplex]
  rw [← Category.assoc]
  congr 1
  apply Pi.hom_ext
  intro y
  change (Pi.lift (fun y : Fin 1 → ι ↦ (I.cocomplex.X n).obj.map
      (MorphismProperty.Over.homMk (∏ᶜ fun l ↦ U (y l)).ι
        (Category.comp_id _) : (additiveCechOpenInclusion X).obj
          (∏ᶜ fun l ↦ U (y l)) ⟶ Scheme.Etale.mk (𝟙 X)).op)) ≫
    (CategoryTheory.Limits.Pi.map (fun y : Fin 1 → ι ↦ (φ.f n).hom.app
      (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l)))))) ≫
      Pi.π _ y = _
  rw [Pi.map_π, ← Category.assoc, Pi.lift_comp_π, Category.assoc]
  erw [Pi.lift_comp_π]
  exact (φ.f n).hom.naturality _

private lemma transfer_beta {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) {I J : InjectiveResolution X.etaleAdditiveSheaf}
    (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = J.ι.f 0) (n : ℕ)
    (x : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).X n) :
    (totalTransfer U φ).f n (additiveCechBeta U I n x) = additiveCechBeta U J n x := by
  unfold additiveCechBeta
  rw [← ConcreteCategory.comp_apply]
  unfold totalTransfer
  rw [HomologicalComplex₂.ιTotal_map]
  rw [ConcreteCategory.comp_apply]
  dsimp only [Scheme.etaleOpenCechResolutionDoubleComplex]
  congr 1
  apply Limits.Concrete.limit_ext
  intro y
  change (Pi.π (C := AddCommGrpCat.{u + 1}) _ y.as)
    ((Limits.Pi.map (fun y : Fin (n + 1) → ι ↦ (φ.f 0).hom.app
      (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l)))))) _) =
    (Pi.π (fun y : Fin (n + 1) → ι ↦ (J.cocomplex.X 0).obj.obj
      (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l))))) y.as) _
  rw [← ConcreteCategory.comp_apply]
  erw [Pi.map_π]
  rw [ConcreteCategory.comp_apply]
  erw [← ConcreteCategory.comp_apply (Pi.lift _) (Pi.π _ _), Pi.lift_comp_π]
  erw [← ConcreteCategory.comp_apply (Pi.lift _) (Pi.π _ _), Pi.lift_comp_π]
  have h := congrArg (fun f ↦ f.hom.app
    (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y.as l))))) hφ
  exact ConcreteCategory.congr_hom h _

/-- Augmentation-preserving transfer between two resolutions commutes with both
Čech augmentations and with every supplied canonical global Ext comparison.
Source: Stacks Project, Tag 01FD, identity-morphism case of Lemma 20.15.1.
(blueprint: lem-pbc-etale-additive-cech-resolution-transfer)

Proof: Lift the identity on the additive sheaf to a map I -> J of injective
resolutions. Evaluation gives the global chain map. Apply the Čech functor
termwise, flip the indices, and totalize to obtain the total chain map. Naturality
of the lifted sheaf morphism gives the alpha square on each tuple; the equation
I.ι followed by the lift = J.ι gives the beta square on each tuple. The canonical
comparison sends a global cocycle to extMk. Postcomposition with the identity
lift preserves this Ext class, so surjectivity of the homology quotient gives
the last equation for every class. No affine or covering assumption is needed:
this is functoriality of the complexes, also for empty covers and degree zero. -/
theorem exists_additiveCech_resolution_transfer
    {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (I J : InjectiveResolution X.etaleAdditiveSheaf)
    (cI : Etale.ResolutionSectionCanonicalComparison X.etaleAdditiveSheaf I)
    (cJ : Etale.ResolutionSectionCanonicalComparison X.etaleAdditiveSheaf J)
    (n : ℕ) :
    ∃ f : additiveCechGlobal I ⟶ additiveCechGlobal J,
    ∃ t : additiveCechTotal U I ⟶ additiveCechTotal U J,
      (additiveCechAlpha U I n ≫ t.f n = f.f n ≫ additiveCechAlpha U J n) ∧
      (∀ x, t.f n (additiveCechBeta U I n x) = additiveCechBeta U J n x) ∧
      (∀ x, cJ.globalEquiv n (HomologicalComplex.homologyMap f n x) =
        cI.globalEquiv n x) := by
  classical
  let φ := InjectiveResolution.desc (𝟙 X.etaleAdditiveSheaf) J I
  have hφ : I.ι.f 0 ≫ φ.f 0 = J.ι.f 0 := by
    simp [φ, InjectiveResolution.desc_commutes_zero]
  let f : additiveCechGlobal I ⟶ additiveCechGlobal J :=
    ((Etale.etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex
      (.up ℕ)).map φ
  refine ⟨f, totalTransfer U φ, transfer_alpha U φ n, transfer_beta U φ hφ n, ?_⟩
  intro x
  let ψ : InjectiveResolution.Hom I J (𝟙 X.etaleAdditiveSheaf) :=
    ⟨φ, by simpa using hφ⟩
  exact canonical_transfer_identity X.etaleAdditiveSheaf I J ψ cI cJ n x

end AlgebraicGeometry.Scheme.Modules
