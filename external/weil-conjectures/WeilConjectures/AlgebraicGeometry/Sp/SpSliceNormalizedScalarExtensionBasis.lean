/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwistLevelsSupplement

import all WeilConjectures.AlgebraicGeometry.Sp.SpSliceScalarExtensionBasis

/-! # Scalar extension of a prescribed basis, with its unit normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.InternalAbelianSheafModule
open scoped TensorProduct ChangeOfRings
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale

private def sliceSectionsMap (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R] (W : X.ProEt)
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R)
    (f : (((Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} W).mapMod R).obj M ⟶
      (((Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} W).mapMod R).obj N) :
    (spRootBasisSliceSections X R W).obj M ⟶
      (spRootBasisSliceSections X R W).obj N := by
  let J := Scheme.ProEt.topology X
  let O := J.overPullback AddCommGrpCat.{u + 1} W
  let G := sheafToPresheaf (J.over W) AddCommGrpCat.{u + 1}
  let H := sheafToPresheaf J AddCommGrpCat.{u + 1}
  refine ⟨{
    app := fun V ↦ ModuleCat.ofHom
      { toFun := fun x ↦ f.hom.hom.app V x
        map_add' := fun x y ↦ map_add (f.hom.hom.app V).hom x y
        map_smul' := ?_ }
    naturality := ?_ }⟩
  · intro r m
    have hf₀ : Functor.LaxMonoidal.μ O R M.X ≫ O.map (Mod.act M.X) ≫ f.hom =
        O.obj R ◁ f.hom ≫ Functor.LaxMonoidal.μ O R N.X ≫ O.map (Mod.act N.X) := by
      simpa only [Functor.act_mapMod_obj, Category.assoc] using Mod.act_hom f
    have hf := congrArg G.map hf₀
    simp only [Functor.map_comp] at hf
    have h := congrArg (fun k ↦ Functor.LaxMonoidal.μ G (O.obj R) (O.obj M.X) ≫ k) hf
    rw [← Functor.LaxMonoidal.μ_natural_right_assoc] at h
    have hμ (P T : Sheaf J AddCommGrpCat.{u + 1}) :
        Functor.LaxMonoidal.μ G (O.obj P) (O.obj T) ≫
            G.map (Functor.LaxMonoidal.μ O P T) =
          Functor.whiskerLeft (Over.forget W).op (Functor.LaxMonoidal.μ H P T) := by
      apply NatTrans.ext
      funext V
      exact Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
        (Over.forget W) AddCommGrpCat.{u + 1} (J.over W) J P T V
    erw [reassoc_of% hμ R M.X, reassoc_of% hμ R N.X] at h
    exact ConcreteCategory.congr_hom (congr_app h V) (r ⊗ₜ[ℤ] m)
  · intro V T g
    ext m
    exact NatTrans.naturality_apply f.hom.hom g m

private def sliceSectionsIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R] (W : X.ProEt)
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R)
    (i : (((Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} W).mapMod R).obj M ≅
      (((Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} W).mapMod R).obj N) :
    (spRootBasisSliceSections X R W).obj M ≅
      (spRootBasisSliceSections X R W).obj N where
  hom := sliceSectionsMap X R W M N i.hom
  inv := sliceSectionsMap X R W N M i.inv
  hom_inv_id := by
    ext V x
    exact congrArg (fun f ↦ f.hom.hom.app V x) i.hom_inv_id
  inv_hom_id := by
    ext V x
    exact congrArg (fun f ↦ f.hom.hom.app V x) i.inv_hom_id

private def regularSectionsIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R] (W : X.ProEt) :
    (spRootBasisSliceSections X R W).obj (Mod.regular R) ≅
      (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R))).over W := by
  let f : (spRootBasisSliceSections X R W).obj (Mod.regular R) ⟶
      (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R))).over W :=
    ⟨{ app := fun V ↦ ModuleCat.ofHom
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
       naturality := by intros; rfl }⟩
  let g : (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) R))).over W ⟶
      (spRootBasisSliceSections X R W).obj (Mod.regular R) :=
    ⟨{ app := fun V ↦ ModuleCat.ofHom
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
       naturality := by intros; rfl }⟩
  exact ⟨f, g, by ext V; rfl, by ext V; rfl⟩

private def sectionExtensionIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (p : R ⟶ S) [IsMonHom p]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R) :
    (sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) S).functor.obj ((Mod.extendScalars p).obj M) ≅
      SheafOfModules.changeOfRings.{u, u + 1, u + 1}
        (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X) p)
        ((sectionModuleEquivalence.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) R).functor.obj M) := by
  let J := Scheme.ProEt.topology X
  let q := sectionScalarMap.{u + 1, u + 1, u} J p
  let E := SheafOfModules.CoefficientOrdinaryProof.tensorFunctor.{u + 1, u + 1, u} q
  let a := SheafOfModules.CoefficientOrdinaryProof.tensorAdjunction.{u + 1, u + 1, u} q
  let α : (sectionModuleEquivalence.{u + 1, u + 1, u} J R).functor ⋙ E ⟶
      Mod.extendScalars p ⋙ (sectionModuleEquivalence.{u + 1, u + 1, u} J S).functor :=
    ((mateEquiv (Mod.extendRestrictAdjunction p) a).symm
      (TwoSquare.mk _ _ _ _ (scalarRestrictionIso.{u + 1, u + 1, u} J p).hom))
  haveI : IsIso α := inverseMate_isIso (Mod.extendRestrictAdjunction p) a
    (scalarRestrictionIso.{u + 1, u + 1, u} J p)
  exact (asIso α).symm.app M

private theorem sectionExtensionIso_unit (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (p : R ⟶ S) [IsMonHom p]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R)
    (V : X.ProEtᵒᵖ) (m : M.X.obj.obj V) :
    (sectionExtensionIso X p M).hom.val.app V ((Mod.extendUnitHom p M).hom.app V m) =
      (toSheafify (Scheme.ProEt.topology X)
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
          (sectionScalarMap.{u + 1, u + 1, u} (Scheme.ProEt.topology X) p)
          ((sectionModuleEquivalence.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X) R).functor.obj M)).presheaf).app V
        ((1 : (sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X) S).obj.obj V)
          ⊗ₜ[_, ((sectionScalarMap.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X) p).hom.app V).hom] m) := by
  let J := Scheme.ProEt.topology X
  let q := sectionScalarMap.{u + 1, u + 1, u} J p
  let a := SheafOfModules.CoefficientOrdinaryProof.tensorAdjunction.{u + 1, u + 1, u} q
  have h :
      (sectionModuleEquivalence.{u + 1, u + 1, u} J R).functor.map
          ((Mod.extendRestrictAdjunction p).unit.app M) ≫
        (scalarRestrictionIso.{u + 1, u + 1, u} J p).hom.app ((Mod.extendScalars p).obj M) =
      a.unit.app ((sectionModuleEquivalence.{u + 1, u + 1, u} J R).functor.obj M) ≫
        (SheafOfModules.scalarRestriction q).map (sectionExtensionIso X p M).inv :=
    unit_mateEquiv_symm (Mod.extendRestrictAdjunction p) a
      (TwoSquare.mk _ _ _ _ (scalarRestrictionIso.{u + 1, u + 1, u} J p).hom) M
  have h' := congrArg (fun f ↦ f ≫
    (SheafOfModules.scalarRestriction q).map (sectionExtensionIso X p M).hom) h
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id] at h'
  have hm := congrArg (fun f ↦ f.val.app V m) h'
  change (sectionExtensionIso X p M).hom.val.app V
      ((Mod.extendUnitHom p M).hom.app V m) =
    (a.unit.app ((sectionModuleEquivalence.{u + 1, u + 1, u} J R).functor.obj M)).val.app V m at hm
  rw [hm]
  rfl

attribute [irreducible] sectionExtensionIso

private def liftSliceSectionsIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    [MonObj R] [IsCommMonObj R] (W : X.ProEt)
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R)
    (e : (spRootBasisSliceSections X R W).obj M ≅
      (spRootBasisSliceSections X R W).obj N) :
    let O := (Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} W
    (O.mapMod R).obj M ≅ (O.mapMod R).obj N := by
  let J := Scheme.ProEt.topology X
  let O := J.overPullback AddCommGrpCat.{u + 1} W
  let G := sheafToPresheaf (J.over W) AddCommGrpCat.{u + 1}
  let H := sheafToPresheaf J AddCommGrpCat.{u + 1}
  let j : O.obj M.X ≅ O.obj N.X := (SheafOfModules.toSheaf _).mapIso e
  refine Mod.isoMk j ?_
  rw [Functor.act_mapMod_obj, Functor.act_mapMod_obj]
  change (Functor.LaxMonoidal.μ O R M.X ≫ O.map (Mod.act M.X)) ≫ j.hom =
    O.obj R ◁ j.hom ≫ (Functor.LaxMonoidal.μ O R N.X ≫ O.map (Mod.act N.X))
  apply Sheaf.tensor_hom_ext
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc]
  apply NatTrans.ext
  funext V
  simp only [NatTrans.comp_app]
  have hμ (P T : Sheaf J AddCommGrpCat.{u + 1}) :
      (Functor.LaxMonoidal.μ G (O.obj P) (O.obj T)).app V ≫
          (G.map (Functor.LaxMonoidal.μ O P T)).app V =
        (Functor.LaxMonoidal.μ H P T).app (op V.unop.left) :=
    Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
      (Over.forget W) AddCommGrpCat.{u + 1} (J.over W) J P T V
  rw [reassoc_of% hμ R M.X, reassoc_of% hμ R N.X]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.toIntLinearMap_injective
  apply TensorProduct.ext'
  intro r m
  exact (e.hom.val.app V).hom.map_smul r m

private theorem sectionSliceTensorBasis (X : Scheme.{u})
    {A B : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : A ⟶ B)
    (M : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) (W : X.ProEt)
    (e : M.over W ≅ (SheafOfModules.unit.{u, u + 1, u + 1} _).over W) :
    ∃ d : (SheafOfModules.changeOfRings.{u, u + 1, u + 1} a M).over W ≅
        (SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)).over W,
      ∀ (V : (Over W)ᵒᵖ) (z : (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a M).obj
          (op V.unop.left)),
        d.hom.val.app V ((toSheafify (Scheme.ProEt.topology X)
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a M).presheaf).app
            (op V.unop.left) z) =
            (localTensorBasisIso X a M W e).hom.app V z := by
  let J := Scheme.ProEt.topology X
  let Q := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a M
  let B₀ := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B
  let U := (SheafOfModules.unit B₀).over W
  let P := SheafOfModules.slicePresheafRestrictionIndependent (J := J.over W)
    (Over.forget W) B₀
  let T := PresheafOfModules.sheafification.{u + 1} (𝟙 (B₀.over W).obj)
  let b := PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 (B₀.over W).obj)
  let t := SheafOfModules.sliceSheafificationComparisonIndependent
    (J := J.over W) (Over.forget W) B₀
  have := SheafOfModules.sliceSheafificationComparisonIndependent_isIso
    (J := J.over W) (Over.forget W) B₀
  let e₀ := localTensorBasisIso X a M W e
  let k := T.mapIso e₀ ≪≫ asIso (b.counit.app U)
  refine ⟨(asIso (t.app Q)).symm ≪≫ k, ?_⟩
  intro V z
  let V₀ := SheafOfModules.sliceModuleRestrictionIndependent
    (J := J.over W) (Over.forget W) B₀
  let S₀ := PresheafOfModules.sheafification.{u + 1} (𝟙 B₀.obj)
  have ht := (b.homEquiv (P.obj Q) (V₀.obj (S₀.obj Q))).apply_symm_apply
    (show P.obj Q ⟶
      (SheafOfModules.forget (B₀.over W) ⋙
        PresheafOfModules.restrictScalars (𝟙 (B₀.over W).obj)).obj (V₀.obj (S₀.obj Q)) from
      P.map ((PresheafOfModules.sheafificationAdjunction (𝟙 B₀.obj)).unit.app Q))
  have ht' := congrArg (fun f ↦ f.app V z) ht
  change (t.app Q).val.app V
      ((toSheafify (J.over W) (P.obj Q).presheaf).app V z) =
    (toSheafify J Q.presheaf).app (op V.unop.left) z at ht'
  have hk : b.homEquiv _ _ k.hom = e₀.hom := by
    apply (b.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    rfl
  have hk' := congrArg (fun f ↦ f.app V z) hk
  change k.hom.val.app V ((toSheafify (J.over W) (P.obj Q).presheaf).app V z) =
    e₀.hom.app V z at hk'
  change k.hom.val.app V ((asIso (t.app Q)).inv.val.app V
    ((toSheafify J Q.presheaf).app (op V.unop.left) z)) = _
  rw [← ht']
  have hi := congrArg (fun f ↦ f.val.app V
    ((toSheafify (J.over W) (P.obj Q).presheaf).app V z)) (asIso (t.app Q)).hom_inv_id
  change (asIso (t.app Q)).inv.val.app V
      ((t.app Q).val.app V ((toSheafify (J.over W) (P.obj Q).presheaf).app V z)) =
    (toSheafify (J.over W) (P.obj Q).presheaf).app V z at hi
  rw [hi]
  exact hk'

/-- Extending a prescribed slice basis gives a basis normalized on the integral unit.

Source: blueprint latest, sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.proof.md, clause (3), scalar extension of the
integral basis; sec-proetale-coefficients/sk-def-sp-tate-twist/_section.md.
(blueprint: lem-sp-slice-normalized-scalar-extension-basis)

Proof: reconstruct the section rings and modules. The mate of the sectionwise
restriction-of-scalars comparison identifies internal scalar extension with
sheafification of the balanced sectionwise tensor product. Restriction to W
commutes with this sheafification, since each object of the slice has exactly
its original covers. Tensor the supplied basis and its inverse with S on the
slice. Compose with S tensor_R R = S, whose forward map sends s tensor r to
s times p(r), and whose inverse sends s to s tensor 1. Balancing proves the
inverse identities and S-linearity. Under this construction p(r) maps to the
image of i(r) under the extension unit, which is the asserted normalization.
These are equations of maps of the actual internal modules, retained by section
reconstruction. The calculation also applies to the zero ring and empty slice.
No roots, inverse systems, or coefficient-field inclusions are involved. -/
theorem spSliceNormalizedScalarExtensionBasis (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (p : R ⟶ S) [IsMonHom p]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R)
    (W : X.ProEt)
    (i : Mod.regular
        (((Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} W).obj R) ≅
      ((((Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} W).mapMod R).obj M)) :
    let O := (Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} W
    ∃ b : Mod.regular (O.obj S) ≅ (O.mapMod S).obj ((Mod.extendScalars p).obj M),
      O.map p ≫ b.hom.hom = i.hom.hom ≫ O.map (Mod.extendUnitHom p M) := by
  let J := Scheme.ProEt.topology X
  let O := J.overPullback AddCommGrpCat.{u + 1} W
  let q := sectionScalarMap.{u + 1, u + 1, u} J p
  let A := sectionRingSheaf.{u + 1, u + 1, u} J R
  let B := sectionRingSheaf.{u + 1, u + 1, u} J S
  let B₀ := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B
  let M₀ := (sectionModuleEquivalence.{u + 1, u + 1, u} J R).functor.obj M
  let e := (sliceSectionsIso X R W (Mod.regular R) M i).symm ≪≫
    regularSectionsIso X R W
  obtain ⟨d, hd⟩ := sectionSliceTensorBasis X q M₀ W e
  let j := (SheafOfModules.overFunctor B₀ W).mapIso (sectionExtensionIso X p M)
  let c := j ≪≫ d
  let f := c ≪≫ (regularSectionsIso X S W).symm
  let b := liftSliceSectionsIso X S W (Mod.regular S) ((Mod.extendScalars p).obj M) f.symm
  refine ⟨b, ?_⟩
  ext V r
  have hc (m : M.X.obj.obj (op V.unop.left)) :
      c.hom.val.app V ((Mod.extendUnitHom p M).hom.app (op V.unop.left) m) =
        (q.hom.app (op V.unop.left)).hom (e.hom.val.app V m) := by
    change d.hom.val.app V ((sectionExtensionIso X p M).hom.val.app
      (op V.unop.left) ((Mod.extendUnitHom p M).hom.app (op V.unop.left) m)) = _
    rw [sectionExtensionIso_unit, hd]
    let := (q.hom.app (op V.unop.left)).hom.toAlgebra
    change (TensorProduct.AlgebraTensorModule.rid (A.obj.obj (op V.unop.left))
      (B.obj.obj (op V.unop.left)) (B.obj.obj (op V.unop.left)))
      ((ModuleCat.extendScalars (q.hom.app (op V.unop.left)).hom).map
        (e.hom.val.app V)
        ((1 : B.obj.obj (op V.unop.left)) ⊗ₜ[_, (q.hom.app (op V.unop.left)).hom] m)) = _
    rw [ModuleCat.ExtendScalars.map_tmul]
    erw [TensorProduct.AlgebraTensorModule.rid_tmul]
    change (q.hom.app (op V.unop.left)).hom (e.hom.val.app V m) * 1 = _
    exact mul_one _
  have hi : e.hom.val.app V (i.hom.hom.hom.app V r) = r :=
    congrArg (fun g ↦ g.hom.hom.app V r) i.hom_inv_id
  have hc' := hc (i.hom.hom.hom.app V r)
  rw [hi] at hc'
  have hinj := ConcreteCategory.bijective_of_isIso
    (((SheafOfModules.evaluation _ V).mapIso c).hom)
  apply hinj.1
  change c.hom.val.app V (c.inv.val.app V ((p.hom.app (op V.unop.left)) r)) =
    c.hom.val.app V ((Mod.extendUnitHom p M).hom.app (op V.unop.left)
      (i.hom.hom.hom.app V r))
  rw [hc']
  exact congrArg (fun g ↦ g.val.app V ((p.hom.app (op V.unop.left)) r)) c.inv_hom_id

end AlgebraicGeometry.ProEtale
