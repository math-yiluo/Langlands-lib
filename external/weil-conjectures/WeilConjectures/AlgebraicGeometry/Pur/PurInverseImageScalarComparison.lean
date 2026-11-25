/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHomDefinitions
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import all WeilConjectures.CategoryTheory.ModuleInverseImageAction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
/-! The normalized scalar-extension comparison. -/
-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s h
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme.PurScalar
open SheafOfModules
private abbrev ringSheaf {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

private noncomputable abbrev restriction
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) :=
  SheafOfModules.restrictScalars.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).map c)

private noncomputable local instance
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A : Sheaf K CommRingCat.{u}} (M : SheafOfModules.{u} (ringSheaf A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) :
    Module (A.obj.obj Y)
      ((ModuleCat.restrictScalars ((ringSheaf A).obj.map i).hom).obj (M.val.obj Y)) :=
  inferInstanceAs (Module (A.obj.obj Y) (M.val.obj Y))

private theorem tensorRestriction_tmul
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) (M : SheafOfModules.{u} (ringSheaf A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (changeOfRingsPresheafOfUniverses.{h, s, u, u} c M).map i
        (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  changeOfRingsMap_tmulOfUniverses.{h, s, u, u} c M i s m

private noncomputable def tensorPresheafFunctor
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) :
    SheafOfModules.{u} (ringSheaf A) ⥤ PresheafOfModules.{u} (ringSheaf S).obj where
  obj M := changeOfRingsPresheafOfUniverses.{h, s, u, u} c M
  map {M N} f :=
    show changeOfRingsPresheafOfUniverses.{h, s, u, u} c M ⟶
      changeOfRingsPresheafOfUniverses.{h, s, u, u} c N from
    { app := fun W ↦ (ModuleCat.extendScalars (c.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturalityOfUniverses.{h, s, u, u} c _ f }
  map_id M := by
    ext W : 1
    change (ModuleCat.extendScalars (c.hom.app W).hom).map (𝟙 _) = _
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_comp _ _

private noncomputable def tensorFunctor
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) :
    SheafOfModules.{u} (ringSheaf A) ⥤ SheafOfModules.{u} (ringSheaf S) :=
  tensorPresheafFunctor c ⋙ PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)

private noncomputable def tensorToRestriction
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S))
    (f : changeOfRingsPresheafOfUniverses.{h, s, u, u} c M ⟶ H.val) :
    M ⟶ (restriction c).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul, map_one] at h
        exact h }

private noncomputable def restrictionToTensor
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S))
    (g : M ⟶ (restriction c).obj H) :
    changeOfRingsPresheafOfUniverses.{h, s, u, u} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (c.hom.app Y).hom (g.val.app Y)
        ((changeOfRingsPresheafOfUniverses.{h, s, u, u} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul, map_one]
    have atOne (W : Dᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S)) :
    (changeOfRingsPresheafOfUniverses.{h, s, u, u} c M ⟶ H.val) ≃ (M ⟶ (restriction c).obj H) where
  toFun := tensorToRestriction c M H
  invFun := restrictionToTensor c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
      (g.val.app W)

private noncomputable def tensorHomEquiv
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S)) :
    ((tensorFunctor c).obj M ⟶ H) ≃ (M ⟶ (restriction c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

private theorem tensorHomEquiv_naturality_left
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    {M N : SheafOfModules.{u} (ringSheaf A)} (a : M ⟶ N)
    (H : SheafOfModules.{u} (ringSheaf S)) (f : (tensorFunctor c).obj N ⟶ H) :
    tensorHomEquiv c M H ((tensorFunctor c).map a ≫ f) =
      a ≫ tensorHomEquiv c N H f := by
  change tensorPresheafHomEquiv c M H
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)).map
          ((tensorPresheafFunctor c).map a) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext W m
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv
    (changeOfRingsPresheafOfUniverses.{h, s, u, u} c N) H f).app W
      ((ModuleCat.extendScalars (c.hom.app W).hom).map (a.val.app W)
        ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

private theorem tensorHomEquiv_naturality_right
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A))
    {H H' : SheafOfModules.{u} (ringSheaf S)}
    (f : (tensorFunctor c).obj M ⟶ H) (b : H ⟶ H') :
    tensorHomEquiv c M H' (f ≫ b) =
      tensorHomEquiv c M H f ≫ (restriction c).map b := by
  change tensorPresheafHomEquiv c M H'
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        (f ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

@[irreducible] private noncomputable def tensorAdjunction
    {D : Type s} [Category.{h} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) : tensorFunctor c ⊣ restriction c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv c
      homEquiv_naturality_left_symm := by
        intro M N H a g
        apply (tensorHomEquiv c M H).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ tensorHomEquiv_naturality_right c _ f b }

attribute [local irreducible] proEtaleModuleInverseImage
  Functor.sheafPullbackConstruction.sheafPullback
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (O O' : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) (α : O ⟶ O')
private noncomputable abbrev imageMap :=
  (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map α
private noncomputable abbrev push (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  T g R

private noncomputable def restrictionSquare :
    restriction.{u + 1, u + 1, u} (K := ProEt.topology X)
        (imageMap g O O' α) ⋙ push g O ≅
      push g O' ⋙ restriction.{u + 1, u + 1, u} (K := ProEt.topology Y) α := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · refine (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦ ?_) ?_)
    · let P := ((restriction.{u + 1, u + 1, u} (K := ProEt.topology X)
          (imageMap g O O' α) ⋙ push g O).obj M).val.obj V
      let Q := ((push g O' ⋙ restriction.{u + 1, u + 1, u}
          (K := ProEt.topology Y) α).obj M).val.obj V
      refine
        { hom := ModuleCat.ofHom (X := P) (Y := Q)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := ?_ }
          inv := ModuleCat.ofHom (X := Q) (Y := P)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := ?_ }
          hom_inv_id := by ext; rfl
          inv_hom_id := by ext; rfl }
      · intro r m
        let m' : M.val.obj ((proEtaleBaseChange g).op.obj V) := m
        change (imageMap g O O' α).hom.app ((proEtaleBaseChange g).op.obj V)
            (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app O).hom.app V r) • m' =
          ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app O').hom.app V
            (α.hom.app V r) • m'
        congr 1
        exact (congrArg (fun k ↦ k.hom.app V (show O.obj.obj V from r))
          ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.naturality α)).symm
      · intro r m
        let m' : M.val.obj ((proEtaleBaseChange g).op.obj V) := m
        change ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app O').hom.app V
            (α.hom.app V r) • m' =
          (imageMap g O O' α).hom.app ((proEtaleBaseChange g).op.obj V)
            (((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app O).hom.app V r) • m'
        congr 1
        exact congrArg (fun k ↦ k.hom.app V (show O.obj.obj V from r))
          ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.naturality α)
    · intro V W i
      ext m
      rfl
  · intro M N f
    ext V m
    rfl

private noncomputable def scalarIso :
    tensorFunctor.{u + 1, u + 1, u} (K := ProEt.topology Y) α ⋙
        proEtaleModuleInverseImage g O' ≅
      proEtaleModuleInverseImage g O ⋙
        tensorFunctor.{u + 1, u + 1, u} (K := ProEt.topology X) (imageMap g O O' α) :=
  ((tensorAdjunction.{u + 1, u + 1, u} (K := ProEt.topology Y) α).comp
    (canonicalAdjunction g O')).leftAdjointUniq
    (((canonicalAdjunction g O).comp
      (tensorAdjunction.{u + 1, u + 1, u} (K := ProEt.topology X)
        (imageMap g O O' α))).ofNatIsoRight
      (restrictionSquare g O O' α))

private theorem tensorUnit_section {Z : Scheme.{u}}
    {R S : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}} (c : R ⟶ S)
    (M : SheafOfModules.{u + 1} (ringSheaf.{u + 1, u + 1, u} R)) (V : Z.ProEt)
    (m : M.val.obj (op V)) :
    ((tensorAdjunction.{u + 1, u + 1, u} (K := ProEt.topology Z) c).unit.app M).val.app
        (op V) m = purScalarSection R S c M V 1 m := by
  unfold tensorAdjunction
  rfl

attribute [local irreducible] SheafOfModules.changeOfRingsOfUniverses

private theorem inverseSection_smul
    (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O')) (V : Y.ProEt)
    (b : O'.obj.obj (op V)) (m : M.val.obj (op V)) :
    @Eq (ModuleCat.carrier (((proEtaleModuleInverseImage g O').obj M).val.obj
      (op ((proEtaleBaseChange g).obj V))))
      (purInverseImageSection g O' M V
        (@SMul.smul (O'.obj.obj (op V)) (M.val.obj (op V)) inferInstance b m))
      (@SMul.smul
        (((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj O').obj.obj
          (op ((proEtaleBaseChange g).obj V)))
        (((proEtaleModuleInverseImage g O').obj M).val.obj
          (op ((proEtaleBaseChange g).obj V))) inferInstance
        ((((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app O').hom.app
          (op V)) b) (purInverseImageSection g O' M V m)) := by
  have h := (((canonicalAdjunction g O').unit.app M).val.app (op V)).hom.map_smul b m
  rw [canonicalUnit_sections, canonicalUnit_sections] at h
  exact h

attribute [local semireducible] SheafOfModules.changeOfRingsOfUniverses
  proEtaleModuleInverseImage

end AlgebraicGeometry.Scheme.PurScalar
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
