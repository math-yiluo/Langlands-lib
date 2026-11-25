/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Normalized scalar-extension adjunction with independent site universes

Source: Stacks Project, Modules on Sites, Tags 03CZ, 03DA and 03DB.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe uC vC u v w uD vD uT vT uB vB r a b
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Opposite
open scoped ChangeOfRings
namespace SheafOfModules.ScalarTelescopeOrdinaryProof

-- Reuse the sectionwise proof of ScalarReductionProof, at independent site universes.
section SameSiteAdjunction

variable {D : Type a} [Category.{b} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify K AddCommGrpCat.{r}]

private abbrev ringSheaf (A : Sheaf K CommRingCat.{r}) :=
  (sheafCompose K (forget₂ CommRingCat.{r} RingCat.{r})).obj A

private noncomputable abbrev restriction
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :=
  restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map c)

section

private local instance scalarLocalizationRestrictedModule
    {A : Sheaf K CommRingCat.{r}} (M : SheafOfModules.{r} (ringSheaf A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) :
    Module (A.obj.obj Y)
      ((ModuleCat.restrictScalars ((ringSheaf A).obj.map i).hom).obj (M.val.obj Y)) :=
  inferInstanceAs (Module (A.obj.obj Y) (M.val.obj Y))

private theorem tensorRestriction_tmul
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) (M : SheafOfModules.{r} (ringSheaf A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (changeOfRingsPresheafOfUniverses.{b, a, r, r} c M).map i (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom]
      m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  changeOfRingsMap_tmulOfUniverses c M i s m

end

private noncomputable def tensorPresheafFunctor
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :
    SheafOfModules.{r} (ringSheaf A) ⥤ PresheafOfModules.{r} (ringSheaf S).obj where
  obj M := changeOfRingsPresheafOfUniverses.{b, a, r, r} c M
  map {M N} f :=
    show changeOfRingsPresheafOfUniverses.{b, a, r, r} c M ⟶
      changeOfRingsPresheafOfUniverses.{b, a, r, r} c N from
    { app := fun W ↦ (ModuleCat.extendScalars (c.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturalityOfUniverses.{b, a, r, r} c _ f }
  map_id M := by
    ext W : 1
    change (ModuleCat.extendScalars (c.hom.app W).hom).map (𝟙 _) = _
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_comp _ _

private noncomputable def tensorFunctor
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) :
    SheafOfModules.{r} (ringSheaf A) ⥤ SheafOfModules.{r} (ringSheaf S) :=
  tensorPresheafFunctor c ⋙ PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)

private noncomputable def tensorToRestriction
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (ringSheaf A)) (H : SheafOfModules.{r} (ringSheaf S))
    (f : changeOfRingsPresheafOfUniverses.{b, a, r, r} c M ⟶ H.val) : M ⟶ (restriction c).obj H
      where
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
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (ringSheaf A)) (H : SheafOfModules.{r} (ringSheaf S))
    (g : M ⟶ (restriction c).obj H) : changeOfRingsPresheafOfUniverses.{b, a, r, r} c M ⟶ H.val
      where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (c.hom.app Y).hom (g.val.app Y)
        ((changeOfRingsPresheafOfUniverses.{b, a, r, r} c M).map i
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
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (ringSheaf A)) (H : SheafOfModules.{r} (ringSheaf S)) :
    (changeOfRingsPresheafOfUniverses.{b, a, r, r} c M ⟶ H.val) ≃ (M ⟶ (restriction c).obj H) where
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
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (ringSheaf A)) (H : SheafOfModules.{r} (ringSheaf S)) :
    ((tensorFunctor c).obj M ⟶ H) ≃ (M ⟶ (restriction c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

private theorem tensorHomEquiv_naturality_left
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    {M N : SheafOfModules.{r} (ringSheaf A)} (a : M ⟶ N)
    (H : SheafOfModules.{r} (ringSheaf S)) (f : (tensorFunctor c).obj N ⟶ H) :
    tensorHomEquiv c M H ((tensorFunctor c).map a ≫ f) =
      a ≫ tensorHomEquiv c N H f := by
  change tensorPresheafHomEquiv c M H
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)).map
          ((tensorPresheafFunctor c).map a) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext W m
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv
    (changeOfRingsPresheafOfUniverses.{b, a, r, r} c N) H f).app W
      ((ModuleCat.extendScalars (c.hom.app W).hom).map (a.val.app W)
        ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

private theorem tensorHomEquiv_naturality_right
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S)
    (M : SheafOfModules.{r} (ringSheaf A))
    {H H' : SheafOfModules.{r} (ringSheaf S)}
    (f : (tensorFunctor c).obj M ⟶ H) (b : H ⟶ H') :
    tensorHomEquiv c M H' (f ≫ b) =
      tensorHomEquiv c M H f ≫ (restriction c).map b := by
  change tensorPresheafHomEquiv c M H'
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        (f ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def tensorAdjunction
    {A S : Sheaf K CommRingCat.{r}} (c : A ⟶ S) : tensorFunctor c ⊣ restriction c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv c
      homEquiv_naturality_left_symm := by
        intro M N H a g
        apply (tensorHomEquiv c M H).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ tensorHomEquiv_naturality_right c _ f b }

end SameSiteAdjunction

attribute [local irreducible] tensorAdjunction

end SheafOfModules.ScalarTelescopeOrdinaryProof

namespace SheafOfModules
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {O O' : Sheaf J CommRingCat.{r}}

omit [EssentiallySmall.{r} C] in
/-- Restriction of scalars is exact, and sheafified sectionwise tensor is its left adjoint,
with Hom map given by evaluation at the image of `1 ⊗ x`.
Source: Stacks Project, Modules on Sites, Tags 03CZ, 03DA and 03DB.
(blueprint: lem-weil-pbc-scalar-localization-coefficient-adjunction-of-universes)
Proof: The sectionwise extension/restriction Hom equivalence commutes with restriction maps:
this follows on pure tensors from naturality of the ring morphism. Compose it with the
module sheafification Hom equivalence to obtain the displayed Hom equivalence. Its
naturality gives an adjunction for the prescribed functor E, since its maps are exactly
the sheafified maps id tensor f. Restriction preserves kernels sectionwise. Cokernels
are sheafifications of sectionwise cokernels, whose underlying additive presheaves do
not change under restriction of scalars. The naturality of sheafification identifies
these cokernels after restriction. Additivity and preservation of kernels and cokernels
imply preservation of finite limits and finite colimits. -/
theorem scalarLocalizationCoefficientAdjunctionOfUniverses (φ : O ⟶ O') :
    ∃ (_ : PreservesFiniteLimits (restrictScalars.{r}
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)))
      (_ : PreservesFiniteColimits (restrictScalars.{r}
                    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ))),
    ∀ (E : SheafOfModules.{r} (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ⥤
        SheafOfModules.{r} (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O')))
      (h : ∀ M, E.obj M = changeOfRingsOfUniverses φ M),
      (∀ {M N} (f : M ⟶ N), E.map f =
        eqToHom (h M) ≫ changeOfRingsHomOfUniverses φ M f ≫ eqToHom (h N).symm) →
      ∀ [E.Additive], ∃ a : E ⊣ restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ),
        (∀ (M : SheafOfModules.{r} (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)))
          (N : SheafOfModules.{r} (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O')))
          (f : changeOfRingsOfUniverses φ M ⟶ N) (U : Cᵒᵖ) (x : M.val.obj U),
          (a.homEquiv M N (eqToHom (h M) ≫ f)).val.app U x =
            f.val.app U
              ((CategoryTheory.toSheafify J (changeOfRingsPresheafOfUniverses φ M).presheaf).app U
                ((1 : O'.obj.obj U) ⊗ₜ[O.obj.obj U, (φ.hom.app U).hom] x))) := by
  classical
  let R := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let S := ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O')
  let F : SheafOfModules.{r} S ⥤ SheafOfModules.{r} R := restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)
  have : PreservesFiniteLimits (F ⋙ toSheaf R) :=
    inferInstanceAs (PreservesFiniteLimits (toSheaf.{r} S))
  have : PreservesFiniteColimits (F ⋙ toSheaf R) :=
    inferInstanceAs (PreservesFiniteColimits (toSheaf.{r} S))
  refine ⟨preservesFiniteLimits_of_reflects_of_preserves F (toSheaf R),
    preservesFiniteColimits_of_reflects_of_preserves F (toSheaf R), ?_⟩
  intro E h hm hadd
  let e : E ≅ ScalarTelescopeOrdinaryProof.tensorFunctor φ :=
    NatIso.ofComponents (fun M ↦ eqToIso (h M)) (by
      intro M N f
      change E.map f ≫ eqToHom (h N) = eqToHom (h M) ≫ changeOfRingsHomOfUniverses φ M f
      rw [hm]
      simp)
  let a := (ScalarTelescopeOrdinaryProof.tensorAdjunction φ).ofNatIsoLeft e.symm
  refine ⟨a, ?_⟩
  intro M N f U x
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  have he : e.symm.hom.app M ≫ (eqToHom (h M) ≫ f) = f := by
    change eqToHom (h M).symm ≫ (eqToHom (h M) ≫ f) = f
    simp
  rw [he]
  unfold ScalarTelescopeOrdinaryProof.tensorAdjunction
  rfl

end SheafOfModules
