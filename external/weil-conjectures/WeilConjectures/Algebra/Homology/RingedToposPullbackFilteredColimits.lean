/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
/-! # Filtered colimits of the specified ringed-topos module pullback

Source: Stacks Project, Modules on Sites, Tag 03D7,
lemma-adjoint-pullback-pushforward-modules.
(auxiliary; not a blueprint node).

The scalar-extension Hom equivalence generalizes the private construction in
ModulePullbackPushforwardAdjunction to independent site and coefficient universes.
The inverse-image argument uses only the supplied natural underlying-sheaf isomorphism. -/

@[expose] public section
universe u v w uD vD uC vC
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})

private theorem underlying_preserves_filtered
    (K : Type w) [Category.{w} K] [IsFiltered K] :
    PreservesColimitsOfShape K
      (toSheaf R ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})) := by
  let U := CategoryTheory.forget AddCommGrpCat.{w}
  let S := sheafCompose J U
  let L := presheafToSheaf J AddCommGrpCat.{w}
  let e := equivSmallModel.{w} C
  let KJ := e.inverse.inducedTopology J
  let : PreservesFilteredColimitsOfSize.{w, w} U := preservesFilteredColimitsOfSize_shrink _
  have : KJ.PreservesSheafification U := inferInstance
  have : ∀ X : Cᵒᵖ, HasLimitsOfShape (StructuredArrow X e.inverse.op)
      AddCommGrpCat.{w} := fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _
  have : ∀ X : Cᵒᵖ, HasLimitsOfShape (StructuredArrow X e.inverse.op)
      (Type w) := fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{w} _ _
  have : HasSheafify KJ (Type w) := inferInstance
  have : HasSheafify J (Type w) := hasSheafifyEssentiallySmallSite J (Type w)
  have : J.PreservesSheafification U :=
    GrothendieckTopology.PreservesSheafification.transport J KJ e.inverse (Type w) U
  have : PreservesColimitsOfShape K S := by
    constructor
    intro F
    let G := F ⋙ sheafToPresheaf J AddCommGrpCat.{w}
    let e : G ⋙ L ≅ F := isoWhiskerLeft F
      (asIso (sheafificationAdjunction J AddCommGrpCat.{w}).counit) ≪≫ F.rightUnitor
    have : PreservesColimit G (L ⋙ S) :=
      preservesColimit_of_natIso G
        (sheafComposeNatIso J U (sheafificationAdjunction J AddCommGrpCat.{w})
          (sheafificationAdjunction J (Type w)))
    have : PreservesColimit (G ⋙ L) S :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves L (colimit.isColimit G))
        (isColimitOfPreserves (L ⋙ S) (colimit.isColimit G))
    exact preservesColimit_of_iso_diagram S e
  infer_instance

private theorem inverseImage_preserves_filtered
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
    {JD : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{w}} {RI : Sheaf JD CommRingCat.{w}}
    (L : Sheaf J (Type w) ⥤ Sheaf JD (Type w))
    (V : Sheaf JD (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)
    (I : AlgebraicInverseImage L R RI)
    (K : Type w) [Category.{w} K] [IsFiltered K] :
    PreservesColimitsOfShape K I.modules := by
  let O := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R
  let OI := (sheafCompose JD (forget₂ CommRingCat.{w} RingCat.{w})).obj RI
  let F := toSheaf O ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})
  let G := toSheaf OI ⋙ sheafCompose JD (CategoryTheory.forget AddCommGrpCat.{w})
  have : PreservesColimitsOfShape K F := underlying_preserves_filtered O K
  have : PreservesColimitsOfShape K G := underlying_preserves_filtered OI K
  have : PreservesColimitsOfShape K L :=
    adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape K (I.modules ⋙ G) :=
    preservesColimitsOfShape_of_natIso I.moduleUnderlying.symm
  have : ReflectsColimitsOfShape K G :=
    ⟨fun {H} ↦ reflectsColimit_of_reflectsIsomorphisms H G⟩
  exact preservesColimitsOfShape_of_reflects_of_preserves I.modules G

open scoped ChangeOfRings
set_option backward.isDefEq.respectTransparency false

private abbrev ringSheaf {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R
private noncomputable abbrev restriction
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S) :=
  restrictScalars.{w} ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map c)

private local instance
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A : Sheaf K CommRingCat.{w}} (M : SheafOfModules.{w} (ringSheaf A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) :
    Module (A.obj.obj Y)
      ((ModuleCat.restrictScalars ((ringSheaf A).obj.map i).hom).obj (M.val.obj Y)) :=
  inferInstanceAs (Module (A.obj.obj Y) (M.val.obj Y))

private theorem tensorRestriction_tmul
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S) (M : SheafOfModules.{w} (ringSheaf A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (changeOfRingsPresheaf.{vD, uD, w} c M).map i (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  Classical.choose_spec (exists_changeOfRingsMap.{vD, uD, w} c M i) s m

private noncomputable def tensorPresheafFunctor
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S) :
    SheafOfModules.{w} (ringSheaf A) ⥤ PresheafOfModules.{w} (ringSheaf S).obj where
  obj M := changeOfRingsPresheaf.{vD, uD, w} c M
  map {M N} f :=
    show changeOfRingsPresheaf.{vD, uD, w} c M ⟶
      changeOfRingsPresheaf.{vD, uD, w} c N from
    { app := fun W ↦ (ModuleCat.extendScalars (c.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturality.{vD, uD, w} c _ f }
  map_id M := by
    ext W : 1
    change (ModuleCat.extendScalars (c.hom.app W).hom).map (𝟙 _) = _
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_comp _ _

private noncomputable def tensorFunctor
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S) :
    SheafOfModules.{w} (ringSheaf A) ⥤ SheafOfModules.{w} (ringSheaf S) :=
  tensorPresheafFunctor c ⋙ PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)

private noncomputable def tensorToRestriction
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S)
    (M : SheafOfModules.{w} (ringSheaf A)) (H : SheafOfModules.{w} (ringSheaf S))
    (f : changeOfRingsPresheaf.{vD, uD, w} c M ⟶ H.val) : M ⟶ (restriction c).obj H where
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
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S)
    (M : SheafOfModules.{w} (ringSheaf A)) (H : SheafOfModules.{w} (ringSheaf S))
    (g : M ⟶ (restriction c).obj H) : changeOfRingsPresheaf.{vD, uD, w} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (c.hom.app Y).hom (g.val.app Y)
        ((changeOfRingsPresheaf.{vD, uD, w} c M).map i
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
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S)
    (M : SheafOfModules.{w} (ringSheaf A)) (H : SheafOfModules.{w} (ringSheaf S)) :
    (changeOfRingsPresheaf.{vD, uD, w} c M ⟶ H.val) ≃ (M ⟶ (restriction c).obj H) where
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

private noncomputable def changeOfRingsTensorHomEquiv
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S)
    (M : SheafOfModules.{w} (ringSheaf A)) (H : SheafOfModules.{w} (ringSheaf S)) :
    ((tensorFunctor c).obj M ⟶ H) ≃ (M ⟶ (restriction c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

private theorem tensorHomEquiv_naturality_left
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S)
    {M N : SheafOfModules.{w} (ringSheaf A)} (a : M ⟶ N)
    (H : SheafOfModules.{w} (ringSheaf S)) (f : (tensorFunctor c).obj N ⟶ H) :
    changeOfRingsTensorHomEquiv c M H ((tensorFunctor c).map a ≫ f) =
      a ≫ changeOfRingsTensorHomEquiv c N H f := by
  change tensorPresheafHomEquiv c M H
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)).map
          ((tensorPresheafFunctor c).map a) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext W m
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv
    (changeOfRingsPresheaf.{vD, uD, w} c N) H f).app W
      ((ModuleCat.extendScalars (c.hom.app W).hom).map (a.val.app W)
        ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

private theorem tensorHomEquiv_naturality_right
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S)
    (M : SheafOfModules.{w} (ringSheaf A))
    {H H' : SheafOfModules.{w} (ringSheaf S)}
    (f : (tensorFunctor c).obj M ⟶ H) (b : H ⟶ H') :
    changeOfRingsTensorHomEquiv c M H' (f ≫ b) =
      changeOfRingsTensorHomEquiv c M H f ≫ (restriction c).map b := by
  change tensorPresheafHomEquiv c M H'
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        (f ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def tensorAdjunction
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S) : tensorFunctor c ⊣ restriction c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := changeOfRingsTensorHomEquiv c
      homEquiv_naturality_left_symm := by
        intro M N H a g
        apply (changeOfRingsTensorHomEquiv c M H).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ tensorHomEquiv_naturality_right c _ f b }

/-- Extension of scalars, specified on both objects and maps, preserves colimits.
Source: Stacks Project, Modules on Sites, Tags 03D7 and 03EP.
The tensor/restriction adjunction gives preservation for its tensor functor;
the two specifications give a natural isomorphism to E.
(auxiliary; not a blueprint node). -/
theorem preservesColimits_specifiedChangeOfRings
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
    {K : GrothendieckTopology D} {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S)
    (E : SheafOfModules.{w} ((sheafCompose K
        (forget₂ CommRingCat.{w} RingCat.{w})).obj A) ⥤
      SheafOfModules.{w} ((sheafCompose K
        (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (hobj : ∀ M, E.obj M = changeOfRings.{vD, uD, w} c M)
    (hmap : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (hobj M) ≫
      changeOfRingsHom.{vD, uD, w} c M f ≫ eqToHom (hobj N).symm) :
    PreservesColimitsOfSize.{0, 0} E := by
  have : PreservesColimitsOfSize.{0, 0} (tensorFunctor c) :=
    (tensorAdjunction c).leftAdjoint_preservesColimits
  let e : tensorFunctor c ≅ E := NatIso.ofComponents
    (fun M ↦ eqToIso (hobj M).symm) (by
      intro M N f
      change changeOfRingsHom c M f ≫ eqToHom (hobj N).symm =
        eqToHom (hobj M).symm ≫ E.map f
      rw [hmap]
      simp)
  exact preservesColimits_of_natIso e

/-- The specified algebraic module pullback preserves coefficient-sized filtered colimits.
Source: Stacks Project, Modules on Sites, Tag 03D7,
lemma-adjoint-pullback-pushforward-modules, and Tag 03EP.
(auxiliary; not a blueprint node).

Proof: forgetting module sheaves to sheaves of abelian groups preserves colimits, by
module sheafification. Forgetting abelian sheaves to sheaves of sets preserves filtered
colimits: the analogous presheaf functor does, and it commutes with sheafification.
Transport sheafification compatibility from the small model of the site in universe w.
The composite forgetful functor reflects isomorphisms and thus reflects these colimits.
The natural isomorphism I.moduleUnderlying and the adjunction uInv ⊣ uPush now show
that I.modules preserves filtered colimits.

Scalar extension is left adjoint to restriction of scalars. Sectionwise the Hom
bijection sends f to (m ↦ f (1 tensor m)), with inverse (s tensor m ↦ s times g(m)).
Naturality of module maps and the formula for tensor restrictions make these maps
presheaf morphisms. Sheafification extends this bijection to sheaves. The two naturality
identities give the adjunction, so scalar extension preserves all colimits. Finally,
hobj and hmap give a natural isomorphism between uStar and its presentation as the
composite of I.modules with scalar extension. Transfer preservation along that isomorphism. -/
theorem preservesFilteredColimits_ringedToposPullback
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{w}} {S RI : Sheaf JD CommRingCat.{w}}
    (uInv : Sheaf JC (Type (w)) ⥤ Sheaf JD (Type (w)))
    (uPush : Sheaf JD (Type (w)) ⥤ Sheaf JC (Type (w)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤
      SheafOfModules.{w} ((sheafCompose JD
        (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (hobj : ∀ M : SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R),
      uStar.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)} (a : M ⟶ N),
      uStar.map a = eqToHom (hobj M) ≫
        changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫ eqToHom (hobj N).symm)
    (K : Type w) [Category.{w} K] [IsFiltered K] :
    PreservesColimitsOfShape K uStar := by
  have : PreservesColimitsOfShape K I.modules :=
    inverseImage_preserves_filtered uInv uPush adj I K
  have : PreservesColimitsOfShape K (tensorFunctor c) :=
    (tensorAdjunction c).leftAdjoint_preservesColimits.preservesColimitsOfShape
  let T := I.modules ⋙ tensorFunctor c
  let e : T ≅ uStar := NatIso.ofComponents
    (fun M ↦ eqToIso (hobj M).symm) (by
      intro M N f
      change changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm = eqToHom (hobj M).symm ≫ uStar.map f
      rw [hmap]
      simp)
  exact preservesColimitsOfShape_of_natIso e
end SheafOfModules
