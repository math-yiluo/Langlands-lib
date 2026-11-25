/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicImmersionCompletedModel
import all WeilConjectures.AlgebraicGeometry.AdicStratumCompletionUnit
import all WeilConjectures.AlgebraicGeometry.CompletedPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleOperations
import all WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
import WeilConjectures.CategoryTheory.NativeRingedRestrictionSlices
import all WeilConjectures.CategoryTheory.SiteAlgebraicCompositionUnit
import all WeilConjectures.CategoryTheory.Sites.GeometricInverseImageExact

/-! # Module-level normalization of immersion and slice restriction

Source: Stacks Tags 00YY, 03D2, 03DJ and 099L.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w c d h vc vd vh

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- Keep coefficient limits folded when comparing module functors.
attribute [local irreducible] CategoryTheory.Limits.limit ConstantCompletion.completed

namespace SfbImmersionNormalization

private abbrev Modules {C : Type c} [Category.{vc} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w}) :=
  SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)

private abbrev restrict {C : Type c} [Category.{vc} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{w}} (q : R ⟶ S) :
    Modules S ⥤ Modules R :=
  SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map q)

section Scalar

variable {C : Type c} [Category.{vc} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{w}}

private def scalarDoubleIso (q : R ≅ S) :
    𝟭 (Modules S) ≅ restrict q.hom ⋙ restrict q.inv := by
  let D := restrict q.hom ⋙ restrict q.inv
  have hq (V : Cᵒᵖ) (r : S.obj.obj V) :
      q.hom.hom.app V (q.inv.hom.app V r) = r :=
    congrArg (fun f : S ⟶ S ↦ f.hom.app V r) q.inv_hom_id
  let a : 𝟭 (Modules S) ⟶ D :=
    { app M :=
        { val :=
            { app V := ModuleCat.ofHom
                (X := M.val.obj V) (Y := (D.obj M).val.obj V)
                { toFun := id
                  map_add' := by intros; rfl
                  map_smul' := by
                    intro r x
                    change r • x = q.hom.hom.app V (q.inv.hom.app V r) • x
                    simp only [hq] }
              naturality := by intros; ext x; rfl } }
      naturality := by intros; ext V x; rfl }
  let b : D ⟶ 𝟭 (Modules S) :=
    { app M :=
        { val :=
            { app V := ModuleCat.ofHom
                (X := (D.obj M).val.obj V) (Y := M.val.obj V)
                { toFun := id
                  map_add' := by intros; rfl
                  map_smul' := by
                    intro r x
                    change @id (M.val.obj V)
                      (q.hom.hom.app V (q.inv.hom.app V r) • @id (M.val.obj V) x) =
                        r • @id (M.val.obj V) x
                    simp only [hq, id_eq] }
              naturality := by intros; ext x; rfl } }
      naturality := by intros; ext V x; rfl }
  exact ⟨a, b, by ext M V x; rfl, by ext M V x; rfl⟩

private def scalarEquivalence (q : R ≅ S) : Modules S ≌ Modules R where
  functor := restrict q.hom
  inverse := restrict q.inv
  unitIso := scalarDoubleIso q
  counitIso := (scalarDoubleIso q.symm).symm
  functor_unitIso_comp := by intros; ext V x; rfl

private def scalarPresentation (q : R ≅ S) :
    SheafOfModules.AlgebraicInverseImage (𝟭 (Sheaf J (Type w))) R S where
  ringUnderlying := (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).mapIso q
  ringAdd := by
    intro T a b t ht V x
    exact (congrArg (q.hom.hom.app V) (ht V x)).trans (map_add _ _ _)
  ringMul := by
    intro T a b t ht V x
    exact (congrArg (q.hom.hom.app V) (ht V x)).trans (map_mul _ _ _)
  ringZero := by
    intro T a ht V x
    exact (congrArg (q.hom.hom.app V) (ht V x)).trans (map_zero _)
  ringOne := by
    intro T a ht V x
    exact (congrArg (q.hom.hom.app V) (ht V x)).trans (map_one _)
  modules := restrict q.inv
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ ht V x ↦ ht V x
  moduleZero := fun _ _ _ ht V x ↦ ht V x
  moduleSMul := by
    intro M T a b t ht V x
    change @id (M.val.obj V) (t.hom.app V x) =
      (q.inv.hom.app V (q.hom.hom.app V (a.hom.app V x))) •
        @id (M.val.obj V) (b.hom.app V x)
    have hq := congrArg (fun f : R ⟶ R ↦ f.hom.app V (a.hom.app V x)) q.hom_inv_id
    change q.inv.hom.app V (q.hom.hom.app V (a.hom.app V x)) = a.hom.app V x at hq
    rw [hq]
    exact ht V x

end Scalar

section SmallScalar

variable {C : Type w} [SmallCategory C]
  {J : GrothendieckTopology C} {R S : Sheaf J CommRingCat.{w}}

private def changeIso (q : R ≅ S) :
    ConstantCompletion.change q.hom ≅ restrict q.inv := by
  let e := scalarEquivalence q
  exact (SheafOfModules.tensorAdjunction q.hom).leftAdjointUniq
    e.symm.toAdjunction

end SmallScalar

section Presentation

variable {C : Type c} {D : Type d} {H : Type h}
  [Category.{vc} C] [Category.{vd} D] [Category.{vh} H]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D] [EssentiallySmall.{w} H]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {T : GrothendieckTopology H}

private def restrictionPresentation (G : D ⥤ C) [G.IsContinuous K J]
    (R : Sheaf J CommRingCat.{w}) :
    SheafOfModules.AlgebraicInverseImage
      (G.sheafPushforwardContinuous (Type w) K J) R
      ((G.sheafPushforwardContinuous CommRingCat.{w} K J).obj R) where
  ringUnderlying := Iso.refl _
  ringAdd := fun _ _ _ _ h V x ↦ h (G.op.obj V) x
  ringMul := fun _ _ _ _ h V x ↦ h (G.op.obj V) x
  ringZero := fun _ _ h V x ↦ h (G.op.obj V) x
  ringOne := fun _ _ h V x ↦ h (G.op.obj V) x
  modules := SheafOfModules.pushforward (F := G) (𝟙 _)
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ h V x ↦ h (G.op.obj V) x
  moduleZero := fun _ _ _ h V x ↦ h (G.op.obj V) x
  moduleSMul := fun _ _ _ _ _ h V x ↦ h (G.op.obj V) x

private def compositePresentation
    {L : Sheaf J (Type w) ⥤ Sheaf K (Type w)}
    {N : Sheaf K (Type w) ⥤ Sheaf T (Type w)}
    {R : Sheaf J CommRingCat.{w}} {RI : Sheaf K CommRingCat.{w}}
    {RII : Sheaf T CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImage L R RI)
    (G : SheafOfModules.AlgebraicInverseImage N RI RII) :
    SheafOfModules.AlgebraicInverseImage (L ⋙ N) R RII where
  ringUnderlying := N.mapIso F.ringUnderlying ≪≫ G.ringUnderlying
  ringAdd := by
    intro S a b t h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.ringAdd (L.obj S) (L.map a ≫ F.ringUnderlying.hom)
      (L.map b ≫ F.ringUnderlying.hom) (L.map t ≫ F.ringUnderlying.hom)
      (F.ringAdd S a b t h) V x
  ringMul := by
    intro S a b t h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.ringMul (L.obj S) (L.map a ≫ F.ringUnderlying.hom)
      (L.map b ≫ F.ringUnderlying.hom) (L.map t ≫ F.ringUnderlying.hom)
      (F.ringMul S a b t h) V x
  ringZero := by
    intro S a h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.ringZero (L.obj S) (L.map a ≫ F.ringUnderlying.hom)
      (F.ringZero S a h) V x
  ringOne := by
    intro S a h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.ringOne (L.obj S) (L.map a ≫ F.ringUnderlying.hom)
      (F.ringOne S a h) V x
  modules := F.modules ⋙ G.modules
  moduleUnderlying := Functor.isoWhiskerLeft F.modules G.moduleUnderlying ≪≫
    Functor.isoWhiskerRight F.moduleUnderlying N
  moduleAdd := by
    intro M S a b t h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.moduleAdd (F.modules.obj M) (L.obj S)
      (L.map a ≫ F.moduleUnderlying.inv.app M)
      (L.map b ≫ F.moduleUnderlying.inv.app M)
      (L.map t ≫ F.moduleUnderlying.inv.app M) (F.moduleAdd M S a b t h) V x
  moduleZero := by
    intro M S a h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.moduleZero (F.modules.obj M) (L.obj S)
      (L.map a ≫ F.moduleUnderlying.inv.app M) (F.moduleZero M S a h) V x
  moduleSMul := by
    intro M S a b t h V x
    simpa only [Functor.map_comp, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      types_comp_apply, Functor.comp_obj, id_eq] using
      G.moduleSMul (F.modules.obj M) (L.obj S)
      (L.map a ≫ F.ringUnderlying.hom)
      (L.map b ≫ F.moduleUnderlying.inv.app M)
      (L.map t ≫ F.moduleUnderlying.inv.app M) (F.moduleSMul M S a b t h) V x

private theorem presentationComparison
    {L N : Sheaf J (Type w) ⥤ Sheaf K (Type w)} [PreservesFiniteLimits L]
    (γ : L ≅ N) {R : Sheaf J CommRingCat.{w}} {R₀ R₁ : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImage L R R₀)
    (G : SheafOfModules.AlgebraicInverseImage N R R₁) :
    ∃ q : R₀ ≅ R₁, Nonempty (F.modules ≅ G.modules ⋙ restrict q.hom) := by
  let F' := CategoryTheory.GeometricMorphism.inverseImageUniverses.{w, c, vc, d, vd} F
  let G' := CategoryTheory.GeometricMorphism.inverseImageUniverses.{w, c, vc, d, vd} G
  obtain ⟨q, _, e, _, hs⟩ := CategoryTheory.algebraicComparison γ R R₀ R₁ F' G'
  let τ : F.modules ⟶ G.modules ⋙ restrict q.hom :=
    { app M :=
        { val :=
            { app V := ModuleCat.ofHom
                (X := (F.modules.obj M).val.obj V)
                (Y := ((restrict q.hom).obj (G.modules.obj M)).val.obj V)
                { toFun := (e.hom.app M).hom.app V
                  map_add' := ((e.hom.app M).hom.app V).hom.map_add
                  map_smul' := hs M V }
              naturality := by
                intro V W f
                ext x
                exact congrArg (fun k ↦ k x) ((e.hom.app M).hom.naturality f) } }
      naturality := by
        intro M N f
        ext V x
        exact congrArg (fun k ↦ k.hom.app V x) (e.hom.naturality f) }
  have (M : Modules R) : IsIso (τ.app M) := by
    have : IsIso ((SheafOfModules.toSheaf _).map (τ.app M)) := by
      change IsIso (e.hom.app M)
      infer_instance
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact ⟨q, ⟨asIso τ⟩⟩

end Presentation

private def restrictionEquivalence
    {C D : Type (u + 1)} [Category.{u + 1} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (e : C ≌ D) [e.inverse.IsDenseSubsite K J]
    (R : Sheaf J CommRingCat.{u + 1}) :
    Modules R ≌ Modules
      ((e.inverse.sheafPushforwardContinuous CommRingCat.{u + 1} K J).obj R) := by
  let e₀ := NativeRestriction.standardModulesEquivalence.{u + 1, u + 1, u + 1, u, 0}
    (K := K) e R
  exact { e₀ with functor := SheafOfModules.pushforward (F := e.inverse) (𝟙 _) }

private def modelEquivalence (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    SheafOfModules.{u + 1} R ≌ SheafOfModules.{u + 1}
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
        RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj R) := by
  let e := (proEtaleModuleModelEquivalence X R).symm
  exact { e with functor := proEtaleModuleToModel R }

end SfbImmersionNormalization

/-- Transport modules to the small model and normalize their completed scalars.
Source: Stacks Tags 00YY and 099L
(auxiliary; not a blueprint node). -/
def sfbImmersionNormalizeModules (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    proEtaleRingModules X (adicLisseCompletedRing X I) ⥤
      ConstantCompletion.Mod (ConstantCompletion.completed (proEtaleModelTopology X) A I) :=
  proEtaleModuleToModel ((adicLisseForget X).obj (adicLisseCompletedRing X I)) ⋙
    ConstantCompletion.res (SfbCompletionNormalization.coefficients X I).inv

/-- The specified algebraic pullback of modules with completed coefficients.
Source: Stacks Tags 03D2 and 099L
(auxiliary; not a blueprint node). -/
def sfbImmersionCompletedPullModules {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i]
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :=
  ConstantCompletion.pull (sfbImmersionAlgebra i)
    (ConstantCompletion.completedMap (sfbImmersionAlgebra i) A I)

/-- Additivity of the specified ordinary module functor.
Source: Stacks Tags 03D2 and 099L
(auxiliary; not a blueprint node). -/
instance sfbImmersionNormalizeModules_additive (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    (sfbImmersionNormalizeModules X I).Additive := by
  let F := proEtaleModuleToModel ((adicLisseForget X).obj (adicLisseCompletedRing X I))
  have : F.Additive := ⟨by intros; ext U x; rfl⟩
  exact inferInstanceAs
    (F ⋙ ConstantCompletion.res (SfbCompletionNormalization.coefficients X I).inv).Additive

/-- Finite-limit preservation of the specified ordinary module functor.
Source: Stacks Tags 03D2 and 099L
(auxiliary; not a blueprint node). -/
instance sfbImmersionNormalizeModules_limits (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    PreservesFiniteLimits (sfbImmersionNormalizeModules X I) := by
  let R := (adicLisseForget X).obj (adicLisseCompletedRing X I)
  let F := proEtaleModuleToModel R
  have : F.IsEquivalence :=
    (SfbImmersionNormalization.modelEquivalence X R).isEquivalence_functor
  have : PreservesFiniteLimits F := by infer_instance
  have := (siteRestrictScalars_exact (SfbCompletionNormalization.coefficients X I).inv).1
  exact inferInstanceAs (PreservesFiniteLimits
    (F ⋙ ConstantCompletion.res (SfbCompletionNormalization.coefficients X I).inv))

/-- Finite-colimit preservation of the specified ordinary module functor.
Source: Stacks Tags 03D2 and 099L
(auxiliary; not a blueprint node). -/
instance sfbImmersionNormalizeModules_colimits (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    PreservesFiniteColimits (sfbImmersionNormalizeModules X I) := by
  let R := (adicLisseForget X).obj (adicLisseCompletedRing X I)
  let F := proEtaleModuleToModel R
  have : F.IsEquivalence :=
    (SfbImmersionNormalization.modelEquivalence X R).isEquivalence_functor
  have : PreservesFiniteColimits F := by infer_instance
  have := (siteRestrictScalars_exact (SfbCompletionNormalization.coefficients X I).inv).2
  exact inferInstanceAs (PreservesFiniteColimits
    (F ⋙ ConstantCompletion.res (SfbCompletionNormalization.coefficients X I).inv))

/-- Additivity of the specified ordinary module functor.
Source: Stacks Tags 03D2 and 099L
(auxiliary; not a blueprint node). -/
instance sfbImmersionCompletedPullModules_additive {X S : Scheme.{u}}
    (i : S ⟶ X) [IsImmersion i] {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    (sfbImmersionCompletedPullModules i I).Additive := by
  unfold sfbImmersionCompletedPullModules
  infer_instance

/-- Finite-limit preservation of the specified ordinary module functor.
Source: Stacks Tags 03D2 and 099L
(auxiliary; not a blueprint node). -/
instance sfbImmersionCompletedPullModules_limits {X S : Scheme.{u}}
    (i : S ⟶ X) [IsImmersion i] {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    PreservesFiniteLimits (sfbImmersionCompletedPullModules i I) := by
  have := SfbAdicRestriction.inverse_limits i
  have := SfbAdicRestriction.completedMap_isIso (sfbImmersionAlgebra i) A I
  exact ConstantCompletion.pull_finiteLimits_of_isIso (sfbImmersionAlgebra i) _

/-- Finite-colimit preservation of the specified ordinary module functor.
Source: Stacks Tags 03D2 and 099L
(auxiliary; not a blueprint node). -/
instance sfbImmersionCompletedPullModules_colimits {X S : Scheme.{u}}
    (i : S ⟶ X) [IsImmersion i] {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    PreservesFiniteColimits (sfbImmersionCompletedPullModules i I) := by
  obtain ⟨G, _, adj, _⟩ := ConstantCompletion.module_adjunction_exists
    (SfbAdicRestriction.direct i) (SfbAdicRestriction.adjunction i)
    (sfbImmersionAlgebra i) (ConstantCompletion.completedMap (sfbImmersionAlgebra i) A I)
  have := adj.leftAdjoint_preservesColimits
  exact inferInstanceAs (PreservesFiniteColimits
    (ConstantCompletion.pull (sfbImmersionAlgebra i)
      (ConstantCompletion.completedMap (sfbImmersionAlgebra i) A I)))

attribute [local instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

/-- The comparison of the two module inverse images, before passing to complexes.

Source: Stacks Tags 00YY, 03D2, 03DJ and 099L; Bhatt--Scholze Lemma 6.5.8
(auxiliary; not a blueprint node).

Proof: transport the actual slice to the AsSmall slice using Over.postEquiv.
The underlying-set identifications of the algebraic inverse image transport all
ring operations and module actions, so they identify its module inverse image
with the transported actual inverse image. Equivalently, both are left adjoint
to the same sectionwise direct image with restricted scalars. Compare their
units on generalized sections; uniqueness of left adjoints gives the natural
module comparison. The completed ring comparison is the limit of the constant
finite quotient comparisons: immersion inverse image preserves countable limits.
It is invertible and commutes with every finite projection. Restrict that ring
isomorphism to the slice and compose its scalar equivalence with the slice-site
module equivalence to obtain e. The scalar balancing maps then give the stated
natural isomorphism. All maps preserve addition, so e.functor is additive.
This is an assertion only about modules and their linear maps; no derived
category, complex, boundedness or perfection appears. Empty slices and the
zero ring use the same site equivalence and tensor unit identities. -/
theorem sfbImmersion_moduleNormalization
    {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i]
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) (U : S.ProEt) :
    let R := (adicLisseForget S).obj
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj (adicLisseCompletedRing X I))
    let B := ConstantCompletion.completed (proEtaleModelTopology S) A I
    let V := (AsSmall.up : S.ProEt ⥤ proEtaleSiteModel S).obj U
    ∃ e : ConstantCompletion.Mod (B.over V) ≌ SheafOfModules.{u + 1} (R.over U),
      e.functor.Additive ∧
      Nonempty (sfbImmersionNormalizeModules X I ⋙ sfbImmersionCompletedPullModules i I ⋙
          SheafOfModules.overFunctor (siteModuleRings B) V ⋙ e.functor ≅
        proEtaleRingModulePullback i (adicLisseCompletedRing X I)
          ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj
            (adicLisseCompletedRing X I)) (Iso.refl _) ⋙ SheafOfModules.overFunctor R U) := by
  classical
  let O := adicLisseCompletedRing X I
  let BX := ConstantCompletion.completed (proEtaleModelTopology X) A I
  let BS := ConstantCompletion.completed (proEtaleModelTopology S) A I
  let F := sfbImmersionAlgebra i
  have := SfbAdicRestriction.inverse_limits i
  have hc : IsIso (ConstantCompletion.completedMap F A I) :=
    SfbAdicRestriction.completedMap_isIso F A I
  let c := asIso (ConstantCompletion.completedMap F A I)
  let upS : S.ProEt ⥤ proEtaleSiteModel S := AsSmall.up
  let RI := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj O
  -- Replacing scalar extension by inverse scalar restriction makes the normalized
  -- composite another algebraic presentation of the actual set inverse image.
  let PX := SfbImmersionNormalization.compositePresentation
    (SfbImmersionNormalization.restrictionPresentation (K := proEtaleModelTopology X)
      (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt) O)
    (SfbImmersionNormalization.scalarPresentation (SfbCompletionNormalization.coefficients X I))
  let PS := SfbImmersionNormalization.compositePresentation
    (SfbImmersionNormalization.scalarPresentation c)
    (SfbImmersionNormalization.restrictionPresentation (K := ProEt.topology S) upS BS)
  let P := SfbImmersionNormalization.compositePresentation
    (SfbImmersionNormalization.compositePresentation PX (F.algebra BX)) PS
  let L := (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      (Type (u + 1)) (proEtaleModelTopology X) (ProEt.topology X) ⋙
    𝟭 _ ⋙ SfbAdicRestriction.inverse i ⋙ 𝟭 _ ⋙
      upS.sheafPushforwardContinuous (Type (u + 1))
        (ProEt.topology S) (proEtaleModelTopology S)
  have : PreservesFiniteLimits L := by
    dsimp only [L]
    infer_instance
  let γ : L ≅ proEtaleSheafInverseImage i (Type (u + 1)) :=
    NatIso.ofComponents (fun T ↦ Iso.refl _) (by intros; rfl)
  obtain ⟨G, hG⟩ := proEtaleAlgebraicInverseImage_exists i O
  -- The final coefficient equivalence is existential, so use the ring comparison
  -- determined by the two algebraic presentations.
  obtain ⟨q, ⟨δ⟩⟩ := SfbImmersionNormalization.presentationComparison γ P G
  let E := SfbImmersionNormalization.scalarEquivalence q
  let T := (SfbImmersionNormalization.restrictionPresentation
    (K := ProEt.topology S) upS BS).modules
  let eS := (AsSmall.equiv.{u, u + 1, u + 1} (C := S.ProEt)).symm
  have : eS.inverse.IsDenseSubsite (ProEt.topology S) (proEtaleModelTopology S) :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := S.ProEt)).functor.IsDenseSubsite
      (ProEt.topology S)
      ((AsSmall.equiv.{u, u + 1, u + 1} (C := S.ProEt)).inverse.inducedTopology
        (ProEt.topology S)))
  let eSite := SfbImmersionNormalization.restrictionEquivalence
    (K := ProEt.topology S) eS BS
  let eg := eSite.trans E.symm
  have hδ : P.modules ⋙ E.inverse ≅ proEtaleModuleInverseImage i O := by
    rw [← hG]
    exact Functor.isoWhiskerRight δ E.inverse ≪≫
      Functor.isoWhiskerLeft G.modules E.unitIso.symm
  have hchange : sfbImmersionNormalizeModules X I ⋙ sfbImmersionCompletedPullModules i I ⋙
      eg.functor ≅ P.modules ⋙ E.inverse := by
    exact Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (sfbImmersionNormalizeModules X I ⋙ (F.algebra BX).modules)
        (SfbImmersionNormalization.changeIso c)) (T ⋙ E.inverse)
  let hactual := (proEtaleRingModulePullbackAdjunction i O RI (Iso.refl _)).leftAdjointUniq
    (proEtaleModuleInverseImageAdjunction i O)
  let hglobal := hchange ≪≫ hδ ≪≫ hactual.symm
  let V := (AsSmall.up : S.ProEt ⥤ proEtaleSiteModel S).obj U
  let es := (Over.postEquiv (X := U)
    (AsSmall.equiv.{u, u + 1, u + 1} (C := S.ProEt))).symm
  have : (AsSmall.up : S.ProEt ⥤ proEtaleSiteModel S).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, u + 1} (C := S.ProEt)).isEquivalence_functor
  have : (AsSmall.up : S.ProEt ⥤ proEtaleSiteModel S).IsDenseSubsite
      (ProEt.topology S) (proEtaleModelTopology S) :=
    inferInstanceAs (eS.inverse.IsDenseSubsite (ProEt.topology S) (proEtaleModelTopology S))
  have : es.inverse.IsDenseSubsite ((ProEt.topology S).over U)
      ((proEtaleModelTopology S).over V) :=
    NativeRestriction.sliceDense (AsSmall.up : S.ProEt ⥤ proEtaleSiteModel S) U
  let eSlice := SfbImmersionNormalization.restrictionEquivalence
    (K := (ProEt.topology S).over U) es (BS.over V)
  let qs := ((ProEt.topology S).overPullback CommRingCat.{u + 1} U).mapIso q
  let e : ConstantCompletion.Mod (BS.over V) ≌
      SheafOfModules.{u + 1} (((adicLisseForget S).obj RI).over U) :=
    eSlice.trans (SfbImmersionNormalization.scalarEquivalence qs).symm
  have he : e.functor.Additive := by
    have : eSlice.functor.Additive := ⟨by intros; ext W x; rfl⟩
    have : (SfbImmersionNormalization.scalarEquivalence qs).inverse.Additive :=
      inferInstanceAs (SfbImmersionNormalization.restrict qs.inv).Additive
    exact inferInstanceAs (eSlice.functor ⋙
      (SfbImmersionNormalization.scalarEquivalence qs).inverse).Additive
  refine ⟨e, he, ⟨?_⟩⟩
  -- Write the identity maps on sections, avoiding equality of whole functor structures.
  let Ls := SheafOfModules.overFunctor (siteModuleRings BS) V ⋙ e.functor
  let Rs := eg.functor ⋙ SheafOfModules.overFunctor ((adicLisseForget S).obj RI) U
  let hs : Ls ≅ Rs := NatIso.ofComponents (fun M ↦
    { hom :=
        { val :=
            { app W := ModuleCat.ofHom
                (X := (Ls.obj M).val.obj W) (Y := (Rs.obj M).val.obj W)
                { toFun := id
                  map_add' := by intros; rfl
                  map_smul' := by intros; rfl }
              naturality := by intros; ext x; rfl } }
      inv :=
        { val :=
            { app W := ModuleCat.ofHom
                (X := (Rs.obj M).val.obj W) (Y := (Ls.obj M).val.obj W)
                { toFun := id
                  map_add' := by intros; rfl
                  map_smul' := by intros; rfl }
              naturality := by intros; ext x; rfl } }
      hom_inv_id := by ext W x; rfl
      inv_hom_id := by ext W x; rfl }) (by intros; ext W x; rfl)
  exact Functor.isoWhiskerLeft
    (sfbImmersionNormalizeModules X I ⋙ sfbImmersionCompletedPullModules i I) hs ≪≫
    Functor.isoWhiskerRight hglobal (SheafOfModules.overFunctor ((adicLisseForget S).obj RI) U)

end AlgebraicGeometry.Scheme
