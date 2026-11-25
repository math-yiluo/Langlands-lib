/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Extending constant coefficients to the constant ring sheaf

Source: Stacks Project, Modules on Sites, Sections 093I and 03CV;
Sites Example 0H7J.
(blueprint: lem-sfb-ring-etale-constant-module-equivalence)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Functor

namespace AlgebraicGeometry.Scheme.FiniteRingCoefficientComparison

variable (Y : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]

/-- The sheafification of the constant ring presheaf.
(blueprint: lem-sfb-ring-etale-constant-module-equivalence)
-/
private abbrev etaleConstantModuleRing : Sheaf Y.smallEtaleTopology RingCat.{u + 1} :=
  (constantSheaf Y.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ)

/-- The sheafification unit of the constant ring presheaf.
(blueprint: lem-sfb-ring-etale-constant-module-equivalence)
-/
private def etaleConstantModuleRingUnit :
    (Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ) ⟶ (etaleConstantModuleRing Y Λ).obj :=
  toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ))

private instance : Presheaf.IsLocallyInjective Y.smallEtaleTopology
    (etaleConstantModuleRingUnit Y Λ) :=
  have : Presheaf.IsLocallyInjective Y.smallEtaleTopology
      (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ))) := by
    apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
    infer_instance
  this

private instance : Presheaf.IsLocallySurjective Y.smallEtaleTopology
    (etaleConstantModuleRingUnit Y Λ) :=
  have : Presheaf.IsLocallySurjective Y.smallEtaleTopology
      (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ))) := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    infer_instance
  this

/-- A module-valued presheaf, viewed as modules over the constant ring presheaf.
(blueprint: lem-sfb-ring-etale-constant-module-equivalence)
-/
private def etaleConstantModulePresheaf (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    PresheafOfModules.{u + 1} ((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ)) :=
  letI (X : Y.Etaleᵒᵖ) : Module
      (((Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ)).obj X)
      ((J.obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj X) :=
    (J.obj.obj X).isModule
  PresheafOfModules.ofPresheaf
    (R := (Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ))
    (J.obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    (fun {_ _} f r m ↦ (J.obj.map f).hom.map_smul r m)

/-- The identity of the underlying abelian presheaf, as a map to the underlying abelian sheaf.
(blueprint: lem-sfb-ring-etale-constant-module-equivalence)
-/
private def etaleConstantModuleUnderlyingHom
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (etaleConstantModulePresheaf Y Λ J).presheaf ⟶
      ((sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J).obj :=
  𝟙 _

private instance (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Presheaf.IsLocallyInjective Y.smallEtaleTopology (etaleConstantModuleUnderlyingHom Y Λ J) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun _ _ _ h ↦ h

private instance (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Presheaf.IsLocallySurjective Y.smallEtaleTopology (etaleConstantModuleUnderlyingHom Y Λ J) :=
  Presheaf.isLocallySurjective_of_surjective _ _ fun _ x ↦ ⟨x, rfl⟩

/-- Extend the scalar action by gluing, keeping the underlying abelian sheaf.
(blueprint: lem-sfb-ring-etale-constant-module-equivalence)
-/
private def etaleConstantModuleRealization
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    SheafOfModules.{u + 1} (etaleConstantModuleRing Y Λ) :=
  PresheafOfModules.sheafify (R := etaleConstantModuleRing Y Λ)
    (etaleConstantModuleRingUnit Y Λ)
    (M₀ := etaleConstantModulePresheaf Y Λ J)
    (A := (sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J)
    (etaleConstantModuleUnderlyingHom Y Λ J)

/-- Extension of the constant scalar action, on objects and morphisms.
(blueprint: lem-sfb-ring-etale-constant-module-equivalence)
-/
private def etaleConstantModuleFunctor :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      SheafOfModules.{u + 1} (etaleConstantModuleRing Y Λ) where
  obj J := etaleConstantModuleRealization Y Λ J
  map {J K} f := PresheafOfModules.sheafifyMap (etaleConstantModuleRingUnit Y Λ)
    (etaleConstantModuleUnderlyingHom Y Λ J)
    (etaleConstantModuleUnderlyingHom Y Λ K)
    (PresheafOfModules.homMk
      (M₁ := etaleConstantModulePresheaf Y Λ J)
      (M₂ := etaleConstantModulePresheaf Y Λ K)
      (whiskerRight f.hom (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
      (fun X r m ↦ (f.hom.app X).hom.map_smul r m))
    ((sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map f)
    (by ext X x; rfl)
  map_id J := by ext X x; rfl
  map_comp f g := by ext X x; rfl

/-- The scalar extension keeps the underlying abelian presheaf.
(blueprint: lem-sfb-ring-etale-constant-module-equivalence)
-/
private def etaleConstantModuleUnderlyingIso
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((etaleConstantModuleFunctor Y Λ).obj J).val.presheaf ≅
      J.obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} :=
  Iso.refl _

/-- Restrict a module over the constant ring sheaf to its constant scalars.
(blueprint: lem-sfb-ring-etale-constant-module-equivalence)
-/
private def etaleConstantModuleRestriction
    (M : SheafOfModules.{u + 1} (etaleConstantModuleRing Y Λ)) :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj :=
    let P := (PresheafOfModules.restrictScalars (etaleConstantModuleRingUnit Y Λ)).obj M.val
    { obj := fun X ↦ P.obj X
      map := fun f ↦ P.map f
      map_id := fun X ↦ by ext x; simp; rfl
      map_comp := fun f g ↦ by ext x; simp; rfl }
  property := by
    apply Presheaf.isSheaf_of_isSheaf_comp Y.smallEtaleTopology _
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    exact M.isSheaf

/-- Restriction of scalars on sheaves and their morphisms.
(blueprint: lem-sfb-ring-etale-constant-module-equivalence)
-/
private def etaleConstantModuleRestrictionFunctor :
    SheafOfModules.{u + 1} (etaleConstantModuleRing Y Λ) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj M := etaleConstantModuleRestriction Y Λ M
  map f := ObjectProperty.homMk
    { app := fun X ↦ (ModuleCat.restrictScalars
        ((etaleConstantModuleRingUnit Y Λ).app X).hom).map (f.val.app X)
      naturality := fun {_ _} g ↦ by ext x; exact PresheafOfModules.naturality_apply f.val g x }
  map_id M := by ext X x; rfl
  map_comp f g := by ext X x; rfl

/-- The identity on sections identifies restriction after extension with the original sheaf.
(blueprint: lem-sfb-ring-etale-constant-module-equivalence)
-/
private def etaleConstantModuleUnitIso :
    𝟭 (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ≅
      etaleConstantModuleFunctor Y Λ ⋙ etaleConstantModuleRestrictionFunctor Y Λ := by
  refine NatIso.ofComponents (fun J ↦ ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun X ↦ ?_) ?_
    · let f := (PresheafOfModules.toSheafify
        (etaleConstantModuleRingUnit Y Λ)
        (M₀ := etaleConstantModulePresheaf Y Λ J)
        (A := (sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj J)
        (etaleConstantModuleUnderlyingHom Y Λ J)).app X
      exact LinearEquiv.toModuleIso (LinearEquiv.ofBijective f.hom
        ⟨fun _ _ h ↦ h, fun x ↦ ⟨x, rfl⟩⟩)
    · intro X Z f
      ext x
      rfl
  · intro J K f
    ext X x
    rfl

/-- The identity of the underlying abelian presheaf of a ringed-site module, viewed as a map out of
its restriction to constant scalars.
(blueprint: lem-sfb-ring-etale-constant-module-equivalence)
-/
private def etaleConstantModuleCounitUnderlyingHom
    (M : SheafOfModules.{u + 1} (etaleConstantModuleRing Y Λ)) :
    (etaleConstantModulePresheaf Y Λ (etaleConstantModuleRestriction Y Λ M)).presheaf ⟶
      (⟨M.val.presheaf, M.isSheaf⟩ : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj :=
  𝟙 _

private instance (M : SheafOfModules.{u + 1} (etaleConstantModuleRing Y Λ)) :
    Presheaf.IsLocallyInjective Y.smallEtaleTopology
      (etaleConstantModuleCounitUnderlyingHom Y Λ M) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun _ _ _ h ↦ h

private instance (M : SheafOfModules.{u + 1} (etaleConstantModuleRing Y Λ)) :
    Presheaf.IsLocallySurjective Y.smallEtaleTopology
      (etaleConstantModuleCounitUnderlyingHom Y Λ M) :=
  Presheaf.isLocallySurjective_of_surjective _ _ fun _ x ↦ ⟨x, rfl⟩

/-- The universal property of scalar extension supplies the counit.
(blueprint: lem-sfb-ring-etale-constant-module-equivalence)
-/
private def etaleConstantModuleCounitHom
    (M : SheafOfModules.{u + 1} (etaleConstantModuleRing Y Λ)) :
    (etaleConstantModuleFunctor Y Λ).obj
      ((etaleConstantModuleRestrictionFunctor Y Λ).obj M) ⟶ M :=
  (PresheafOfModules.sheafifyHomEquiv
    (etaleConstantModuleRingUnit Y Λ)
    (M₀ := etaleConstantModulePresheaf Y Λ (etaleConstantModuleRestriction Y Λ M))
    (A := ⟨M.val.presheaf, M.isSheaf⟩)
    (etaleConstantModuleCounitUnderlyingHom Y Λ M)).symm
      (PresheafOfModules.homMk (𝟙 _) (fun _ _ _ ↦ rfl))

/-- The counit is the identity on underlying abelian presheaves.
(blueprint: lem-sfb-ring-etale-constant-module-equivalence)
-/
private lemma etaleConstantModuleCounitHom_underlying
    (M : SheafOfModules.{u + 1} (etaleConstantModuleRing Y Λ)) :
    (PresheafOfModules.toPresheaf _).map (etaleConstantModuleCounitHom Y Λ M).val =
      𝟙 M.val.presheaf := by
  have h := PresheafOfModules.comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom
    (etaleConstantModuleRingUnit Y Λ)
    (M₀ := etaleConstantModulePresheaf Y Λ (etaleConstantModuleRestriction Y Λ M))
    (A := ⟨M.val.presheaf, M.isSheaf⟩)
    (etaleConstantModuleCounitUnderlyingHom Y Λ M) M.isSheaf
    (PresheafOfModules.homMk (𝟙 _) (fun _ _ _ ↦ rfl))
  exact (Category.id_comp _).symm.trans h

/-- Extending the restricted scalar action recovers the original ringed-site module.
(blueprint: lem-sfb-ring-etale-constant-module-equivalence)
-/
private def etaleConstantModuleCounitIso :
    etaleConstantModuleRestrictionFunctor Y Λ ⋙ etaleConstantModuleFunctor Y Λ ≅
      𝟭 (SheafOfModules.{u + 1} (etaleConstantModuleRing Y Λ)) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let f := etaleConstantModuleCounitHom Y Λ M
    have hf (X : Y.Etaleᵒᵖ) (x : ((etaleConstantModuleFunctor Y Λ).obj
        ((etaleConstantModuleRestrictionFunctor Y Λ).obj M)).val.obj X) :
        f.val.app X x = x :=
      CategoryTheory.congr_fun
        (NatTrans.congr_app (etaleConstantModuleCounitHom_underlying Y Λ M) X) x
    let e : ((etaleConstantModuleFunctor Y Λ).obj
        ((etaleConstantModuleRestrictionFunctor Y Λ).obj M)).val ≅ M.val :=
      PresheafOfModules.isoMk
      (fun X ↦ LinearEquiv.toModuleIso (LinearEquiv.ofBijective (f.val.app X).hom
        ⟨fun x y h ↦ (hf X x).symm.trans (h.trans (hf X y)),
          fun x ↦ ⟨x, hf X x⟩⟩))
      (fun {_ _} g ↦ f.val.naturality g)
    exact (SheafOfModules.fullyFaithfulForget (etaleConstantModuleRing Y Λ)).preimageIso e
  · intro M N f
    apply (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map_injective
    change (PresheafOfModules.toPresheaf _).map
        ((etaleConstantModuleFunctor Y Λ).map
          ((etaleConstantModuleRestrictionFunctor Y Λ).map f)).val ≫
        (PresheafOfModules.toPresheaf _).map (etaleConstantModuleCounitHom Y Λ N).val =
      (PresheafOfModules.toPresheaf _).map (etaleConstantModuleCounitHom Y Λ M).val ≫
        (PresheafOfModules.toPresheaf _).map f.val
    rw [etaleConstantModuleCounitHom_underlying, etaleConstantModuleCounitHom_underlying]
    ext X x
    rfl

/-- Extending to the constant ring sheaf is an equivalence of categories.

Source: Stacks Project, Modules on Sites, Sections 093I and 03CV, and Sites Example 0H7J.
The equivalence argument is the constant-scalar construction in steps 1--3 of
lem-weil-pbc-injective-etale-constant-ring-module.
(blueprint: lem-sfb-ring-etale-constant-module-equivalence)

Proof: Let R be the sheafification of the constant ring presheaf. For a module-valued
sheaf J, view its underlying abelian presheaf as modules over the constant ring
presheaf. Apply the module-sheafification construction to the identity map of the
underlying abelian sheaf. This extends the scalar action to R and leaves the
abelian presheaf unchanged. The same construction on morphisms gives a functor F.
Restrict scalars along the constant-ring sheafification map to define G. Its
underlying abelian presheaf is still the original sheaf, so it is a module-valued
sheaf. The canonical map to module sheafification is linear and is the identity
on sections. Its bijectivity gives the natural isomorphism from J to G(F(J)).
For M over R, the universal property of module sheafification extends the identity
of the scalar-restricted presheaf to a morphism F(G(M)) to M. The factorization
identity in that universal property shows that its underlying abelian-presheaf
map is the identity. Each component is thus a bijective linear map, yielding an
isomorphism of presheaves of modules and then of sheaves of modules. Naturality
holds because both maps are the identity on sections. These two natural
isomorphisms exhibit F and G as inverse equivalences. Neither construction needs
nonzero scalars or a nonempty scheme. -/
private theorem etaleConstantModuleFunctor_isEquivalence :
    (etaleConstantModuleFunctor Y Λ).IsEquivalence :=
  Functor.IsEquivalence.mk' (etaleConstantModuleRestrictionFunctor Y Λ)
    (etaleConstantModuleUnitIso Y Λ) (etaleConstantModuleCounitIso Y Λ)

/-- Module-valued étale sheaves over an arbitrary ring are modules over its constant ring
sheaf, by an equivalence preserving the underlying abelian sheaf.
Source: Stacks, Tags 093I and 03CV; the constant-scalar construction is a substep of
Stacks 0F0D with coefficient restriction.
(blueprint: lem-sfb-ring-etale-constant-module-equivalence).

Proof: extend the sectionwise scalar action along the sheafification of the constant ring
presheaf. Module sheafification leaves the underlying abelian sheaf unchanged. Restriction
along the sheafification unit gives an inverse. The identity on sections supplies both
natural isomorphisms; the counit is linear by the module sheafification universal property.
No step commutes two scalar multiplications, so an arbitrary ring suffices. -/
@[no_expose]
def constantModuleEquivalence :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ≌ SheafOfModules.{u + 1}
      ((constantSheaf Y.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ)) :=
  letI := etaleConstantModuleFunctor_isEquivalence Y Λ
  (etaleConstantModuleFunctor Y Λ).asEquivalence

/-- The equivalence `constantModuleEquivalence` does not change the underlying abelian sheaf.
(blueprint: lem-sfb-ring-etale-constant-module-equivalence) -/
@[no_expose]
def constantModuleEquivalenceToSheafIso :
    (constantModuleEquivalence Y Λ).functor ⋙ SheafOfModules.toSheaf
        ((constantSheaf Y.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ)) ≅
      sheafCompose Y.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  Iso.refl _

end AlgebraicGeometry.Scheme.FiniteRingCoefficientComparison
