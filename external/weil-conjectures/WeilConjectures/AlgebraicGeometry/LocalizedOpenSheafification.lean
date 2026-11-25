/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Sheafification and the localized open-site equivalence
Source: Stacks Project, Tag 01CD, localized-site construction.
(blueprint: lem-sc-localized-open-sheafification).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/- Every presheaf is a sheaf for the bottom topology. This lets us reuse the proved
module-sheaf transport adjunction to construct its presheaf counterpart. -/
private def botModuleLift {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) :
    PresheafOfModules.{u} R ⥤ SheafOfModules.{u} (⟨R, Presheaf.isSheaf_bot R⟩) where
  obj M := ⟨M, Presheaf.isSheaf_bot M.presheaf⟩
  map f := ⟨f⟩

private def botModuleLiftFullyFaithful {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) : (botModuleLift R).FullyFaithful where
  preimage f := f.val

private noncomputable def presheafTransportAdjunction
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}
    (φ : S ⟶ F.op ⋙ R) (ψ : R ⟶ G.op ⋙ S)
    (h₁ : Functor.whiskerRight (NatTrans.op adj.counit) R =
      ψ ≫ G.op.whiskerLeft φ)
    (h₂ : φ ≫ F.op.whiskerLeft ψ ≫
      Functor.whiskerRight (NatTrans.op adj.unit) S = 𝟙 S) :
    PresheafOfModules.pushforward.{u} φ ⊣ PresheafOfModules.pushforward.{u} ψ := by
  let Sb : Sheaf (⊥ : GrothendieckTopology C) RingCat.{u} :=
    ⟨S, Presheaf.isSheaf_bot S⟩
  let Rb : Sheaf (⊥ : GrothendieckTopology D) RingCat.{u} :=
    ⟨R, Presheaf.isSheaf_bot R⟩
  have : F.IsContinuous (⊥ : GrothendieckTopology C) (⊥ : GrothendieckTopology D) :=
    ⟨fun _ ↦ Presieve.isSheaf_bot⟩
  have : G.IsContinuous (⊥ : GrothendieckTopology D) (⊥ : GrothendieckTopology C) :=
    ⟨fun _ ↦ Presieve.isSheaf_bot⟩
  let φb : Sb ⟶ (F.sheafPushforwardContinuous RingCat _ _).obj Rb := ⟨φ⟩
  let ψb : Rb ⟶ (G.sheafPushforwardContinuous RingCat _ _).obj Sb := ⟨ψ⟩
  exact (SheafOfModules.pushforwardPushforwardAdj adj φb ψb h₁ h₂).restrictFullyFaithful
    (botModuleLiftFullyFaithful R) (botModuleLiftFullyFaithful S)
    (Iso.refl _) (Iso.refl _)

/-- Construct the comparison before specializing the sites and coefficient rings. -/
private noncomputable def sheafificationTransportIso
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [HasWeakSheafify J AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    [F.IsContinuous J K] [G.IsContinuous K J]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat K J).obj S)
    (h₁ : Functor.whiskerRight (NatTrans.op adj.counit) R.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom)
    (h₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit) S.obj = 𝟙 S.obj) :
    PresheafOfModules.sheafification.{u} (𝟙 R.obj) ⋙ SheafOfModules.pushforward φ ≅
      PresheafOfModules.pushforward φ.hom ⋙
        PresheafOfModules.sheafification.{u} (𝟙 S.obj) :=
  Adjunction.leftAdjointUniq
    ((PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)).comp
      (SheafOfModules.pushforwardPushforwardAdj adj φ ψ h₁ h₂))
    ((presheafTransportAdjunction adj φ.hom ψ.hom h₁ h₂).comp
      (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 S.obj)))

/-- Sheafification commutes with transport along the localized open-site equivalence.
Source: Stacks Project, Tag 01CD, sheafification step in the localized-site construction.
(blueprint: lem-sc-localized-open-sheafification).

Proof: the inverse open-site equivalence identifies presheaves of modules, using
restriction of the structure sheaf for the coefficient rings. Its inverse is
precomposition with the forward site equivalence, with unit and counit supplied
by those of the site equivalence. Covering sieves correspond, so transport
preserves and reflects the sheaf condition. Consequently both displayed
composites are left adjoint to inverse transport followed by forgetting the
sheaf condition: compose the presheaf transport adjunction and the sheafification
adjunction on one side, and the sheafification adjunction and overEquiv adjunction
on the other. Their right adjoints identify by the sectionwise definition of
pushforward. Uniqueness of left adjoints gives the displayed natural isomorphism.
This does not use tensor products, and applies to empty opens and zero rings. -/
theorem exists_localizedOpen_sheafification_iso (X : Scheme.{u}) (U : X.Opens) :
    Nonempty (
      PresheafOfModules.sheafification.{u}
          (R := (moduleRings X.toRingedSpace).over U)
          (𝟙 ((moduleRings X.toRingedSpace).over U).obj) ⋙
          (Scheme.Modules.overEquiv U).functor ≅
        PresheafOfModules.pushforward₀OfCommRingCat
          (TopologicalSpace.Opens.overEquivalence U).inverse (X.sheaf.over U).obj ⋙
          PresheafOfModules.sheafification.{u}
            (R₀ := (moduleRings U.toScheme.toRingedSpace).obj)
            (R := moduleRings U.toScheme.toRingedSpace)
            (𝟙 (moduleRings U.toScheme.toRingedSpace).obj)) := by
  let R := moduleRings X.toRingedSpace
  let e := (TopologicalSpace.Opens.overEquivalence U).symm
  let φ := (U.overPullbackSheafEquivOver.app R).inv
  let ψ := (U.sheafRestrictSheafEquivOver.app R).inv
  have h₁ : Functor.whiskerRight (NatTrans.op e.counit) (R.over U).obj =
      ψ.hom ≫ e.inverse.op.whiskerLeft φ.hom := rfl
  have h₂ : φ.hom ≫ e.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.unit) (U.sheafRestrict.obj R).obj =
        𝟙 (U.sheafRestrict.obj R).obj := by
    ext : 2
    simp [φ, ψ, e, TopologicalSpace.Opens.overPullbackSheafEquivOver,
      TopologicalSpace.Opens.sheafRestrictSheafEquivOver,
      TopologicalSpace.Opens.overEquivalence, eqToHom_map, IsOpenMap.functor]
    rfl
  exact ⟨sheafificationTransportIso e.toAdjunction φ ψ h₁ h₂⟩

end AlgebraicGeometry
