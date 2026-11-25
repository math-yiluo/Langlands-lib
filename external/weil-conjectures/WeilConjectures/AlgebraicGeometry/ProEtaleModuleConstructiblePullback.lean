/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal

import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback

/-!
# Pullback of constructible module objects

Source: `ConstructibleSheaf/ProEtaleModule/Def.lean` and
`ConstructibleSheaf/Pullback.lean`; finite presentations and stratifications pull back.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u v₁ v₂ u₁ u₂

open CategoryTheory Limits
open scoped CategoryTheory.Obj

open MonoidalCategory

section Presentation

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    {R : C} {S : D} [MonObj R] [MonObj S]
    [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft S)]

private lemma finitePresentation_of_iso {M N : Mod C R} (e : M ≅ N)
    (hM : Mod.IsFinitelyPresented R M) : Mod.IsFinitelyPresented R N := by
  obtain ⟨n, m, g, ⟨eg⟩⟩ := hM
  exact ⟨n, m, g, ⟨e.symm ≪≫ eg⟩⟩

private lemma finitePresentation_map (F : Mod C R ⥤ Mod D S) [F.Additive]
    [PreservesFiniteColimits F]
    (e : ∀ n : ℕ, F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n)
    {M : Mod C R} (hM : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented S (F.obj M) := by
  obtain ⟨n, m, g, ⟨eg⟩⟩ := hM
  refine ⟨n, m, (e m).inv ≫ F.map g ≫ (e n).hom, ⟨?_⟩⟩
  exact F.mapIso eg ≪≫ PreservesCokernel.iso F g ≪≫
    cokernel.mapIso _ _ (e m) (e n) (by simp)

private instance mapMod_additive (F : C ⥤ D) [F.LaxMonoidal] [F.Additive] :
    (F.mapMod R).Additive where
  map_add := by intros; ext; exact F.map_add

private noncomputable def finiteFree_mapMod (F : C ⥤ D) [F.LaxMonoidal] [F.Additive]
    [PreservesFiniteColimits F] [PreservesFiniteColimits (tensorLeft (F.obj R))] (n : ℕ) :
    (F.mapMod R).obj (Mod.finiteFree R n) ≅ Mod.finiteFree (F.obj R) n :=
  (F.mapMod R).mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
    biproduct.mapIso (fun _ ↦ Iso.refl _)

private lemma finitePresentation_mapMod (F : C ⥤ D) [F.LaxMonoidal] [F.Additive]
    [PreservesFiniteColimits F] [PreservesFiniteColimits (tensorLeft (F.obj R))]
    {M : Mod C R} (hM : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented (F.obj R) ((F.mapMod R).obj M) := by
  exact finitePresentation_map (F.mapMod R) (finiteFree_mapMod F) hM

end Presentation

section SheafPresentation

variable {X : AlgebraicGeometry.Scheme.{u}}
    {R S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S]

private noncomputable def finiteFree_comap (φ : S ⟶ R) [IsMonHom φ] [IsIso φ] (n : ℕ) :
    (Mod.comap φ).obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n :=
  (Mod.comap φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
    biproduct.mapIso (fun _ ↦ by simpa using Mod.regularIsoOfIsIso (inv φ))

private lemma finitePresentation_comap (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    {M : Mod _ R} (hM : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented S ((Mod.comap φ).obj M) :=
  finitePresentation_map (Mod.comap φ) (finiteFree_comap φ) hM

private lemma finitePresentation_of_comap (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    {M : Mod _ R} (hM : Mod.IsFinitelyPresented S ((Mod.comap φ).obj M)) :
    Mod.IsFinitelyPresented R M := by
  apply finitePresentation_of_iso
    (((Mod.comapComp (inv φ) φ).symm ≪≫ Mod.comapCongr (IsIso.inv_hom_id φ) ≪≫
      Mod.comapId R).app M)
  exact finitePresentation_comap (inv φ) hM

lemma localFinitePresentation_of_iso {M N : Mod _ R} (e : M ≅ N)
    (hM : AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented R M) :
    AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented R N := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  exact ⟨𝒰, fun i ↦ finitePresentation_of_iso
    (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapMod R).mapIso e)
    (h𝒰 i)⟩

lemma localFinitePresentation_comap (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    {M : Mod _ R} (hM : AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented R M) :
    AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented S ((Mod.comap φ).obj M) := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine ⟨𝒰, fun i ↦ ?_⟩
  exact finitePresentation_of_iso
    (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (𝒰.f i)).mapModComapIso φ).app M).symm
    (finitePresentation_comap _ (h𝒰 i))

lemma localFinitePresentation_of_comap (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    {M : Mod _ R}
    (hM : AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented S ((Mod.comap φ).obj M)) :
    AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented R M := by
  apply localFinitePresentation_of_iso
    (((Mod.comapComp (inv φ) φ).symm ≪≫ Mod.comapCongr (IsIso.inv_hom_id φ) ≪≫
      Mod.comapId R).app M)
  exact localFinitePresentation_comap (inv φ) hM

lemma constructible_of_iso {M N : Mod _ R} (e : M ≅ N)
    (hM : AlgebraicGeometry.ProEtale.IsConstructibleModuleObject R M) :
    AlgebraicGeometry.ProEtale.IsConstructibleModuleObject R N := by
  obtain ⟨T, hT⟩ := hM
  exact ⟨T, fun a ↦ localFinitePresentation_of_iso
    (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (T.immersion a)).mapMod R).mapIso e)
    (hT a)⟩

lemma constructible_comap (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    {M : Mod _ R} (hM : AlgebraicGeometry.ProEtale.IsConstructibleModuleObject R M) :
    AlgebraicGeometry.ProEtale.IsConstructibleModuleObject S ((Mod.comap φ).obj M) := by
  obtain ⟨T, hT⟩ := hM
  refine ⟨T, fun a ↦ ?_⟩
  exact localFinitePresentation_of_iso
    (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (T.immersion a)).mapModComapIso φ).app
      M).symm (localFinitePresentation_comap _ (hT a))

end SheafPresentation

namespace AlgebraicGeometry.ProEtale

lemma localFinitePresentation_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}} [MonObj R] {M : Mod _ R}
    (hM : IsLocallyFinitelyPresented R M) :
    IsLocallyFinitelyPresented ((f)^*[Ab.{u + 1}].obj R)
      (((f)^*[Ab.{u + 1}].mapMod R).obj M) := by
  obtain ⟨𝒰, h𝒰⟩ := hM
  refine ⟨𝒰.pullback₁ f, fun i ↦ ?_⟩
  let a := pullback.fst f (𝒰.f i)
  let b := pullback.snd f (𝒰.f i)
  let e₁ := Functor.mapModCompIso (𝒰.f i)^*[Ab.{u + 1}] (b)^*[Ab.{u + 1}]
    (upperStarComp Ab.{u + 1} b (𝒰.f i)).inv R
  have hp : Mod.IsFinitelyPresented ((b ≫ 𝒰.f i)^*[Ab.{u + 1}].obj R)
      (((b ≫ 𝒰.f i)^*[Ab.{u + 1}].mapMod R).obj M) := by
    apply finitePresentation_of_comap
      (Functor.compAlgHom (𝒰.f i)^*[Ab.{u + 1}] (b)^*[Ab.{u + 1}]
        (upperStarComp Ab.{u + 1} b (𝒰.f i)).inv R)
    exact finitePresentation_of_iso (e₁.app M)
      (finitePresentation_mapMod (b)^*[Ab.{u + 1}] (h𝒰 i))
  have hp' : Mod.IsFinitelyPresented ((a ≫ f)^*[Ab.{u + 1}].obj R)
      (((a ≫ f)^*[Ab.{u + 1}].mapMod R).obj M) := by
    exact (congrArg (fun g : pullback f (𝒰.f i) ⟶ Y ↦
      Mod.IsFinitelyPresented ((g)^*[Ab.{u + 1}].obj R)
        (((g)^*[Ab.{u + 1}].mapMod R).obj M))
      (show a ≫ f = b ≫ 𝒰.f i from pullback.condition)).mpr hp
  let e₃ := Functor.mapModCompIso (f)^*[Ab.{u + 1}] (a)^*[Ab.{u + 1}]
    (upperStarComp Ab.{u + 1} a f).inv R
  exact finitePresentation_of_iso (e₃.app M).symm (finitePresentation_comap _ hp')

private lemma constructible_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}} [MonObj R] {M : Mod _ R}
    (hM : IsConstructibleModuleObject R M) :
    IsConstructibleModuleObject ((f)^*[Ab.{u + 1}].obj R)
      (((f)^*[Ab.{u + 1}].mapMod R).obj M) := by
  obtain ⟨T, hT⟩ := hM
  refine ⟨T.pullback f, fun i ↦ ?_⟩
  let a := pullback.snd (T.immersion i) f
  let b := pullback.fst (T.immersion i) f
  let e₁ := Functor.mapModCompIso (T.immersion i)^*[Ab.{u + 1}] (b)^*[Ab.{u + 1}]
    (upperStarComp Ab.{u + 1} b (T.immersion i)).inv R
  have hp : IsLocallyFinitelyPresented ((b ≫ T.immersion i)^*[Ab.{u + 1}].obj R)
      (((b ≫ T.immersion i)^*[Ab.{u + 1}].mapMod R).obj M) := by
    apply localFinitePresentation_of_comap
      (Functor.compAlgHom (T.immersion i)^*[Ab.{u + 1}] (b)^*[Ab.{u + 1}]
        (upperStarComp Ab.{u + 1} b (T.immersion i)).inv R)
    exact localFinitePresentation_of_iso (e₁.app M)
      (localFinitePresentation_pullback b (hT i))
  have hp' : IsLocallyFinitelyPresented ((a ≫ f)^*[Ab.{u + 1}].obj R)
      (((a ≫ f)^*[Ab.{u + 1}].mapMod R).obj M) := by
    exact (congrArg (fun g : pullback (T.immersion i) f ⟶ Y ↦
      IsLocallyFinitelyPresented ((g)^*[Ab.{u + 1}].obj R)
        (((g)^*[Ab.{u + 1}].mapMod R).obj M))
      (show a ≫ f = b ≫ T.immersion i from pullback.condition.symm)).mpr hp
  let e₃ := Functor.mapModCompIso (f)^*[Ab.{u + 1}] (a)^*[Ab.{u + 1}]
    (upperStarComp Ab.{u + 1} a f).inv R
  exact localFinitePresentation_of_iso (e₃.app M).symm
    (localFinitePresentation_comap _ hp')

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Pullback preserves constructible module objects.

Source: `ConstructibleSheaf/ProEtaleModule/Def.lean` (constructibility) and
`ConstructibleSheaf/Pullback.lean` (pullback stratification).
Pull back the finite stratification and, on each stratum, the pro-étale cover presenting the
module. Inverse image preserves finite sums and cokernels and takes the regular coefficient
module to the regular pulled-back coefficient module. Thus the pulled-back presentations
are finite presentations. The coefficient comparison identifies these with the prescribed
condensed coefficient modules.
(auxiliary; not a blueprint node) -/
theorem isConstructibleModuleObject_upperStar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ Y) M) :
    IsConstructibleModuleObject (condensedRingObj Λ X) ((f)^*⟦Λ⟧.obj M) := by
  apply constructible_of_iso
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).app
      (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).obj M)).symm
  exact constructible_comap (inv (condensedPullbackHom Λ f)) (constructible_pullback f hM)

end AlgebraicGeometry.ProEtale.CondensedRing
