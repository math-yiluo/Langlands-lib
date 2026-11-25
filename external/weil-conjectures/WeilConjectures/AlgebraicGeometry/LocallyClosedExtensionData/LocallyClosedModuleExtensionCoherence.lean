/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.LocallyClosedModuleExtensionCoherence

public import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedModuleExtensionData
import WeilConjectures.AlgebraicGeometry.LocallyClosedCoefficientImmersion.LocallyClosedModuleExtensionModel

/-! Normalized locally closed module extension: assembly from the fixed model.

## References

* Stacks, Tags 02V0 and 09AH
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

namespace LocallyClosedExtensionData

/-- Normalized comparison laws on module sheaves. The two factorization orders follow
by composing `gamma` with `closedComparison` and the open adjunction; normalization
and the Hom bijection make the comparison between any two factorizations unique. -/
structure Coherent (E : LocallyClosedExtensionData.{u}) : Prop where
  full : ∀ {S X : LocallyClosedCoefficients.{u}} (a : LocallyClosedCoefficientImmersion S X),
    (E.extension a).Full
  faithful : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X), (E.extension a).Faithful
  homBijection : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (M N : proEtaleRingModules S.scheme S.ring),
    Function.Bijective (fun f : (E.extension a).obj M ⟶ (E.extension a).obj N ↦
      (E.restriction a).inv.app M ≫ a.pull.map f ≫ (E.restriction a).hom.app N)
  normalized : ∀ {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S),
    LocallyClosedBinaryNormalization (E.extension a) (E.extension b) a.pull b.pull
      (a.comp b).pull (E.extension (a.comp b)) (E.restriction a) (E.restriction b)
      (E.restriction (a.comp b)) (a.pullComp b) (E.gamma a b)
  innerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : a.comp (.identity S) = a,
      E.gamma a (.identity S) ≪≫ eqToIso (congrArg E.extension h) =
        Functor.isoWhiskerRight (E.identity S) (E.extension a) ≪≫
          Functor.leftUnitor (E.extension a)
  outerUnit : ∀ {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X),
    ∃ h : (LocallyClosedCoefficientImmersion.identity X).comp a = a,
      E.gamma (.identity X) a ≪≫ eqToIso (congrArg E.extension h) =
        Functor.isoWhiskerLeft (E.extension a) (E.identity X) ≪≫
          Functor.rightUnitor (E.extension a)
  associative : ∀ {S X T W : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (d : LocallyClosedCoefficientImmersion W T),
    ∃ h : (a.comp b).comp d = a.comp (b.comp d),
      Functor.isoWhiskerRight (E.gamma b d) (E.extension a) ≪≫ E.gamma a (b.comp d) =
        Functor.associator (E.extension d) (E.extension b) (E.extension a) ≪≫
          Functor.isoWhiskerLeft (E.extension d) (E.gamma a b) ≪≫ E.gamma (a.comp b) d ≪≫
            eqToIso (congrArg E.extension h)

end LocallyClosedExtensionData

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleDirectImage

private theorem restriction_hom_bijective
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    [F.Full] [F.Faithful] (r : F ⋙ L ≅ 𝟭 C) (M N : C) :
    Function.Bijective (fun f : F.obj M ⟶ F.obj N ↦
      r.inv.app M ≫ L.map f ≫ r.hom.app N) := by
  have hr (f : M ⟶ N) : r.inv.app M ≫ L.map (F.map f) ≫ r.hom.app N = f := by
    simpa using congrArg (fun g ↦ r.inv.app M ≫ g) (r.hom.naturality f)
  constructor
  · intro f g h
    obtain ⟨f, rfl⟩ := F.map_surjective f
    obtain ⟨g, rfl⟩ := F.map_surjective g
    change r.inv.app M ≫ L.map (F.map f) ≫ r.hom.app N =
      r.inv.app M ≫ L.map (F.map g) ≫ r.hom.app N at h
    rw [hr, hr] at h
    exact congrArg F.map h
  · intro f
    exact ⟨F.map f, hr f⟩

private theorem restriction_injective
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    [F.Full] [F.Faithful] (r : F ⋙ L ≅ 𝟭 C)
    {A : D} {M N : C} (e : A ≅ F.obj M) {f g : A ⟶ F.obj N}
    (h : L.map f = L.map g) : f = g := by
  apply (cancel_epi e.inv).mp
  apply (restriction_hom_bijective F L r M N).injective
  simp only [Functor.map_comp, h]

private theorem normalized_existsUnique
    {C D : Type*} [Category C] [Category D] (H : C ⥤ D) (L : D ⥤ C)
    [H.Full] [H.Faithful] (r : H ⋙ L ≅ 𝟭 C) (A : D) (M : C)
    (t : L.obj A ⟶ M)
    (h : ∃ e : A ≅ H.obj M, LocallyClosedObjectNormalization H L r t e) :
    ∃! e : A ≅ H.obj M, LocallyClosedObjectNormalization H L r t e := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply restriction_injective H L r e
  apply (cancel_mono (r.hom.app M)).mp
  exact he'.trans he.symm

private def compositeRestriction
    {A B C : Type*} [Category A] [Category B] [Category C]
    (Ea : B ⥤ C) (Eb : A ⥤ B) (La : C ⥤ B) (Lb : B ⥤ A) (Lab : C ⥤ A)
    (ra : Ea ⋙ La ≅ 𝟭 B) (rb : Eb ⋙ Lb ≅ 𝟭 A) (c : Lab ≅ La ⋙ Lb) :
    (Eb ⋙ Ea) ⋙ Lab ≅ 𝟭 A :=
  NatIso.ofComponents (fun M ↦ c.app (Ea.obj (Eb.obj M)) ≪≫
    Lb.mapIso (ra.app (Eb.obj M)) ≪≫ rb.app M) (by
    intro M N f
    simp only [Functor.comp_map, Functor.id_map, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom]
    have hc := c.hom.naturality (Ea.map (Eb.map f))
    have ha := ra.hom.naturality (Eb.map f)
    have hb := rb.hom.naturality f
    simp only [Functor.comp_map, Functor.id_map] at hc ha hb
    calc
      _ = c.hom.app _ ≫ Lb.map (La.map (Ea.map (Eb.map f))) ≫
          Lb.map (ra.hom.app (Eb.obj N)) ≫ rb.hom.app N := by
        rw [← Category.assoc, hc, Category.assoc]
      _ = c.hom.app _ ≫ Lb.map
          (La.map (Ea.map (Eb.map f)) ≫ ra.hom.app (Eb.obj N)) ≫ rb.hom.app N := by
        rw [Lb.map_comp, Category.assoc]
      _ = c.hom.app _ ≫ Lb.map
          (ra.hom.app (Eb.obj M) ≫ Eb.map f) ≫ rb.hom.app N := by rw [ha]
      _ = c.hom.app _ ≫ Lb.map (ra.hom.app (Eb.obj M)) ≫
          Lb.map (Eb.map f) ≫ rb.hom.app N := by rw [Lb.map_comp, Category.assoc]
      _ = _ := by rw [hb]; simp only [Category.assoc])

private structure OpenNormalization
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) where
  adj : F ⊣ L
  normalized : LocallyClosedOpenNormalization F L r adj

private theorem openNormalization_nonempty
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C)
    (h : ∃ adj : F ⊣ L, LocallyClosedOpenNormalization F L r adj) :
    Nonempty (OpenNormalization F L r) := ⟨⟨h.choose, h.choose_spec⟩⟩

@[irreducible] private def openNormalization
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C)
    (h : ∃ adj : F ⊣ L, LocallyClosedOpenNormalization F L r adj) :
    OpenNormalization F L r := Classical.choice (openNormalization_nonempty F L r h)

private structure ClosedNormalization
    {C D : Type*} [Category C] [Category D] (F P : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) (d : P ⋙ L ⟶ 𝟭 C) where
  iso : F ≅ P
  normalized : LocallyClosedClosedNormalization F P L r d iso

private theorem closedNormalization_nonempty
    {C D : Type*} [Category C] [Category D] (F P : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) (d : P ⋙ L ⟶ 𝟭 C)
    (h : ∃ e : F ≅ P, LocallyClosedClosedNormalization F P L r d e) :
    Nonempty (ClosedNormalization F P L r d) := ⟨⟨h.choose, h.choose_spec⟩⟩

@[irreducible] private def closedNormalization
    {C D : Type*} [Category C] [Category D] (F P : C ⥤ D) (L : D ⥤ C)
    (r : F ⋙ L ≅ 𝟭 C) (d : P ⋙ L ⟶ 𝟭 C)
    (h : ∃ e : F ≅ P, LocallyClosedClosedNormalization F P L r d e) :
    ClosedNormalization F P L r d :=
  Classical.choice (closedNormalization_nonempty F P L r d h)

end AlgebraicGeometry.Scheme
