/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocallyClosedCoefficientImmersion.LocallyClosedModuleExtensionModel
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
/-! Associativity portion of locally closed model coherence. -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

private noncomputable abbrev ringAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleSheafAdjunction f CommRingCat.{u + 1}

private theorem ring_pull_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    conjugateIsoEquiv (ringAdj g) (ringAdj f)
      (eqToIso (congrArg (fun k ↦ proEtaleSheafInverseImage k CommRingCat.{u + 1}) h)) =
      (eqToIso (congrArg
        (fun k ↦ proEtaleSheafDirectImage k CommRingCat.{u + 1}) h)).symm := by
  cases h
  ext : 1
  simp

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleRingDirectImageMap proEtaleRingCompositeCoefficients proEtaleRingInverseImageComp

private noncomputable abbrev moduleAdj {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) :=
  proEtaleRingModuleAdjunction a.hom X.ring S.ring a.coefficient

@[irreducible] private noncomputable def pushComp {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S) :
    b.push ⋙ a.push ≅ (a.comp b).push :=
  conjugateIsoEquiv ((moduleAdj a).comp (moduleAdj b)) (moduleAdj (a.comp b)) (a.pullComp b)

-- The module compositor is fixed by its sectionwise right-adjoint normalization.
attribute [local irreducible] LocallyClosedCoefficientImmersion.pullComp
  exchangeModuleComposition

-- Comparing underlying direct images requires reducing several module structures.
attribute [local irreducible] proEtaleRingModuleDirectImage

-- The concrete conjugation involves large module functor and adjunction types.
private theorem restriction_injective
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    [F.Full] [F.Faithful] (r : F ⋙ L ≅ 𝟭 C)
    {A : D} {M N : C} (e : A ≅ F.obj M) {f g : A ⟶ F.obj N}
    (h : L.map f = L.map g) : f = g := by
  apply (cancel_epi e.inv).mp
  obtain ⟨f', hf⟩ := F.map_surjective (e.inv ≫ f)
  obtain ⟨g', hg⟩ := F.map_surjective (e.inv ≫ g)
  have hn := r.hom.naturality f'
  have hm := r.hom.naturality g'
  dsimp only [Functor.comp_map, Functor.id_map] at hn hm
  have he : L.map (F.map f') = L.map (F.map g') := by
    rw [hf, hg, L.map_comp, L.map_comp, h]
  rw [he, hm] at hn
  have : f' = g' := (cancel_epi (r.hom.app M)).mp hn.symm
  rw [← hf, ← hg, this]

-- The normalized restrictions of both triple paths have the same three-factor tail.
private theorem normalization_transport
    {A C D : Type*} [Category A] [Category C] [Category D]
    (Ea : C ⥤ D) (Eb : A ⥤ C) (La : D ⥤ C) (Lb : C ⥤ A)
    (L L' : D ⥤ A) (H H' : A ⥤ D)
    (ra : Ea ⋙ La ≅ 𝟭 C) (rb : Eb ⋙ Lb ≅ 𝟭 A)
    (r : H ⋙ L ≅ 𝟭 A) (r' : H' ⋙ L' ≅ 𝟭 A)
    (e : H ≅ H') (c : L ≅ L') (cab : L' ≅ La ⋙ Lb)
    (g : Eb ⋙ Ea ≅ H')
    (ht : ∀ M, L.map (e.inv.app M) ≫ r.hom.app M =
      c.hom.app (H'.obj M) ≫ r'.hom.app M)
    (ng : LocallyClosedBinaryNormalization Ea Eb La Lb L' H' ra rb r' cab g) :
    LocallyClosedBinaryNormalization Ea Eb La Lb L H ra rb r (c ≪≫ cab)
      (g ≪≫ e.symm) := by
  intro M
  change L.map (g.hom.app M ≫ e.inv.app M) ≫ r.hom.app M = _
  rw [Functor.map_comp, Category.assoc, ht, ← Category.assoc, c.hom.naturality]
  rw [Category.assoc, ng M]
  simp only [LocallyClosedCompositeRestrictionMap, Iso.trans_hom,
    NatTrans.comp_app, Functor.comp_obj, Category.assoc]

-- Perform equality transport before specializing to the concrete module functors.
private theorem restriction_transport {S X : LocallyClosedCoefficients.{u}}
    {a b : LocallyClosedCoefficientImmersion S X} (h : a = b)
    (M : proEtaleRingModules S.scheme S.ring) :
    a.pull.map ((eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension h)).inv.app M)
        ≫ a.modelRestriction.hom.app M =
      (eqToIso (congrArg LocallyClosedCoefficientImmersion.pull h)).hom.app
        (b.modelExtension.obj M) ≫ b.modelRestriction.hom.app M := by
  cases h
  simp

-- Instantiating the categorical argument requires reduction of concrete module functors.
end AlgebraicGeometry.Scheme
