/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.Native.NativeBasicComparisons
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenProperInterchange
import WeilConjectures.Compactification.CompactificationCategory

/-! # Comparison of native Weil compactification models

The auxiliary predicate spells out the refinement chain, using the canonical base structures
of the compactifications. It introduces no new operations or chosen comparison maps.

## References

* Stacks Project, Tags 0F7I and 0F7J, compactification calculations
* Stacks Project, Tag 0F7I, displayed calculation along a refinement
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The displayed refinement comparison chain, on bounded constructible native inputs.
The local base structures are exactly `Compactification.over`, induced by the proper legs.
All functors and all isomorphisms are in the actual native equivariant derived categories.
-/
noncomputable def nativeWeilCompactificationRefinementComparisons
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (h : X ⟶ Y) [h.IsOver (Spec (CommRingCat.of k₀))]
    (c₁ c₂ : Compactification h) (v : Compactification.Refinement c₁ c₂) : Prop :=
  letI := Compactification.over (k₀ := k₀) c₁
  letI := Compactification.over (k₀ := k₀) c₂
  letI : v.hom.IsOver (Spec (CommRingCat.of k₀)) :=
    ⟨(Category.assoc v.hom c₂.g (Y ↘ Spec (CommRingCat.of k₀))).symm.trans
      (congrArg (fun m ↦ m ≫ Y ↘ Spec (CommRingCat.of k₀)) v.hom_g)⟩
  Nonempty
      ((WeilComplex.objectProperty k₀ l X).ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l c₂.i).mapDerivedCategory ≅
        (WeilComplex.objectProperty k₀ l X).ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l c₁.i).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l v.hom).rightDerivedFunctor) ∧
    Nonempty
      ((WeilComplex.objectProperty k₀ l X).ι ⋙
          ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l h c₂ ≅
        (WeilComplex.objectProperty k₀ l X).ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l c₁.i).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l v.hom).rightDerivedFunctor ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l c₂.g).rightDerivedFunctor) ∧
    Nonempty
      ((WeilComplex.objectProperty k₀ l X).ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l c₁.i).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l v.hom).rightDerivedFunctor ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l c₂.g).rightDerivedFunctor ≅
        (WeilComplex.objectProperty k₀ l X).ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l c₁.i).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l (v.hom ≫ c₂.g)).rightDerivedFunctor) ∧
    (WeilComplex.objectProperty k₀ l X).ι ⋙
        (ProEtaleWeilSheaf.extensionByZero k₀ l c₁.i).mapDerivedCategory ⋙
        (ProEtaleWeilSheaf.lowerStar k₀ l (v.hom ≫ c₂.g)).rightDerivedFunctor =
      (WeilComplex.objectProperty k₀ l X).ι ⋙
        ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l h c₁

/-- Proper refinements compare native compactification models, arbitrary models are naturally
isomorphic, and every model compares with the framework's chosen model. Only existence is
asserted, without a cocycle or independence assertion.
-/
theorem nativeWeilCompactificationModelComparison
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    (h : X ⟶ Y) [h.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] :
    (∀ (c₁ c₂ : Compactification h) [QuasiCompact c₁.i] [QuasiCompact c₂.i]
      (v : Compactification.Refinement c₁ c₂),
      nativeWeilCompactificationRefinementComparisons k₀ l h c₁ c₂ v) ∧
    (∀ (c₁ c₂ : Compactification h) [QuasiCompact c₁.i] [QuasiCompact c₂.i],
      Nonempty
        ((WeilComplex.objectProperty k₀ l X).ι ⋙
            ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l h c₂ ≅
          (WeilComplex.objectProperty k₀ l X).ι ⋙
            ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l h c₁)) ∧
    (∀ (c : Compactification h) [QuasiCompact c.i],
      Nonempty
        ((WeilComplex.objectProperty k₀ l X).ι ⋙
            ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l h c ≅
          WeilComplex.derivedLowerShriek k₀ l h ⋙
            (WeilComplex.objectProperty k₀ l Y).ι)) := by
  classical
  have href : ∀ (c₁ c₂ : Compactification h) [QuasiCompact c₁.i] [QuasiCompact c₂.i]
      (v : Compactification.Refinement c₁ c₂),
      nativeWeilCompactificationRefinementComparisons k₀ l h c₁ c₂ v := by
    intro c₁ c₂ _ _ v
    let := Compactification.over (k₀ := k₀) c₁
    let := Compactification.over (k₀ := k₀) c₂
    let : v.hom.IsOver (Spec (CommRingCat.of k₀)) :=
      ⟨(Category.assoc v.hom c₂.g (Y ↘ Spec (CommRingCat.of k₀))).symm.trans
        (congrArg (fun m ↦ m ≫ Y ↘ Spec (CommRingCat.of k₀)) v.hom_g)⟩
    have : LocallyOfFiniteType (c₁.Z ↘ Spec (CommRingCat.of k₀)) :=
      inferInstanceAs (LocallyOfFiniteType (c₁.g ≫ Y ↘ Spec (CommRingCat.of k₀)))
    have : LocallyOfFiniteType (c₂.Z ↘ Spec (CommRingCat.of k₀)) :=
      inferInstanceAs (LocallyOfFiniteType (c₂.g ≫ Y ↘ Spec (CommRingCat.of k₀)))
    have : QuasiCompact (c₁.Z ↘ Spec (CommRingCat.of k₀)) :=
      inferInstanceAs (QuasiCompact (c₁.g ≫ Y ↘ Spec (CommRingCat.of k₀)))
    have : QuasiCompact (c₂.Z ↘ Spec (CommRingCat.of k₀)) :=
      inferInstanceAs (QuasiCompact (c₂.g ≫ Y ↘ Spec (CommRingCat.of k₀)))
    obtain ⟨eid⟩ := (nativeWeilBasicComparisons k₀ l).2.1 X
    obtain ⟨e⟩ := WeilComplex.nonempty_extensionByZero_rightDerivedLowerStar_iso
      k₀ l c₁.i (𝟙 X) v.hom c₂.i (by simpa using v.i_hom)
    let α := (Functor.isoWhiskerLeft (WeilComplex.objectProperty k₀ l X).ι
      (Functor.isoWhiskerRight eid
        (ProEtaleWeilSheaf.extensionByZero k₀ l c₂.i).mapDerivedCategory ≪≫
        Functor.leftUnitor _)).symm ≪≫ e
    obtain ⟨ecomp⟩ := (nativeWeilBasicComparisons k₀ l).1 c₁.Z c₂.Z Y v.hom c₂.g
    refine ⟨⟨α⟩, ⟨Functor.isoWhiskerRight α
      (ProEtaleWeilSheaf.lowerStar k₀ l c₂.g).rightDerivedFunctor⟩,
      ⟨Functor.isoWhiskerLeft ((WeilComplex.objectProperty k₀ l X).ι ⋙
        (ProEtaleWeilSheaf.extensionByZero k₀ l c₁.i).mapDerivedCategory) ecomp.symm⟩, ?_⟩
    dsimp [ProEtaleWeilSheaf.rightDerivedLowerShriek]
    simp only [v.hom_g]
  have hmodel : ∀ (c₁ c₂ : Compactification h) [QuasiCompact c₁.i] [QuasiCompact c₂.i],
      Nonempty ((WeilComplex.objectProperty k₀ l X).ι ⋙
          ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l h c₂ ≅
        (WeilComplex.objectProperty k₀ l X).ι ⋙
          ProEtaleWeilSheaf.rightDerivedLowerShriek k₀ l h c₁) := by
    intro c₁ c₂ _ _
    have : CompactSpace Y :=
      QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k₀))
    have : QuasiSeparatedSpace Y :=
      quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (CommRingCat.of k₀))
    let d := Compactification.inf c₁ c₂
    have : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
    have hc := (Compactification.compactificationCategory_properties.{u, 0} h).2.2.1 c₁ c₂
    obtain ⟨v₁⟩ := hc.2.2.1
    obtain ⟨v₂⟩ := hc.2.2.2
    obtain ⟨a₁⟩ := (href d c₁ v₁).2.1
    obtain ⟨b₁⟩ := (href d c₁ v₁).2.2.1
    obtain ⟨a₂⟩ := (href d c₂ v₂).2.1
    obtain ⟨b₂⟩ := (href d c₂ v₂).2.2.1
    let γ₁ := a₁ ≪≫ b₁ ≪≫ eqToIso (href d c₁ v₁).2.2.2
    let γ₂ := a₂ ≪≫ b₂ ≪≫ eqToIso (href d c₂ v₂).2.2.2
    exact ⟨γ₂ ≪≫ γ₁.symm⟩
  refine ⟨href, hmodel, ?_⟩
  intro c _
  let c₀ := HasCompactification.compactification h
    (hf := hasCompactification_of_over (k₀ := k₀) h)
  have : QuasiCompact c₀.i := c₀.quasiCompact_openImmersion inferInstance
  obtain ⟨e⟩ := hmodel c₀ c
  exact ⟨e⟩

end AlgebraicGeometry
