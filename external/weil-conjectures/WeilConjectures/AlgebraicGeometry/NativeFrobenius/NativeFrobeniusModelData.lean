/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmallSite.SmallSiteModuleHom
public import WeilConjectures.AlgebraicGeometry.Adic.AdicSectionModuleEquivalence
public import WeilConjectures.SixFunctors.WeilFrobeniusAction.WeilFrobeniusActionResolutions

/-! # Explicit ordinary small model for native Frobenius

## References

* Stacks 03D6
* Stacks 03EO
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.NativeFrobenius
open WeilConjectures.WeilFrobeniusAction

variable (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- The actual locally finite coefficient functions, restricted to the lifted site. -/
abbrev ring : Sheaf (topology Y) CommRingCat.{u + 1} :=
  SheafOfModules.SmallSite.coefficient (Scheme.ProEt.topology Y) (comparisonRing l Y)

/-- The ordinary equivalence first un-lifts the site, then reverses native section encoding. -/
def equivalence : TwistedActionRingedSite.Modules (ring Y l) ≌ AdicSheaf l Y :=
  ((SheafOfModules.SmallSite.equivalence (Scheme.ProEt.topology Y)
    (comparisonRing l Y)).trans (adicSectionModuleEquivalence l Y).symm).changeFunctor
      (G := SheafOfModules.SmallSite.restriction (Scheme.ProEt.topology Y)
        (comparisonRing l Y) ⋙ (adicSectionModuleEquivalence l Y).inverse)
      (Functor.isoWhiskerRight (eqToIso (SheafOfModules.SmallSite.equivalence_functor
        (Scheme.ProEt.topology Y) (comparisonRing l Y)))
          (adicSectionModuleEquivalence l Y).inverse)

/-- The equivalence retains addition of actual section maps. -/
instance equivalence_additive : (equivalence Y l).functor.Additive := by
  have : (comparisonModuleFunctor l Y).Additive :=
    { map_add := by intros; ext V x; rfl }
  have : (adicSectionModuleEquivalence l Y).functor.Additive :=
    inferInstanceAs (comparisonModuleFunctor l Y).Additive
  have := (adicSectionModuleEquivalence l Y).inverse_additive
  exact inferInstanceAs (SheafOfModules.SmallSite.restriction
    (Scheme.ProEt.topology Y) (comparisonRing l Y) ⋙
      (adicSectionModuleEquivalence l Y).inverse).Additive

private theorem presieve_map_comp {C D E : Type*}
    [Category C] [Category D] [Category E] (F : C ⥤ D) (G : D ⥤ E)
    {X : C} (S : Presieve X) : (S.map F).map G = S.map (F ⋙ G) := by
  funext W f
  apply propext
  constructor
  · rintro ⟨⟨h⟩⟩
    exact ⟨h⟩
  · rintro ⟨h⟩
    exact ⟨⟨h⟩⟩

private theorem postcompose_continuous (g : Y ≅ Y) :
    (postcompose g).functor.IsContinuous (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology Y) := by
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy (postcompose g).functor
    (Scheme.ProEt.precoverage Y) (Scheme.ProEt.precoverage Y)
  intro U S hS
  change (S.map (postcompose g).functor).map (Scheme.ProEt.forget Y ⋙ Over.forget Y) ∈
    Scheme.proetalePrecoverage _
  change S.map (Scheme.ProEt.forget Y ⋙ Over.forget Y) ∈ Scheme.proetalePrecoverage _ at hS
  rw [presieve_map_comp]
  exact hS

/-- Both directions of inverse geometric translation preserve covers. -/
theorem translation_continuous (g : Y ≅ Y) :
    (translation g).functor.IsContinuous (topology Y) (topology Y) ∧
      (translation g).inverse.IsContinuous (topology Y) (topology Y) := by
  have : AsSmall.up.IsContinuous (Scheme.ProEt.topology Y) (topology Y) :=
    SheafOfModules.SmallSite.up_continuous (Scheme.ProEt.topology Y)
  have : AsSmall.down.IsContinuous (topology Y) (Scheme.ProEt.topology Y) := inferInstance
  have := postcompose_continuous Y g
  have := postcompose_continuous Y g.symm
  have : (postcompose g.symm).inverse.IsContinuous (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology Y) := postcompose_continuous Y g
  have : ((postcompose g.symm).trans
      (AsSmall.equiv : Y.ProEt ≌ Site Y)).functor.IsContinuous
      (Scheme.ProEt.topology Y) (topology Y) :=
    Functor.isContinuous_comp (postcompose g.symm).functor AsSmall.up
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Y) (topology Y)
  have : ((postcompose g.symm).trans
      (AsSmall.equiv : Y.ProEt ≌ Site Y)).inverse.IsContinuous
      (topology Y) (Scheme.ProEt.topology Y) :=
    Functor.isContinuous_comp AsSmall.down (postcompose g.symm).inverse
      (topology Y) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Y)
  exact ⟨Functor.isContinuous_comp AsSmall.down _ _ (Scheme.ProEt.topology Y) _,
    Functor.isContinuous_comp _ AsSmall.up _ (Scheme.ProEt.topology Y) _⟩

/-- Coefficient functions have exactly the same values under postcomposition. -/
def ringIso (g : Y ≅ Y) :
    let _ := (translation_continuous Y g).2
    ((translation g).inverse.sheafPushforwardContinuous CommRingCat.{u + 1}
      (topology Y) (topology Y)).obj (ring Y l) ≅ ring Y l := by
  let _ := (translation_continuous Y g).2
  exact ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))

end AlgebraicGeometry.ProEtale.NativeFrobenius
