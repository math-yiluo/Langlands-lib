/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Module pullback and abelian pullback have isomorphic underlying sheaves.
Source: Stacks Project, Modules on Sites, Tags 03D3 and 03D7 (inverse image of modules).
(blueprint: lemma-weil-pbc-etale-pullback-forget-modules)

Proof: Both pullbacks are formed by left Kan extension of the underlying presheaf,
followed by sheafification. Forgetting module structure preserves colimits and finite
limits. It therefore commutes with the left Kan extension and with sheafification;
composing these two comparison isomorphisms gives the asserted isomorphism. -/
theorem pullback_forget_modules_iso (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((upperStar (ModuleCat.{u + 1} Λ) p).obj F) ≅
      (upperStar AddCommGrpCat.{u + 1} p).obj
        ((sheafCompose Y.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let L := (MorphismProperty.Over.pullback @Etale ⊤ p).op
  have : CategoryTheory.Limits.HasLimitsOfSize.{u + 1, u + 1}
      (ModuleCat.{u + 1} Λ) := inferInstance
  have : CategoryTheory.Limits.HasLimitsOfSize.{u + 1, u + 1}
      AddCommGrpCat.{u + 1} := inferInstance
  have : CategoryTheory.Limits.HasColimitsOfSize.{u + 1, u + 1}
      AddCommGrpCat.{u + 1} := inferInstance
  have : CategoryTheory.Limits.PreservesLimitsOfSize.{u + 1, u + 1} U := inferInstance
  have : CategoryTheory.Limits.PreservesColimitsOfSize.{u + 1, u + 1} U :=
    ModuleCat.forget₂PreservesColimitsOfSize Λ
  have : X.smallEtaleTopology.PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification X.smallEtaleTopology U
  let e₁ := (sheafComposeNatIso X.smallEtaleTopology U
    (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1})).app
      (L.lan.obj F.obj)
  let e₂ := (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
    ((U.lanCompIsoOfPreserves L).app F.obj)
  exact ⟨e₁.symm ≪≫ e₂⟩

end AlgebraicGeometry.Etale
