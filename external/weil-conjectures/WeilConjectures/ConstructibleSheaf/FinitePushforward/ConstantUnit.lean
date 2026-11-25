/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# The unit of `g^* ⊣ g_*` on constant sheaves

For a morphism of schemes `g : Z ⟶ Y` and a `Λ`-module `M`, the unit `M_Y ⟶ g_* g^* M_Y`
followed by `g_*` of the identification `g^* M_Y ≅ M_Z` sends the constant section `m` over an
étale `Y`-scheme `V` to the constant section `m` over `V ×_Y Z`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {Z Y : Scheme.{u}} (g : Z ⟶ Y)
  (M : ModuleCat.{u + 1} Λ)

/-- The unit of `g^* ⊣ g_*` at the constant sheaf `M_Y`, followed by `g_*` of
`g^* M_Y ≅ M_Z`. -/
noncomputable def Etale.constantSheafUnit :
    (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M ⟶
      (g)_*[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
  (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _ ≫
    (g)_*[ModuleCat.{u + 1} Λ].map ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M)

/-- **The unit on constant sections.** -/
theorem Etale.constantSheafUnit_app_toSheafify (V : Y.Etale) (m : M) :
    (Etale.constantSheafUnit g M).hom.app (op V)
      ((CategoryTheory.toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
        (op V) m) =
      (CategoryTheory.toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M)).app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V)) m := by
  let adjY := constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) terminalIsTerminal
  let adjZ := constantSheafAdj Z.smallEtaleTopology (ModuleCat.{u + 1} Λ) terminalIsTerminal
  let e := Etale.lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} Λ) g
  let adj := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g
  have key : (adjY.unit.app M ≫ ((sheafSections Y.smallEtaleTopology _).obj (op (⊤_ Y.Etale))).map
      (adj.unit.app ((constantSheaf Y.smallEtaleTopology _).obj M)) ≫ e.hom.app _) ≫
      ((sheafSections Z.smallEtaleTopology _).obj (op (⊤_ Z.Etale))).map
        ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M) = adjZ.unit.app M :=
    Adjunction.unit_leftAdjointUniq_hom_app ((adjY.comp adj).ofNatIsoRight e) adjZ M
  have h := congr(($key).hom m)
  -- constant sections are compatible with restriction
  have hts {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) [HasWeakSheafify J
      (ModuleCat.{u + 1} Λ)] {U W : C} (f : U ⟶ W) :
      (sheafify J ((Functor.const Cᵒᵖ).obj M)).map f.op
        ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op W) m) =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U) m :=
    (congr(($((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).naturality
      f.op)).hom m)).symm
  let θ := Etale.constantSheafUnit g M
  let F := MorphismProperty.Over.pullback @Etale ⊤ g
  let i := (PreservesTerminal.iso g.Etale)
  let G := (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let x := (CategoryTheory.toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
    (op (⊤_ Y.Etale)) m
  have h₁ : G.obj.map i.op.symm.hom (θ.hom.app (op (⊤_ Y.Etale)) x) =
      (CategoryTheory.toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M)).app
        (op (⊤_ Z.Etale)) m :=
    (NatTrans.naturality_apply ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M).hom
      i.op.symm.hom _).symm.trans h
  have hT : θ.hom.app (op (⊤_ Y.Etale)) x =
      (CategoryTheory.toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M)).app
        (op (F.obj (⊤_ Y.Etale))) m := by
    have h₂ := congrArg (G.obj.map i.op.hom) h₁
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Iso.symm_hom, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.id_apply] at h₂
    exact h₂.trans (hts Z.smallEtaleTopology i.hom)
  have hn := NatTrans.naturality_apply θ.hom (terminal.from V).op x
  rw [← hts Y.smallEtaleTopology (terminal.from V)]
  refine hn.trans ?_
  change G.obj.map (F.map (terminal.from V)).op (θ.hom.app (op (⊤_ Y.Etale)) x) = _
  rw [hT]
  exact hts Z.smallEtaleTopology _

end AlgebraicGeometry
