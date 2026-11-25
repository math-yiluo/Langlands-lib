/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Constant sheaves and the constructed set inverse image

Source: Stacks Project, Tags 03CB, 03CC, and 03P5.
(blueprint: def-weil-pbc-etale-set-constant-pullback-comparison).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The comparison for the actual left-Kan-extension inverse image of sets.
Compose the constant-sheaf adjunction with the constructed inverse-image adjunction.
Its right adjoint is global sections: base change preserves the terminal etale object.
Uniqueness of left adjoints then gives this comparison, in the full value universe.
Source: Stacks Project, Tags 03CB, 03CC, and 03P5.
(blueprint: def-weil-pbc-etale-set-constant-pullback-comparison). -/
noncomputable def etaleSetConstantPullbackComparison
    {P U : Scheme.{u}} (h : U ⟶ P) :
    constantSheaf P.smallEtaleTopology (Type (u + 1)) ⋙ Scheme.etaleSetPullback h ≅
      constantSheaf U.smallEtaleTopology (Type (u + 1)) := by
  let b := MorphismProperty.Over.pullback @Etale ⊤ h
  letI : b.IsContinuous P.smallEtaleTopology U.smallEtaleTopology :=
    Etale.isContinuous_overPullback h
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    b (Type (u + 1)) P.smallEtaleTopology U.smallEtaleTopology
  let e : b.sheafPushforwardContinuous (Type (u + 1))
      P.smallEtaleTopology U.smallEtaleTopology ⋙
        (sheafSections P.smallEtaleTopology (Type (u + 1))).obj (op (⊤_ P.Etale)) ≅
      (sheafSections U.smallEtaleTopology (Type (u + 1))).obj (op (⊤_ U.Etale)) :=
    NatIso.ofComponents
      (fun H ↦ H.obj.mapIso (PreservesTerminal.iso b).op.symm)
      (fun α ↦ (α.hom.naturality _).symm)
  exact (((constantSheafAdj P.smallEtaleTopology (Type (u + 1))
    terminalIsTerminal).comp adj).ofNatIsoRight e).leftAdjointUniq
      (constantSheafAdj U.smallEtaleTopology (Type (u + 1)) terminalIsTerminal)

end AlgebraicGeometry
