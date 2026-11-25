/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalSectionCone
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Specialization of abelian étale stalks

Source: Stacks Project, etale-cohomology.tex, Tag 0GJ2, section-specialization
(blueprint: def-weil-pbc-etale-stalk-specialization).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Restrict a strict-local section to the germ at a geometric point, then identify
its inverse-image stalk with the stalk at the composite point of the original scheme.
Preceding this by the canonical pointed-neighbourhood restriction gives specialization.
Source: Stacks Project, etale-cohomology.tex, Tag 0GJ2, section-specialization
(blueprint: def-weil-pbc-etale-stalk-specialization). -/
noncomputable def etaleStalkSpecialization
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s)
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Scheme.pointSmallEtale s).sheafFiber.obj F ⟶
      (Scheme.pointSmallEtale (t ≫ Scheme.strictHenselizationStructuralMap s)).sheafFiber.obj F :=
  Classical.choose ((strictLocalSectionCone s).existsUnique_restriction F) ≫
    (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (Scheme.strictHenselizationScheme s))
        (Scheme.Etale.mk (𝟙 (Scheme.strictHenselizationScheme s))) Over.mkIdTerminal)).hom.app
      ((upperStar AddCommGrpCat.{u + 1}
        (Scheme.strictHenselizationStructuralMap s)).obj F) ≫
    (Scheme.pointSmallEtale t).toPresheafFiber
      (Scheme.Etale.mk (𝟙 (Scheme.strictHenselizationScheme s)))
      (Over.homMk t (Category.comp_id t))
      ((upperStar AddCommGrpCat.{u + 1}
        (Scheme.strictHenselizationStructuralMap s)).obj F).obj ≫
    (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
      (Scheme.strictHenselizationStructuralMap s) t).hom.app F

end AlgebraicGeometry.Etale
