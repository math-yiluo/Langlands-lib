/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Pulling back module sheaves from an algebraically closed point

Source: Stacks Project, Tags 03P5, 0A3H and 03Q1.
(blueprint: lem-sbc-geometric-point-module-constant)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- The inverse image of a module sheaf from an algebraically closed geometric point is
constant, with a module as its value.

Source: Stacks Project, Tags 03P5, 0A3H and 03Q1.
(blueprint: lem-sbc-geometric-point-module-constant)

Proof: apply the existing constancy theorem to the underlying set sheaf. The constant
sheaf comparison for forgetting coefficients identifies its counit with the image of
the module-valued counit. Forgetting modules reflects isomorphisms, so this latter
counit is invertible as well. Take its value to be the module of global sections.
Inverse image preserves constant sheaves by the constant-sheaf pullback isomorphism. -/
theorem exists_constant_module_upperStar_geometricPoint
    (Λ : Type (u + 1)) [CommRing Λ] {K : Type u} [Field K] [IsAlgClosed K]
    {Y : Scheme.{u}} (e : Y ⟶ Spec (.of K))
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ M : ModuleCat.{u + 1} Λ,
      Nonempty ((upperStar (ModuleCat.{u + 1} Λ) e).obj F ≅
        (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  let J := (Spec (.of K)).smallEtaleTopology
  let U := CategoryTheory.forget (ModuleCat.{u + 1} Λ)
  let G := (sheafCompose J U).obj F
  have hG : IsIso ((constantSheafAdj J (Type (u + 1)) terminalIsTerminal).counit.app G) :=
    (Scheme.spec_algClosed_etale_sheaf_constant K G).1
  have hF : IsIso ((constantSheafAdj J (ModuleCat.{u + 1} Λ)
      terminalIsTerminal).counit.app F) := by
    have hm : IsIso ((sheafCompose J U).map
        ((constantSheafAdj J (ModuleCat.{u + 1} Λ) terminalIsTerminal).counit.app F)) := by
      rw [← constantSheafAdj_counit_w J U F terminalIsTerminal]
      infer_instance
    exact isIso_of_reflects_iso _ (sheafCompose J U)
  let M := F.obj.obj ⟨⊤_ (Spec (.of K)).Etale⟩
  let i := (asIso ((constantSheafAdj J (ModuleCat.{u + 1} Λ)
    terminalIsTerminal).counit.app F)).symm
  exact ⟨M, ⟨(upperStar (ModuleCat.{u + 1} Λ) e).mapIso i ≪≫
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) e).app M⟩⟩

end AlgebraicGeometry.Etale
