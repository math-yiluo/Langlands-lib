/-
Ported from `P2M/Sol/S_ProjSpaceCech_GradedModule_Hom_secMap_injective.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped and its commands are replaced
by standard Lean commands. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_ProjSpaceCech_GradedModule_Hom_secMap_injective

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

universe u

noncomputable section

open Finset Function MvPolynomial

namespace ProjSpaceCech
export _root_.ProjSpaceCech (GradedModule GradedModule.Frac GradedModule.sec GradedModule.sec.mk GradedModule.sec_mk_eq GradedModule.Hom GradedModule.Hom.map_monMul GradedModule.Hom.secMap)
open _root_.ProjSpaceCech

section SecMapInj

variable {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : GradedModule R n}

namespace GradedModule export _root_.ProjSpaceCech.GradedModule (Frac sec sec.mk sec_mk_eq Hom Hom.map_monMul Hom.secMap mk) namespace Hom export _root_.ProjSpaceCech.GradedModule.Hom (map_monMul secMap mem_grade mk toLinearMap) end GradedModule.Hom
open scoped _root_.ProjSpaceCech.GradedModule _root_.ProjSpaceCech.GradedModule.Hom in
theorem GradedModule.Hom.secMap_mk (φ : GradedModule.Hom D₁ D₂) (I : Finset (Fin (n + 1)))
    (x : GradedModule.Frac D₁ I) :
    GradedModule.Hom.secMap φ I (GradedModule.sec.mk D₁ I x)
      = GradedModule.sec.mk D₂ I ⟨x.denExp, x.hden, φ.toLinearMap x.num, φ.mem_grade _ _ x.hnum⟩ := rfl

open scoped _root_.ProjSpaceCech.GradedModule _root_.ProjSpaceCech.GradedModule.Hom in

theorem GradedModule.Hom.secMap_injective' (φ : GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap) (I : Finset (Fin (n + 1))) :
    Function.Injective (GradedModule.Hom.secMap φ I) := by
  intro p q h
  obtain ⟨x, rfl⟩ := Quotient.exists_rep p
  obtain ⟨y, rfl⟩ := Quotient.exists_rep q
  change GradedModule.sec.mk D₁ I x = GradedModule.sec.mk D₁ I y
  change GradedModule.Hom.secMap φ I (GradedModule.sec.mk D₁ I x)
    = GradedModule.Hom.secMap φ I (GradedModule.sec.mk D₁ I y) at h
  rw [GradedModule.Hom.secMap_mk, GradedModule.Hom.secMap_mk, GradedModule.sec_mk_eq] at h
  obtain ⟨c, hc, heq⟩ := h
  refine (GradedModule.sec_mk_eq D₁ I).mpr ⟨c, hc, hinj ?_⟩
  rw [GradedModule.Hom.map_monMul, GradedModule.Hom.map_monMul]
  exact heq

end SecMapInj

end ProjSpaceCech

theorem solution {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule R n} (φ : ProjSpaceCech.GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap) (I : Finset (Fin (n + 1))) :
    Function.Injective (ProjSpaceCech.GradedModule.Hom.secMap φ I) :=
  ProjSpaceCech.GradedModule.Hom.secMap_injective' φ hinj I

end
