/-
Ported from `P2M/Sol/S_ProjSpaceCech_GradedModule_Hom_HMap_bijective_of_saturated.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_Hom_cochainMap_bijective_of_saturated
import Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_HMap_bijective_of_cochainMap_bijective
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_ProjSpaceCech_GradedModule_Hom_HMap_bijective_of_saturated

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
export _root_.ProjSpaceCech (GradedModule GradedModule.Hom GradedModule.Hom.HMap GradedModule.Hom.cochainMap_bijective_of_saturated GradedModule.HMap_bijective_of_cochainMap_bijective)
open _root_.ProjSpaceCech

section HMapSat

variable {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : GradedModule R n}

namespace GradedModule export _root_.ProjSpaceCech.GradedModule (Hom Hom.HMap xMul grade Hom.cochainMap_bijective_of_saturated HMap_bijective_of_cochainMap_bijective) namespace Hom export _root_.ProjSpaceCech.GradedModule.Hom (HMap toLinearMap cochainMap_bijective_of_saturated) end GradedModule.Hom
open scoped _root_.ProjSpaceCech.GradedModule _root_.ProjSpaceCech.GradedModule.Hom in

theorem GradedModule.Hom.HMap_bijective_of_saturated' (φ : GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap)
    (hsat : ∀ (j : Fin (n + 1)) (e : ℤ), ∀ m ∈ D₂.grade e,
      ∃ k : ℕ, ∃ m' ∈ D₁.grade (e + k), φ.toLinearMap m' = (D₂.xMul j ^ k) m) (i : ℕ) :
    Function.Bijective (GradedModule.Hom.HMap φ i) :=
  GradedModule.HMap_bijective_of_cochainMap_bijective φ
    (GradedModule.Hom.cochainMap_bijective_of_saturated φ hinj hsat) i

end HMapSat

end ProjSpaceCech

theorem solution {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule R n} (φ : ProjSpaceCech.GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap)
    (hsat : ∀ (j : Fin (n + 1)) (e : ℤ), ∀ m ∈ D₂.grade e,
      ∃ k : ℕ, ∃ m' ∈ D₁.grade (e + k), φ.toLinearMap m' = (D₂.xMul j ^ k) m) (i : ℕ) :
    Function.Bijective (ProjSpaceCech.GradedModule.Hom.HMap φ i) :=
  ProjSpaceCech.GradedModule.Hom.HMap_bijective_of_saturated' φ hinj hsat i

end
