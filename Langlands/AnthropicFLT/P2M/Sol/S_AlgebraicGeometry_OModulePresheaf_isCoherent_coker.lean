/-
Ported from `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_isCoherent_coker.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_coker

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Spec Scheme OModulePresheaf.coker OModulePresheaf.imCokerSES OModulePresheaf.Hom OModulePresheaf OModulePresheaf.IsCoherent)
namespace OModulePresheaf
export _root_.AlgebraicGeometry.OModulePresheaf (coker imCokerSES Hom IsCoherent)
namespace G4T
open _root_.AlgebraicGeometry.OModulePresheaf _root_.AlgebraicGeometry

universe u

section PModAlg
variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G)

theorem isCoherent_coker (hG : OModulePresheaf.IsCoherent G) :
    OModulePresheaf.IsCoherent (OModulePresheaf.coker φ) := fun U => by
  haveI := hG U
  exact Module.Finite.of_surjective ((OModulePresheaf.imCokerSES φ).proj.appSections U.1)
    ((OModulePresheaf.imCokerSES φ).surjective U.1)

end PModAlg

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_coker.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G) (hG : G.IsCoherent) : (OModulePresheaf.coker φ).IsCoherent :=
  AlgebraicGeometry.OModulePresheaf.G4T.isCoherent_coker φ hG
