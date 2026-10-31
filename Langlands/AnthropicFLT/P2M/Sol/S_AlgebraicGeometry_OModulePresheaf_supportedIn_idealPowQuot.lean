/-
Ported from `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_supportedIn_idealPowQuot.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_supportedIn_idealPowQuot

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Spec Scheme OModulePresheaf.idealPowQuot OModulePresheaf OModulePresheaf.SupportedIn)
namespace OModulePresheaf
export _root_.AlgebraicGeometry.OModulePresheaf (idealPow idealPowSuccSub idealPowQuot SupportedIn obj)
namespace G4T
open _root_.AlgebraicGeometry.OModulePresheaf _root_.AlgebraicGeometry

universe u

section Closure

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

theorem supportedIn_idealPowQuot (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ)
    {Y : Closeds V} (hFs : OModulePresheaf.SupportedIn F Y) :
    OModulePresheaf.SupportedIn (idealPowQuot π I F k) Y := fun U hU => by
  haveI := hFs U hU
  haveI : Subsingleton ((idealPow π I F k).obj U.1) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  exact ⟨fun a b => by
    obtain ⟨a', rfl⟩ := (idealPowSuccSub π I F k U.1).mkQ_surjective a
    obtain ⟨b', rfl⟩ := (idealPowSuccSub π I F k U.1).mkQ_surjective b
    exact congrArg _ (Subsingleton.elim a' b')⟩

end Closure

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_supportedIn_idealPowQuot.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) {Y : TopologicalSpace.Closeds V} (hFs : F.SupportedIn Y) : (OModulePresheaf.idealPowQuot π I F k).SupportedIn Y :=
  AlgebraicGeometry.OModulePresheaf.G4T.supportedIn_idealPowQuot π I F k hFs
